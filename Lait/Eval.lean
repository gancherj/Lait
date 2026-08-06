import Lait.Syntax
import Lait.Utils
import Std.Data.TreeMap
import Lean

deriving instance BEq for Const

-- Values are evaluated against an *environment* (`List Val`, innermost binding
-- at the head = de Bruijn index 0) rather than by substitution.  Functions are
-- represented as closures capturing that environment; `fix` is a `VRec` that is
-- unfolded one step on demand (see `Val.whnf`).  Types are erased at runtime, so
-- a closure body's type-variable count `t` is irrelevant and left existential.
inductive Val where
  | VConst : Const -> Val
  | VLoc : Nat -> Val
  | VClosure : List Val -> {t m : Nat} -> Exp t (m + 1) -> Val
  | VRec : List Val -> {t m : Nat} -> Exp t (m + 1) -> Val
  | VPair : Val -> Val -> Val
  | VConstructor : String -> List Val -> Val
  | VRecord : List (String × Val) -> Val

instance : Inhabited Val := ⟨.VConst .Unit⟩

def Const.pretty (c : Const) : _root_.String :=
  match c with
  | .Num n => toString n
  | .Bool b => if b then "true" else "false"
  | .String s => s!"\"{s}\""
  | .Unit => "()"

partial def Val.pretty (v : Val) : _root_.String :=
  match v with
  | .VConst c => c.pretty
  | .VLoc _ => "<location>"
  | .VClosure .. => "<function>"
  | .VRec .. => "<function>"
  | .VPair v1 v2 => "(" ++ v1.pretty ++ ", " ++ v2.pretty ++ ")"
  | .VConstructor x vs => x ++ "(" ++ _root_.String.intercalate ", " (vs.map pretty) ++ ")"
  | .VRecord xs => "{" ++ _root_.String.intercalate ", " (xs.map fun (x, v) => x ++ ": " ++ v.pretty) ++ "}"

partial def Val.eq (stx : Lean.Syntax) (v1 v2 : Val) : Except (String × Lean.Syntax) Bool :=
  match v1, v2 with
  | .VConst c1, .VConst c2 => pure (c1 == c2)
  | .VLoc i1, .VLoc i2 => pure (i1 == i2)
  | .VClosure .., .VClosure .. => throw (s!"Eq: functions", stx)
  | .VRec .., .VRec .. => throw (s!"Eq: functions", stx)
  | .VPair v1 v2, .VPair v1' v2' => do
    let b1 <- v1.eq stx v1'
    let b2 <- v2.eq stx v2'
    pure (b1 && b2)
  | .VConstructor x1 vs1, .VConstructor x2 vs2 =>
     if x1 != x2 then
       pure false
     else if vs1.length != vs2.length then
       pure false
     else do
      (vs1.zip vs2).allM fun (v1, v2) => v1.eq stx v2
  | _, _ => pure false


def Heap := Nat × Std.TreeMap Nat Val


def Heap.alloc (h : Heap) (v : Val) : Heap × Nat :=
  let (i, m) := h
  ((i + 1, m.insert i v), i)

def Heap.assign (h : Heap) (loc : Nat) (v : Val) : Heap :=
  let (i, m) := h
  (i, m.insert loc v)

def Heap.get (h : Heap) (loc : Nat) : Except String Val :=
  let (_, m) := h
  match m.get? loc with
  | some v => pure v
  | none => throw s!"Location {loc} not found in heap"

def Heap.new : Heap :=
  (0, Std.TreeMap.empty)

structure EvalState where
  heap : Heap
  opMap : Std.TreeMap String (Lean.Syntax -> List Val -> Except (String × Lean.Syntax) Val)
  timeout : UInt32 := 3000
  /-- Interpreter steps per top-level evaluation (`Exp.eval`, `Val.whnf`, `Val.apply`). -/
  maxSteps : Nat := 8000
  stepsRemaining : Nat := 8000
  logs : List (String) := []

def initOpMap : Std.TreeMap String (Lean.Syntax -> List Val -> Except (String × Lean.Syntax) Val) :=
  Std.TreeMap.ofList [
    ("+", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Num (n1 + n2)))
      | _ => Except.error (s!"Wrong inputs to addition", stx)
    ),
    ("-", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Num (n1 - n2)))
      | _ => throw (s!"Wrong inputs to subtraction", stx)
    ),
    ("*", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Num (n1 * n2)))
      | _ => throw (s!"Wrong inputs to multiplication", stx)
    ),
    ("++", fun stx vs => do
      match vs with
      | [Val.VConst (Const.String s1), .VConst (Const.String s2)] => pure (Val.VConst (Const.String (s1 ++ s2)))
      | _ => throw (s!"Wrong inputs to ++", stx)
    ),
    ("not", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Bool b)] => pure (Val.VConst (Const.Bool (not b)))
      | _ => throw (s!"Wrong inputs to not", stx)
    ),
    ("&&", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Bool b1), .VConst (Const.Bool b2)] => pure (Val.VConst (Const.Bool (b1 && b2)))
      | _ => throw (s!"Wrong inputs to &&", stx)
    ),
    ("||", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Bool b1), .VConst (Const.Bool b2)] => pure (Val.VConst (Const.Bool (b1 || b2)))
      | _ => throw (s!"Wrong inputs to ||", stx)
    ),
    ("<", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Bool (n1 < n2)))
      | _ => throw (s!"Wrong inputs to <", stx)
    ),
    (">", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Bool (n1 > n2)))
      | _ => throw (s!"Wrong inputs to >", stx)
    ),
    ("<=", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Bool (n1 ≤ n2)))
      | _ => throw (s!"Wrong inputs to <=", stx)
    ),
    (">=", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n1), .VConst (Const.Num n2)] => pure (Val.VConst (Const.Bool (n1 ≥ n2)))
      | _ => throw (s!"Wrong inputs to >=", stx)
    ),
    ("num2string", fun stx vs => do
      match vs with
      | [Val.VConst (Const.Num n)] => pure (Val.VConst (Const.String (toString n)))
      | _ => throw (s!"Wrong inputs to num2string", stx)
    ),
    ("==", fun (stx : Lean.Syntax) (vs : List Val) => do
      match vs with
      | [v1, v2] => do
          let b <- v1.eq stx v2
          pure (Val.VConst (Const.Bool b))
      | _ => throw (s!"Wrong inputs to ==", stx)
    ),
  ]

def EvalState.new : EvalState :=
  { heap := Heap.new, opMap := initOpMap }

def EvalState.resetSteps (st : EvalState) : EvalState :=
  { st with stepsRemaining := st.maxSteps, logs := [] }

open Lean Elab Command
abbrev ExpEval := StateT EvalState (ExceptT (String × Lean.Syntax) IO)
abbrev DeclEval := StateT EvalState (ExceptT (String × Lean.Syntax) TermElabM)

def throwExp (stx : Lean.Syntax) (e : String) : ExpEval α :=
  fun _ => (pure (Except.error (e, stx)) : IO (Except (String × Lean.Syntax) (α × EvalState)))
def throwDecl (stx : Lean.Syntax) (e : String) : DeclEval α :=
  fun _ => (pure (Except.error (e, stx)) : TermElabM (Except (String × Lean.Syntax) (α × EvalState)))

def ExpEval.scopeError (e : ExpEval α) : ExpEval (Except (String × Lean.Syntax) α) := do
  let st ← get
  let res : Except (String × Lean.Syntax) (α × EvalState) ← (e.run st).run
  match res with
  | .ok (a, st') => do set st'; pure (.ok a)
  | .error err => pure (.error err)

def withTimeout (ms : UInt32) (action : IO α) : IO (Option α) := do
  let actionTask ← IO.asTask action Task.Priority.dedicated
  let timeoutTask ← IO.asTask (do IO.sleep ms) Task.Priority.dedicated
  let finished ← IO.waitAny [
    actionTask.map (fun r => (0, r.toOption)),
    timeoutTask.map (fun _ => (1, none))
  ]
  match finished with
  | (0, some a) => do
     actionTask.asServerTask.cancel
     timeoutTask.asServerTask.cancel
     return some a
  | _           => return none

def printLogs  (stx : Lean.Syntax) (logs : List String) : DeclEval Unit := do
  logs.forM fun log => do
    Lean.logInfoAt stx log

def DeclEval.liftExpEval (stx : Lean.Syntax) (e : ExpEval α) : DeclEval (Except (String × Lean.Syntax) α) := do
  modify EvalState.resetSteps
  let st ← get
  let res : Option (Except (String × Lean.Syntax) (α × EvalState)) ← withTimeout st.timeout (e.run st).run
  match res with
  | none => pure (.error ("Timeout", .missing))
  | some (.ok (a, st')) => do
     printLogs stx st'.logs
     set { st' with logs := [] }
     pure (.ok a)
  | some (.error err) => throwDecl err.2 err.1

def DeclEval.scopeExpError (stx : Lean.Syntax) (e : ExpEval α) : DeclEval (Except String α) := do
  modify EvalState.resetSteps
  let st ← get
  let res : Option (Except (String × Lean.Syntax) (α × EvalState)) ← withTimeout st.timeout (e.run st).run
  match res with
  | none => pure (.error "Timeout")
  | some (.ok (a, st')) => do printLogs stx st'.logs; set { st' with logs := [] }; pure (.ok a)
  | some (.error err) => pure (.error err.1)

partial def evalOp (stx : Lean.Syntax) (s : String) (vs : List Val) : ExpEval Val := do
  match (← get).opMap.get? s with
  | some f => f stx vs
  | none => throwExp stx s!"Unknown binary operator: {s}"

def ExpEval.log (log : String) : ExpEval Unit := do
  modify fun st => { st with logs := log :: st.logs }

def ExpEval.consumeStep (stx : Lean.Syntax) : ExpEval Unit := do
  let st ← get
  if st.stepsRemaining = 0 then
    throwExp stx s!"Step limit exceeded ({st.maxSteps} steps): evaluation did not terminate"
  set { st with stepsRemaining := st.stepsRemaining - 1 }

mutual

-- Reduce to weak head normal form by unfolding a recursive binding (`VRec`):
-- evaluate its body with the recursion itself bound at de Bruijn index 0.  The
-- body is always a value-producing form (a `fun`, or a tuple of them for mutual
-- groups), so this terminates immediately for well-formed `fix`.  Every other
-- value is already a head normal form.
partial def Val.whnf (v : Val) : ExpEval Val := do
  ExpEval.consumeStep .missing
  match v with
  | .VRec renv body => do Val.whnf (← Exp.eval (v :: renv) body)
  | _ => pure v

partial def Val.apply (v1 v2 : Val) : ExpEval Val := do
  ExpEval.consumeStep .missing
  match ← Val.whnf v1 with
  | .VClosure cenv body => Exp.eval (v2 :: cenv) body
  | v => throwExp .missing s!"Application of non-function: got {v.pretty}"

-- `env` holds the values of in-scope variables, innermost (de Bruijn index 0)
-- first.  Evaluation looks variables up here instead of substituting them, so
-- cost is independent of how many bindings are in scope.



partial def Exp.eval (env : List Val) (e : Exp t m) : ExpEval Val := do
  let ⟨stx, _⟩ := e
  ExpEval.consumeStep stx
  match e with
  | .mk _ (.Const c) => pure (.VConst c)
  | .mk _ (.Lam _ _ body) => pure (.VClosure env body)
  | .mk _ (.Rec _ body) => pure (.VRec env body)
  | .mk _ (.Var i) => pure env[i.val]!
  | .mk _ (.Loc i) => pure (.VLoc i)
  | .mk _ (.App e1 e2) => do
    let v1 ← Exp.eval env e1
    let v2 ← Exp.eval env e2
    Val.apply v1 v2
  | .mk _ (.Let _ _ e1 e2) => do
    let v1 ← Exp.eval env e1
    Exp.eval (v1 :: env) e2
  | .mk stx (.If e1 e2 e3) => do
    match ← Val.whnf (← Exp.eval env e1) with
    | .VConst (Const.Bool b) => if b then Exp.eval env e2 else Exp.eval env e3
    | _ => throwExp stx "Condition of if must be a boolean"
  | .mk _ (.Pair e1 e2) => do
    pure (.VPair (← Exp.eval env e1) (← Exp.eval env e2))
  | .mk stx (.Error e) => do
    throwExp stx (← Exp.eval env e).pretty
  | .mk _ (.Print e) => do
    let v ← Exp.eval env e
    ExpEval.log (s!"{v.pretty}")
    pure (.VConst .Unit)
  | .mk _ (.Try e1 e2) => do
    match ← ExpEval.scopeError (Exp.eval env e1) with
    | .ok v => pure v
    | .error _ => Exp.eval env e2
  | .mk _ (.Alloc e) => do
    let v ← Exp.eval env e
    let st ← get
    let (h', i) := st.heap.alloc v
    set { st with heap := h' }
    pure $ .VLoc i
  | .mk stx (.Deref e) => do
    match ← Val.whnf (← Exp.eval env e) with
    | .VLoc i =>
      match (← get).heap.get i with
      | .ok v => pure v
      | .error e => throwExp stx e
    | _ => throwExp stx "Dereference of non-location"
  | .mk stx (.Assign e1 e2) => do
    let v1 ← Val.whnf (← Exp.eval env e1)
    let v2 ← Exp.eval env e2
    match v1 with
    | .VLoc i => do
      modify fun st => { st with heap := st.heap.assign i v2 }
      pure $ .VConst $ .Unit
    | _ => throwExp stx "Assignment of non-location"
  | .mk stx (.Op s es) => do
    let vs ← es.toList.mapM (Exp.eval env)
    evalOp stx s vs
  | .mk stx (.Fst e) => do
    match ← Val.whnf (← Exp.eval env e) with
    | .VPair v1 _ => pure v1
    | _ => throwExp stx "First of non-pair"
  | .mk stx (.Snd e) => do
    match ← Val.whnf (← Exp.eval env e) with
    | .VPair _ v2 => pure v2
    | _ => throwExp stx "Second of non-pair"
  | .mk stx (.Match e cases) => do
    match ← Val.whnf (← Exp.eval env e) with
    | .VConstructor x vs =>
      match cases.toList.find? (fun ⟨c, _, _⟩ => x = c) with
      | some ⟨_, xs, k⟩ =>
         if xs.length = vs.length then Exp.eval (vs ++ env) k
         else throwExp stx "Wrong number of arguments to constructor"
      | none =>
         match cases.wild? with
         | some k => Exp.eval env k
         | none => throwExp stx "Could not find case for match"
    | _ => throwExp stx "Match of non-constructor"
  | .mk _ (.MkRecord es) => do
      let vs ← es.toList.mapM (fun (s, x) => do pure (s, ← Exp.eval env x))
      pure (.VRecord vs)
  | .mk stx (.RecordGet e x) => do
    match ← Val.whnf (← Exp.eval env e) with
    | .VRecord xs => match xs.find? (fun (s, _) => s = x) with
      | some (_, v) => pure v
      | none => throwExp stx s!"Field {x} not found in record"
    | _ => throwExp stx "Record get of non-record"

end

def addConstructor (cname : String) : DeclEval Unit := do
  modify fun st => { st with opMap := st.opMap.insert cname (fun _ vs =>
                        pure (Val.VConstructor cname vs)) }


-- `env` holds the values of in-scope (prior) declarations, innermost (de Bruijn
-- index 0) first.  Definitions are added to the environment by reference rather
-- than substituted into later bodies.
def Decl.eval (d : Decl n m) (env : List Val) : DeclEval (List Val) :=
  match d with
  | .mk _ .DeclNil => pure env
  | .mk _ (.DeclConcat d1 d2)  => do
    let env' ← d1.eval env
    d2.eval env'
  | .mk dstx (.DeclDef _ _ _ e) => do
    let v ← DeclEval.liftExpEval dstx (Exp.eval env e)
    match v with
    | .ok v => pure (v :: env)
    | .error e => do
      Lean.logErrorAt e.2 e.1
      pure env
  | .mk _ (.DeclTypeAlias _ _) => pure env
  | .mk _ (.DeclCheck _) => pure env
  | .mk stx (.DeclEval e) => do
    match ← DeclEval.scopeExpError stx (Exp.eval env e) with
    | .ok v => do
      Lean.logInfoAt stx s!"{v.pretty}"
      pure env
    | .error e => do
      Lean.logErrorAt stx e
      pure env
  | .mk stx (.DeclTest e1 e2) => do
    let v12 ← DeclEval.scopeExpError stx do
       let v1 ← Exp.eval env e1
       let v2 ← Exp.eval env e2
       pure (v1, v2)
    match v12 with
    | .ok (v1, v2) => do
      let b ← v1.eq stx v2
      if not b then Lean.logErrorAt stx s!"Test failed: got {v1.pretty} but expected {v2.pretty}"
      pure env
    | .error e => do
      Lean.logErrorAt stx e
      pure env
  | .mk stx (.DeclTestError e msg) => do
    match ← DeclEval.scopeExpError stx (Exp.eval env e) with
    | .ok v => do
      Lean.logErrorAt stx s!"Test failed: expected an error containing \"{msg}\" but evaluation succeeded with {v.pretty}"
      pure env
    | .error err => do
      if msg.isEmpty || (err.splitOn msg).length > 1 then
        pure ()
      else
        Lean.logErrorAt stx s!"Test failed: expected an error containing \"{msg}\" but got error \"{err}\""
      pure env
  | .mk _ (.DeclInductive _ _ cs) => do
    let _ ← cs.mapM fun (cname, _) => addConstructor cname
    pure env

def Decl.run (d : Decl 0 m) : TermElabM Unit := do
  match <- d.eval [] EvalState.new with
  | .ok _ => pure ()
  | .error e => throwErrorAt e.2 e.1

-- Evaluate `d` starting from an existing runtime environment `env` and state
-- `st` (rather than empty), returning the extended environment and state.  Used
-- to thread evaluation state across separately-elaborated top-level commands.
def Decl.runFrom (d : Decl n m) (env : List Val) (st : EvalState) :
    TermElabM (List Val × EvalState) := do
  match <- (d.eval env) st with
  | .ok res => pure res
  | .error e => throwErrorAt e.2 e.1
