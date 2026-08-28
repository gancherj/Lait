import Lait.Syntax
import Lait.Utils
import Lean

open Lean Elab Command

-- An operator/constructor signature.  The variables in `tyVars` are FVars
-- appearing in `argTys`/`outTy`; each instantiation refreshes them to fresh
-- FVars (analogous to plzoo's `refresh`).
structure OpSig where
  tyVars : List Lean.Name
  argTys : List (Ty 0)
  outTy : Ty 0

inductive TyVal where
  -- Nat is the arity; the list holds this type's constructor names (in
  -- declaration order), used for `match` exhaustiveness checking.
  | Inductive : Nat -> List String -> TyVal
  | Alias : TyScheme -> TyVal
  -- A primitive type (`Int`, `Bool`, ...).  Carries nothing: these have their own
  -- `TyX` constructors, so the entry exists only to reserve the name.
  | Builtin : TyVal

structure TcEnv (n : Nat) where
  opMap : Std.TreeMap String OpSig
  tyMap : Std.TreeMap String TyVal
  curSyntax : Lean.Syntax
  -- In-scope variable schemes, innermost (de Bruijn index 0) first.  Stored as a
  -- length-indexed vector rather than a `Fin n → TyScheme` function: building the
  -- latter via nested `Fin.cases` closures in `withVar` makes deep lookups
  -- exponential because sharing is lost as the chain is threaded through the monad.
  varMap : Vec n TyScheme
  -- Where "go to definition" should jump for each in-scope variable, in the same order as
  -- `varMap`.  `none` for a binding with no usable source position, e.g. one introduced by
  -- a declaration that a surface pass synthesized.
  varLocs : Vec n (Option DeclarationLocation)
  -- Source locations of the top-level names spliced into this module by `#include`.  Their
  -- syntax carries no positions of its own (it belongs to another file, see the `#include`
  -- case of `elabLaitDecl`), so `#include` records where each name was defined instead.
  defLocs : Std.TreeMap String DeclarationLocation
  -- Running union of `Ty.fvars` over every in-scope binding's scheme, maintained
  -- incrementally by `withVar` so that `envFVars` is O(1).
  frozen : Lean.NameSet
  -- The names bound by top-level `def`s so far (including the defs generated for
  -- inductive constructors).  A top-level definition may not shadow an existing
  -- one, so `withDefName` rejects a repeat; `let`/`fun`/`match` binders go
  -- through `withVar` and may still shadow freely.
  defNames : Std.TreeSet String
  -- The de Bruijn *levels* (not indices, which shift as bindings are pushed) of
  -- the in-scope variables that stand for data constructors -- i.e. the `def`s
  -- `mkConstrFns` generates.  Applying one of those is non-expansive, so the value
  -- restriction needs to tell them apart from ordinary functions; see `Exp.isValue`.
  ctorLevels : Std.TreeSet Nat

-- Does `s` name a data constructor of an inductive type, as opposed to one of the
-- primitive operators (`+`, `==`, ...) that also live in `opMap`?
def TcEnv.isCtorName (env : TcEnv n) (s : String) : Bool :=
  match env.opMap.get? s with
  | some { outTy := .mk _ (.TApp tname _), .. } =>
    match env.tyMap.get? tname with
    | some (.Inductive ..) => true
    | _ => false
  | _ => false

-- Is the variable at de Bruijn index `i` a constructor function?  Index `i` in a
-- context of `n` bindings is level `n - 1 - i`.
def TcEnv.isCtorVar (env : TcEnv n) (i : Fin n) : Bool :=
  env.ctorLevels.contains (n - 1 - i.val)

abbrev Constraint := Lean.Syntax × TyX 0 × TyX 0

structure TcState where
  constraints : List Constraint := []
  freshCounter : Nat := 0
  -- Hovers to attach once the constraints are solved: the syntax of an expression, its
  -- type, and -- for a variable occurrence -- the location of the binding it resolves to.
  stxMap: List (Lean.Syntax × Ty 0 × Option DeclarationLocation) := []

abbrev Check n := ReaderT (TcEnv n) (StateT TcState TermElabM)

instance : MonadExcept String (Check n) where
  throw s := throwError s
  tryCatch _ _ := throwError "Unhandled exception"

def Check.runMetaM (m : MetaM α) : Check n α := do
  m


-- ---- Well-formedness ----

def List.hasDup [BEq α] (xs : List α) : Bool :=
  match xs with
  | [] => false
  | x :: xs => if xs.contains x then true else xs.hasDup

def TyScheme.hasDupFVars (t : TyScheme) : Bool :=
  t.tyVars.hasDup

mutual
partial def normalizeTy : Ty k -> Check n (Ty k)
  | .mk stx t => do pure $ .mk stx (← normalizeTyX stx t)

partial def normalizeTyX (stx : Lean.Syntax) (t : TyX k) : Check n (TyX k) :=
   match t with
    | .Int | .Unit | .Str | .Bool | .Var _ | .FVar _ => pure t
    | .Arrow t1 t2  => do let t1' ← normalizeTy t1; let t2' ← normalizeTy t2; pure (.Arrow t1' t2')
    | .Prod t1 t2 => do let t1' ← normalizeTy t1; let t2' ← normalizeTy t2; pure (.Prod t1' t2')
    | .Ref t => do let t' ← normalizeTy t; pure (.Ref t')
    | .Record xs => do
       let xs' <- xs.mapM (fun (x, y) => do
        let y' ← normalizeTy y
        pure (x, y'))
       if (xs'.map Prod.fst).hasDup then throwErrorAt stx s!"Duplicate field name in record"
       let xs' := xs'.mergeSort (fun x y => x.1 <= y.1)
       pure (.Record xs')
    | .TApp s ts => do
        let ts <- ts.mapM normalizeTy
        match (← read).tyMap.get? s with
        | some (.Alias { tyVars := tyVars, ty := ty }) => do
          if h : ts.length = tyVars.length then do
            let ty := ty.subst (h ▸ (ts.get))
            normalizeTyX stx ty.get
          else throwErrorAt stx s!"Wrong number of arguments to {s}"
        | some (.Inductive arity _) => do
          if arity == ts.length then pure (.TApp s ts)
          else throwErrorAt stx s!"Wrong number of arguments to {s}"
        | some .Builtin => throwErrorAt stx s!"{s} is a built-in type and takes no arguments"
        | none => throwErrorAt stx s!"Unknown type constructor: {s}"
end

-- ---- Free variables ----
mutual
partial def Ty.fvars : Ty n → Lean.NameSet
  | .mk _ t => TyX.fvars t

partial def TyX.fvars : TyX n → Lean.NameSet
  | .FVar n => Lean.NameSet.empty.insert n
  | .Record xs => xs.foldl (fun s x => s.union (Ty.fvars x.2)) {}
  | .Arrow t1 t2 | .Prod t1 t2 => (Ty.fvars t1).union (Ty.fvars t2)
  | .Ref t => Ty.fvars t
  | .TApp _ ts => ts.foldl (fun s t => s.union (Ty.fvars t)) {}
  | .Var _ | .Int | .Bool | .Str | .Unit => {}
end

def withVar (ty : TyScheme) (loc? : Option DeclarationLocation)
    (k : Check (n + 1) α) (isCtor : Bool := false) : Check n α := fun env =>
  k {
    opMap := env.opMap,
    tyMap := env.tyMap,
    curSyntax := env.curSyntax,
    frozen := env.frozen.union (Ty.fvars ty.ty),
    varMap := env.varMap.cons ty,
    varLocs := env.varLocs.cons loc?,
    defLocs := env.defLocs,
    defNames := env.defNames,
    -- The binding being pushed sits at index 0, i.e. at level `n`.
    ctorLevels := if isCtor then env.ctorLevels.insert n else env.ctorLevels
  }

/-- The "go to definition" target of a binding introduced by `stx`.  `stx` belongs to the
file being elaborated (declarations from other modules have no positions), so its own start
is the target. -/
def Check.locOf (stx : Lean.Syntax) : Check n (Option DeclarationLocation) := do
  mkStartLocation? (← getMainModule) stx

-- Top-level names are unique, so re-defining one is an error rather than
-- shadowing.  Checked before the body is inferred, so that a duplicate is
-- reported instead of whatever errors the (now unreachable) body may contain.
-- `_` is a wildcard, not a name, so it never clashes.
def checkDefNameFresh (stx : Lean.Syntax) (name : String) : Check n Unit := do
  if name != "_" && (← read).defNames.contains name then
    throwErrorAt stx s!"{name} is already defined"

-- Bind a top-level `def`.
def withDefName (stx : Lean.Syntax) (name : String) (ty : TyScheme)
    (k : Check (n + 1) α) : Check n α := do
  checkDefNameFresh stx name
  -- A name spliced in from another module is declared by position-less syntax; `#include`
  -- recorded where it was defined, so prefer that over `stx`.
  let loc? ← match (← read).defLocs.get? name with
    | some loc => pure (some loc)
    | none => Check.locOf stx
  -- A constructor's `def` is generated by `mkConstrFns` after the `type` that
  -- declares it, so `opMap` already knows the name by the time we bind it.
  let isCtor := (← read).isCtorName name
  withReader (fun env => { env with defNames := env.defNames.insert name })
    (withVar ty loc? k (isCtor := isCtor))

-- Type names are unique too: a `type` declaration may not re-declare a type
-- introduced by an earlier declaration, nor a primitive one -- `initTyMap` seeds
-- `tyMap` with those (`lait_ty` also lexes them as keywords, so in practice the
-- parser rejects them before we get here).
def checkTyNameFresh (stx : Lean.Syntax) (tname : String) : Check n Unit := do
  if (← read).tyMap.contains tname then
    throwErrorAt stx s!"Type {tname} is already defined"

def TyScheme.mono (t : Ty 0) : TyScheme := { tyVars := [], ty := t }

def freshTyName : Check n Lean.Name := do
  let s ← get
  let i := s.freshCounter
  set { s with freshCounter := i + 1 }
  pure (Lean.Name.mkNum `_tcFresh i)

def freshTy (stx : Lean.Syntax := .missing) : Check n (Ty 0) := do
  let nm ← freshTyName
  pure (.mk stx (.FVar nm))

def addConstraint (stx : Lean.Syntax) (t1 t2 : Ty 0) : Check n Unit :=
  modify fun s => { s with constraints := (stx, t1.get, t2.get) :: s.constraints }

-- Build (Fin k → Ty 0) of fresh FVars, plus the list of names used (in
-- the order: position i ↔ names.get i).
def freshSubst : (k : Nat) → Check n ((Fin k → Ty 0) × List Lean.Name)
  | 0 => pure ((fun i => nomatch i), [])
  | k+1 => do
    let nm ← freshTyName
    let (σ, ns) ← freshSubst k
    pure (Fin.cases (.mk .missing (.FVar nm)) σ, nm :: ns)

-- Like `freshSubst`, but opens each declared type variable with an FVar that
-- keeps the user-written name (e.g. `k`, `v`).  Used when checking a `def` with
-- an explicit polymorphic signature so that hovers inside the body show the
-- source names rather than internal `_tcFresh` ones.  Within a single `def` the
-- declared variables are distinct, and they are generalized away before the next
-- declaration, so the bare names cannot collide.
def namedSubst : (names : List String) → Check n ((Fin names.length → Ty 0) × List Lean.Name)
  | [] => pure ((fun i => nomatch i), [])
  | nm :: nms => do
    let name := Lean.Name.mkSimple nm
    let (σ, ns) ← namedSubst nms
    pure (Fin.cases (.mk .missing (.FVar name)) σ, name :: ns)

def TyScheme.instantiate (sch : TyScheme) : Check n (Ty 0) := do
  let (σ, _) ← freshSubst sch.tyVars.length
  pure (Ty.subst σ sch.ty)

def OpSig.instantiate (sig : OpSig) : Check n (List (Ty 0) × Ty 0) := do
  let mut m : Lean.NameMap (TyX 0) := {}
  for nm in sig.tyVars do
    let f ← freshTyName
    m := m.insert nm (.FVar f)
  let argTys ← sig.argTys.mapM (Ty.substFVars m)
  let outTy ← Ty.substFVars m sig.outTy
  pure (argTys, outTy)

-- ---- Occurs check ----
mutual
  partial def Ty.occurs (s : Lean.Name) (t : Ty n) :=
    match t with
    | .mk _ t => t.occurs s

  partial def TyX.occurs (s : Lean.Name) (t : TyX n) :=
    match t with
    | .FVar n => n == s
    | .Arrow t1 t2 | .Prod t1 t2 => Ty.occurs s t1 || Ty.occurs s t2
    | .Ref t => Ty.occurs s t
    | .TApp _ ts => ts.attach.any (fun ⟨x, _⟩ => Ty.occurs s x)
    | .Var _ | .Int | .Bool | .Str | .Unit => false
    | .Record xs => xs.attach.any (fun ⟨x, _⟩ => Ty.occurs s x.2)
end




-- ---- Pretty-printing ----

def tyVarNames := ["a", "b", "c", "s", "t", "u"]

def tyVarName (i : Nat) :=
  if h : i < tyVarNames.length then
    tyVarNames[i]
  else
    s!"a{i}"



mutual
partial def Ty.pretty : Ty 0 → String
  | .mk _ t => TyX.pretty t

partial def TyX.pretty : TyX 0 → String
  | .Int => "Int"
  | .Bool => "Bool"
  | .Str => "String"
  | .Unit => "Unit"
  | .Arrow t1 t2 => s!"({Ty.pretty t1} -> {Ty.pretty t2})"
  | .Prod t1 t2 => s!"({Ty.pretty t1} * {Ty.pretty t2})"
  | .Ref t => s!"Ref<{Ty.pretty t}>"
  | .Var i => s!"#{i.val}"
  | .FVar n => s!"{n}"
  | .TApp s [] => s
  | .TApp s ts => s!"{s}<{",".intercalate (ts.attach.map fun ⟨x, _⟩ => Ty.pretty x)}>"
  | .Record xs =>
     "{" ++ (String.intercalate ", " (xs.map fun x => s!"{x.1}: {Ty.pretty x.2}")) ++ "}"


partial def TyScheme.pretty : TyScheme → String
  | { tyVars := tyVars, ty := ty } =>
    let ty0 : Ty 0 := ty.subst (fun i => .mk .missing $ TyX.FVar (Name.mkSimple (tyVarName i)))
    let varNames := tyVars.mapIdx (fun i _ => tyVarName i)
    if varNames.isEmpty then
      Ty.pretty ty0
    else
      s!"∀ {",".intercalate varNames}. {Ty.pretty ty0}"

end

-- Render the type of a binding whose variables the value restriction refused to
-- generalize.  Those variables are not quantified -- each is an as-yet-unknown
-- but fixed type -- so they print as `_a`, `_b`, ... rather than under a `∀`,
-- following OCaml's notation for the same thing.
def TyScheme.prettyWeak : TyScheme → String
  | { tyVars := _, ty := ty } =>
    Ty.pretty (ty.subst (fun i => .mk .missing $ TyX.FVar (Name.mkSimple s!"{tyVarName i}")))

-- ---- Pure substitution (forward declaration) ----
mutual
partial def Ty.substFVarsP' (m : Lean.NameMap (TyX 0)) : Ty 0 → Ty 0
  | .mk stx x => .mk stx (TyX.substFVarsP' m x)

partial def TyX.substFVarsP' (m : Lean.NameMap (TyX 0)) : TyX 0 → TyX 0
  | .Int => .Int
  | .Unit => .Unit
  | .Bool => .Bool
  | .Str => .Str
  | .FVar j => (m.get? j).getD (.FVar j)
  | .Var i => .Var i
  | .Arrow t1 t2 => .Arrow (Ty.substFVarsP' m t1) (Ty.substFVarsP' m t2)
  | .Prod t1 t2 => .Prod (Ty.substFVarsP' m t1) (Ty.substFVarsP' m t2)
  | .Ref t => .Ref (Ty.substFVarsP' m t)
  | .TApp s ts => .TApp s (ts.attach.map fun ⟨x, _⟩ => Ty.substFVarsP' m x)
  | .Record xs => .Record (xs.map fun (x, y) => (x, Ty.substFVarsP' m y))
end

-- ---- Unification ----

-- Internal unification variables are created by `freshTyName`/`freshSubst` as
-- `` Name.mkNum `_tcFresh i ``.  User-written type variables (e.g. `a`) keep
-- their source name, so when unifying two FVars we prefer to eliminate the
-- internal one and keep the user-facing name in the resulting types/hovers.
def Lean.Name.isTcFresh : Lean.Name → Bool
  | .num (.str .anonymous "_tcFresh") _ => true
  | _ => false

-- Assumes the type is already normalized.
partial def solveAux : List Constraint → List (Lean.Name × TyX 0) →
    Check n (List (Lean.Name × TyX 0))
  | [], sbst => pure sbst
  | (stx, t1, t2) :: cs, sbst => do
    if t1 == t2 then solveAux cs sbst
    else
      let elimFVar {k} (n : Lean.Name) (t : TyX 0) :
          Check k (List (Lean.Name × TyX 0)) := do
        if t.occurs n then
          throwErrorAt stx s!"Occurs check failed: {n} occurs in {TyX.pretty t}"
        else
          let sbst1 : Lean.NameMap (TyX 0) := Lean.NameMap.insert {} n t
          let cs' : List Constraint := cs.map (fun ⟨s, x, y⟩ =>
            (s, TyX.substFVarsP' sbst1 x, TyX.substFVarsP' sbst1 y))
          let sbst' : List (Lean.Name × TyX 0) :=
            sbst.map fun (m, u) => (m, TyX.substFVarsP' sbst1 u)
          solveAux cs' ((n, t) :: sbst')
      match t1, t2 with
      | .FVar n, .FVar m =>
        -- Keep the user-facing name when exactly one side is an internal var.
        if n.isTcFresh then elimFVar n (.FVar m) else elimFVar m (.FVar n)
      | .FVar n, t => elimFVar n t
      | t, .FVar n => elimFVar n t
      | .Var i, _ => nomatch i
      | _, .Var i => nomatch i
      | .Arrow a1 b1, .Arrow a2 b2 =>
        solveAux ((stx, a1.get, a2.get) :: (stx, b1.get, b2.get) :: cs) sbst
      | .Prod a1 b1, .Prod a2 b2 =>
        solveAux ((stx, a1.get, a2.get) :: (stx, b1.get, b2.get) :: cs) sbst
      | .Ref a, .Ref b =>
        solveAux ((stx, a.get, b.get) :: cs) sbst
      | .TApp s1 t1s, .TApp s2 t2s => do
        if s1 = s2 ∧ t1s.length = t2s.length then
          let extra : List Constraint :=
            ((t1s.map Ty.get).zip (t2s.map Ty.get)).map (fun ⟨a, b⟩ => (stx, a, b))
          solveAux (extra ++ cs) sbst
        else
          throwErrorAt stx s!"Cannot unify {TyX.pretty t1} with {TyX.pretty t2}"
      | .Record xs, .Record ys => do
          let xs := xs.mergeSort (fun x y => x.1 <= y.1)
          let ys := ys.mergeSort (fun x y => x.1 <= y.1)
          if xs.map Prod.fst = ys.map Prod.fst then
            let extra : List Constraint :=
              (xs.zip ys).map fun ⟨(_, y), (_, w)⟩ => (stx, y.get, w.get)
            solveAux (extra ++ cs) sbst
          else
            throwErrorAt stx s!"Cannot unify {TyX.pretty t1} with {TyX.pretty t2}"
      | _, _ =>
        throwErrorAt stx s!"Cannot unify {TyX.pretty t1} with {TyX.pretty t2}"

-- Solve all currently-buffered constraints, returning a substitution.
def solveAll : Check n (Lean.NameMap (TyX 0)) := do
  let cs := (← get).constraints
  let cs <- cs.mapM fun (stx, t1, t2) => do pure (stx, ← normalizeTyX stx t1, ← normalizeTyX stx t2)
  modify fun s => { s with constraints := [] }
  let sbst ← solveAux cs []
  pure (sbst.foldl (fun (m : Lean.NameMap (TyX 0)) (n, t) => m.insert n t)
    (Lean.mkNameMap (TyX 0)))

def envFVars : Check n Lean.NameSet := do
  pure (← read).frozen

-- ---- Initial environment ----
def initTcOpMap : Std.TreeMap String OpSig :=
  Std.TreeMap.ofList
    [ ("+", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.Int } : OpSig))
    , ("*", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.Int } : OpSig))
    , ("-", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.Int } : OpSig))
    , ("++", ({ tyVars := [], argTys := [Ty.mk .missing .Str, Ty.mk .missing .Str], outTy := Ty.mk .missing .Str } : OpSig))
    , ("&&", ({ tyVars := [], argTys := [Ty.mk .missing .Bool, Ty.mk .missing .Bool], outTy := Ty.mk .missing .Bool } : OpSig))
    , ("not", ({ tyVars := [], argTys := [Ty.mk .missing .Bool], outTy := Ty.mk .missing .Bool } : OpSig))
    , ("||", ({ tyVars := [], argTys := [Ty.mk .missing .Bool, Ty.mk .missing .Bool], outTy := Ty.mk .missing .Bool } : OpSig))
    , ("<", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.mk .missing .Bool } : OpSig))
    , (">", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.mk .missing .Bool } : OpSig))
    , ("<=", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.mk .missing .Bool } : OpSig))
    , (">=", ({ tyVars := [], argTys := [Ty.Int, Ty.Int], outTy := Ty.mk .missing .Bool } : OpSig))
    , ("==", ({ tyVars := [`_laitEqTy]
              , argTys := [Ty.mk .missing (.FVar `_laitEqTy), Ty.mk .missing (.FVar `_laitEqTy)]
              , outTy := Ty.mk .missing .Bool } : OpSig))
    , ("toString", ({ tyVars := [`_a], argTys := [Ty.mk .missing (.FVar `_a)], outTy := Ty.mk .missing .Str } : OpSig))
    ]

-- The primitive types.  Listing them here keeps them out of reach of `type`
-- declarations (`checkTyNameFresh`) and, like the entries above, they are part of
-- every Lait program's starting environment.
def initTyMap : Std.TreeMap String TyVal :=
  Std.TreeMap.ofList
    [ ("Int", TyVal.Builtin)
    , ("Bool", TyVal.Builtin)
    , ("String", TyVal.Builtin)
    , ("Unit", TyVal.Builtin)
    , ("Ref", TyVal.Builtin)
    ]

-- The term-level names built into the language: the boolean literals, the
-- unary primitives, and the reference primitives.  All of them are `lait_exp`
-- syntax rather than definitions (see `Lait/Elab.lean`), so a `def` of the same
-- name could never be referred to; `checkDefNameFresh` rejects it instead of
-- letting it be silently unusable.
def initDefNames : Std.TreeSet String :=
  Std.TreeSet.ofList
    [ "true", "false"
    , "fst", "snd", "not"
    , "builtin_alloc", "builtin_get", "builtin_set"
    ]

-- Given a constructor name, return its owning inductive type's name together
-- with that type's full set of constructor names.  Used to check `match`
-- exhaustiveness.
def ctorTypeInfo (cname : String) (stx : Lean.Syntax) :
    Check n (String × List String) := do
  let env ← read
  match env.opMap.get? cname with
  | none => throwErrorAt stx s!"Unknown constructor in match: {cname}"
  | some sig =>
    match sig.outTy with
    | .mk _ (.TApp tname _) =>
      match env.tyMap.get? tname with
      | some (.Inductive _ ctors) => pure (tname, ctors)
      | _ => throwErrorAt stx s!"Constructor {cname} does not belong to an inductive type"
    | _ => throwErrorAt stx s!"Constructor {cname} does not belong to an inductive type"

-- ---- Inference (constraint generation) ----

def checkBannedLetName (stx : Lean.Syntax) (n : String) : Check m Unit := do
  match n with
  | "true" | "false" => throwErrorAt stx s!"Cannot redefine {n} here"
  | _ => pure ()


def Exp.stx : Exp 0 m → Lean.Syntax
  | .mk stx _ => stx



mutual
  partial def Exp.infer (e : Exp 0 m) : Check m (Ty 0) := do
    let resTy <- match e with
      | .mk stx (.Const c) =>
        match c with
        | .Num _ => pure (.mk stx .Int)
        | .Bool _ => pure (.mk stx .Bool)
        | .String _ => pure (.mk stx .Str)
        | .Unit => pure (.mk stx .Unit)
      | .mk _ (.Var i) => do
        let env ← read
        (env.varMap.get i).instantiate
      | .mk stx (.Lam _ oty e) => do
        let argTy : Ty 0 ← match oty with
          | none => freshTy stx
          | some t => normalizeTy t
        let bodyTy ← withVar (TyScheme.mono argTy) (← Check.locOf stx) (Exp.infer e)
        pure (.mk stx (.Arrow argTy bodyTy))
      | .mk stx (.App e1 e2) => do
        let t1 ← Exp.infer e1
        let t2 ← Exp.infer e2
        let r ← freshTy stx
        addConstraint stx t1 (.mk stx (.Arrow t2 r))
        pure r
      | .mk stx (.Let n oty e1 e2) => do
        checkBannedLetName stx n
        let t1 ← Exp.infer e1
        match oty with
        | none => pure ()
        | some t => do let t ← normalizeTy t; addConstraint stx t1 t
        withVar (TyScheme.mono t1) (← Check.locOf stx) (Exp.infer e2)
      | .mk stx (.If e1 e2 e3) => do
        let t1 ← Exp.infer e1
        let t2 ← Exp.infer e2
        let t3 ← Exp.infer e3
        addConstraint stx t1 (.mk stx .Bool)
        addConstraint stx t2 t3
        pure t2
      | .mk stx (.Pair e1 e2) => do
        let t1 ← Exp.infer e1
        let t2 ← Exp.infer e2
        pure (.mk stx (.Prod t1 t2))
      | .mk stx (.Fst e) => do
        let t ← Exp.infer e
        let a ← freshTy stx
        let b ← freshTy stx
        addConstraint stx t (.mk stx (.Prod a b))
        pure a
      | .mk stx (.Snd e) => do
        let t ← Exp.infer e
        let a ← freshTy stx
        let b ← freshTy stx
        addConstraint stx t (.mk stx (.Prod a b))
        pure b
      | .mk stx (.Alloc e) => do
        let t ← Exp.infer e
        pure (.mk stx (.Ref t))
      | .mk stx (.Error e) => do
        let t ← Exp.infer e
        addConstraint stx t (.mk stx .Str)
        let r <- freshTy stx
        pure r
      | .mk stx (.Print e) => do
        let t ← Exp.infer e
        addConstraint stx t (.mk stx .Str)
        pure (.mk stx .Unit)
      | .mk stx (.Rec _ e1) => do
        let r <- freshTy stx
        let res <- withVar (TyScheme.mono r) (← Check.locOf stx) (Exp.infer e1)
        addConstraint stx r res
        pure res
      | .mk stx (.Deref e) => do
        let t ← Exp.infer e
        let a ← freshTy stx
        addConstraint stx t (.mk stx (.Ref a))
        pure a
      | .mk stx (.Assign e1 e2) => do
        let t1 ← Exp.infer e1
        let t2 ← Exp.infer e2
        addConstraint stx t1 (.mk stx (.Ref t2))
        pure (.mk stx .Unit)
      | .mk stx (.Try e1 e2) => do
        let t1 ← Exp.infer e1
        let t2 ← Exp.infer e2
        addConstraint stx t1 t2
        pure t1
      | .mk stx (.Op s es) => do
        let env ← read
        match env.opMap.get? s with
        | none => throwErrorAt stx s!"Unknown operator/constructor: {s}"
        | some sig => do
          let (argTys, outTy) ← sig.instantiate
          let argEs := es.toList
          if argEs.length ≠ argTys.length then
            throwErrorAt stx
              s!"Operator {s} expects {argTys.length} arguments but got {argEs.length}"
          for (a, t) in argEs.zip argTys do
            let ta ← Exp.infer a
            addConstraint stx ta t
          pure outTy
      | .mk _ (.Loc _) => throwError "Loc should not appear in source"
      | .mk stx (.Match e cases) => do
        let scrutTy ← Exp.infer e
        let resTy ← freshTy stx
        Exp.inferCases cases scrutTy resTy stx []
        pure resTy
      | .mk stx (.MkRecord es) => do
        let ts <- es.toList.mapM (fun (s, e) => do pure (s, <- Exp.infer e))
        pure (.mk stx (.Record ts))
      | .mk stx (.RecordGet e x) => do
        let t <- Exp.infer e
        match t with
        | .mk _ (.Record xs) => match xs.find? (fun (s, _) => s = x) with
          | some (_, t) => pure t
          | none => throwErrorAt stx s!"Field {x} not found in record"
        | _ => throwErrorAt stx s!"Record get of non-record"
    -- A variable occurrence points at its binding; any other expression has no target.
    let loc? ← match e with
      | .mk _ (.Var i) => pure ((← read).varLocs.get i)
      | _ => pure none
    modify fun s => { s with stxMap := (e.stx, resTy, loc?) :: s.stxMap }
    pure resTy

  -- `seen` accumulates the constructor names already matched (in reverse), used
  -- to reject duplicates and, once the case list is exhausted, to verify that
  -- every constructor of the scrutinee's type is covered.
  partial def Exp.inferCases (cs : ExpMatchCases 0 m) (scrutTy resTy : Ty 0)
      (matchStx : Lean.Syntax) (seen : List String) : Check m Unit := do
    match cs with
    | .Nil =>
      match seen with
      | [] => throwErrorAt matchStx "Empty match: cannot determine the type being matched"
      | c :: _ => do
        let (tname, allCtors) ← ctorTypeInfo c matchStx
        let missing := allCtors.filter (fun c => !seen.contains c)
        if !missing.isEmpty then
          throwErrorAt matchStx
            s!"Non-exhaustive match on {tname}: missing constructor(s) {", ".intercalate missing}"
    | .Wild body => do
      -- A catch-all makes the match exhaustive; the body binds no variables.
      let bodyTy ← Exp.infer body
      addConstraint matchStx bodyTy resTy
    | .Cons cname xs body rest => do
      let env ← read
      match env.opMap.get? cname with
      | none => throwErrorAt matchStx s!"Unknown constructor in match: {cname}"
      | some sig => do
        if seen.contains cname then
          throwErrorAt matchStx s!"Duplicate constructor in match: {cname}"
        let (argTys, outTy) ← sig.instantiate
        if h : argTys.length = xs.length then
          addConstraint matchStx scrutTy outTy
          let body' : Exp 0 (m + argTys.length) := body.cast (by rw [h])
          -- Pattern variables are de Bruijn indexed with the first variable at
          -- index 0 (see `casesFromSurface`: `xs ++ vars`).  Since `withVar`
          -- pushes each new binding to index 0, we must introduce the argument
          -- types innermost-first, i.e. reversed, so `argTys[i]` lands at index i.
          let bodyTy ← Exp.inferWithVars argTys.reverse (← Check.locOf matchStx)
            (body'.cast (by simp))
          addConstraint matchStx bodyTy resTy
          Exp.inferCases rest scrutTy resTy matchStx (cname :: seen)
        else
          throwErrorAt matchStx
            s!"Constructor {cname} expects {argTys.length} arguments but pattern has {xs.length}"

  -- Extend the env with monomorphic bindings for each ty in `argTys`,
  -- then infer `body`.
  partial def Exp.inferWithVars {m : Nat} :
      (argTys : List (Ty 0)) → Option DeclarationLocation → Exp 0 (m + argTys.length) →
      Check m (Ty 0)
    | [], _, body => Exp.infer (body.cast (by simp))
    | t :: ts, loc?, body =>
        withVar (TyScheme.mono t) loc? $
          Exp.inferWithVars (m := m + 1) ts loc? (body.cast (by simp; omega))
end

-- ---- The value restriction ----

-- The context a value test descends into: `isCtor` says which `Op` names are data
-- constructors rather than primitives like `+`, and `isCtorVar` which in-scope
-- variables are the constructor functions `mkConstrFns` generates.  `TcEnv` supplies
-- both (`TcEnv.valueCtx`); they are packaged together so that the mutual block below
-- can thread them under binders, where `isCtorVar` shifts.
structure ValueCtx (m : Nat) where
  isCtor : String → Bool
  isCtorVar : Fin m → Bool

-- Extend a `ValueCtx` under a binder: the newly bound variable, at index 0, is not
-- a constructor, and every old index shifts up by one.
def ValueCtx.under (c : ValueCtx m) : ValueCtx (m + 1) :=
  { isCtor := c.isCtor, isCtorVar := Fin.cases false c.isCtorVar }

def TcEnv.valueCtx (env : TcEnv n) : ValueCtx n :=
  { isCtor := env.isCtorName, isCtorVar := env.isCtorVar }

mutual
  -- Is `e` a syntactic value ("non-expansive", in the SML sense)?  Evaluating one of
  -- these allocates no reference cells and performs no other effect, which is what
  -- makes it sound to generalize its type variables; see the `DeclDef` case of
  -- `Decl.check`.
  def Exp.isValue (c : ValueCtx m) : Exp n m → Bool
    | .mk _ x => ExpX.isValue c x

  def ExpX.isValue (c : ValueCtx m) : ExpX n m → Bool
    | .Const _ | .Var _ | .Lam .. | .Loc _ => true
    -- `rec x => e` builds a closure without running `e` (see `Exp.eval`), but a
    -- projection below may force it later, so `e` must be non-expansive too.
    | .Rec _ e => Exp.isValue c.under e
    | .Pair e1 e2 => Exp.isValue c e1 && Exp.isValue c e2
    -- Projecting out of a value neither allocates nor has an effect.  These are not
    -- values in SML -- which has no projection forms -- but they are how
    -- `elabDefMutual` pulls each function out of its recursive bundle, so ruling them
    -- out would make every `and` group monomorphic.
    | .Fst e | .Snd e | .RecordGet e _ => Exp.isValue c e
    | .MkRecord es => ExpRecord.isValue c es
    | .Let _ _ e1 e2 => Exp.isValue c e1 && Exp.isValue c.under e2
    | .Op s es => c.isCtor s && ExpList.isValue c es
    -- A constructor application is non-expansive when its arguments are: it only
    -- builds the constructed value (or, if partial, a closure).  Every other
    -- application may run arbitrary code, so it is expansive.
    | .App e1 e2 => Exp.isCtorApp c e1 && Exp.isValue c e2
    | .If .. | .Error _ | .Print _ | .Match .. | .Alloc _ | .Deref _
    | .Assign .. | .Try .. => false

  -- Is `e` a constructor applied to (possibly zero) values, i.e. the head of an
  -- application spine that is safe to apply one more value to?  Surface `Cons h t`
  -- reaches the type checker as nested `App`s of the generated `def Cons`, not as an
  -- `Op`, so this is what makes `def empty := Map []` generalize.
  def Exp.isCtorApp (c : ValueCtx m) : Exp n m → Bool
    | .mk _ (.Var i) => c.isCtorVar i
    | .mk _ (.App e1 e2) => Exp.isCtorApp c e1 && Exp.isValue c e2
    | _ => false

  def ExpList.isValue (c : ValueCtx m) : ExpList n m → Bool
    | .Nil => true
    | .Cons e es => Exp.isValue c e && ExpList.isValue c es

  def ExpRecord.isValue (c : ValueCtx m) : ExpRecord n m → Bool
    | .Nil => true
    | .Cons _ e es => Exp.isValue c e && ExpRecord.isValue c es
end

-- ---- Generalization ----

-- Close gens[0] outermost (Var 0 in the resulting scheme), gens[1] next, etc.
def closeMany : (gs : List Lean.Name) → Ty 0 → Ty gs.length
  | [], t => t
  | g :: gs, t => (closeMany gs t).close g

def Ty.generalize (frozen : Lean.NameSet) (t : Ty 0) : TyScheme :=
  let gens := (Ty.fvars t).toList.filter (fun n => !frozen.contains n)
  let closed : Ty gens.length := closeMany gens t
  let tyVars : List String := gens.mapIdx (fun i _ => s!"a{i}")
  have hlen : tyVars.length = gens.length := by
    simp [tyVars]
  { tyVars := tyVars, ty := hlen ▸ closed }

def applySubstTy (sbst : Lean.NameMap (TyX 0)) (t : Ty 0) :
    Check n (Ty 0) :=
  normalizeTy (Ty.substFVarsP' sbst t)

-- ---- Decl checking ----

def addStxMapHovers (sbst : NameMap (TyX 0)) : Check n Unit := do
  forM ((<- get).stxMap) fun (stx, ty, loc?) => do
    let ty' <- applySubstTy sbst ty
    Check.runMetaM (addHoverInfo stx s!"{ty'.pretty}" loc?)
  modify fun s => { s with stxMap := [] }


def withSolveAll (k : Check n α) : Check n (NameMap (TyX 0) × α) := do
  let res <- k
  let sbst <- solveAll
  addStxMapHovers sbst
  pure (sbst, res)

partial def Decl.check : {n m : Nat} → (d : Decl n m) → Check m α → Check n α
  | _, _, .mk _ .DeclNil, k => k
  | _, _, .mk _ (.DeclConcat d1 d2), k => Decl.check d1 (Decl.check d2 k)
  | _, _, .mk dstx (.DeclDef name tvars oty e), k => do
    -- Open the type variables of the scheme with skolem FVars that keep the
    -- user-written names, so hovers inside the body show e.g. `k`/`v`.
    if tvars.hasDup then throwErrorAt dstx s!"Duplicate type variable in declaration"
    checkDefNameFresh dstx name
    let (σ, skolems) ← namedSubst tvars
    let e' := Exp.substTy σ e
    let oty' : Option (Ty 0) := oty.map (Ty.subst σ)
    let (sbst, inferredTy) ← withSolveAll do
      let inferredTy ← Exp.infer e'
      match oty' with
      | none => pure ()
      | some t => do
        let t ← normalizeTy t
        addConstraint dstx inferredTy t
      pure inferredTy
    let finalTy ← applySubstTy sbst inferredTy
    let envFV ← envFVars
    -- Apply the substitution to envFV (FVars in env that got resolved
    -- should not be frozen; only their *remaining* FVars are).  But for
    -- simplicity, we freeze the original envFV; this is conservative but
    -- correct.
    let _ := skolems  -- skolems are free in finalTy and not in env, so
                      -- they'll be generalized naturally.
    let scheme := Ty.generalize envFV finalTy
    -- The value restriction.  Generalizing the type of an expression that
    -- allocates is unsound once `Ref` is in the language: `def r := builtin_alloc([])`
    -- at type `∀ a. Ref<List<a>>` would let one use of `r` store `Int`s into the
    -- single underlying cell and another read them back as `String`s.  So only a
    -- syntactic value may be generalized.
    --
    -- The left-over variables of a non-value cannot simply stay free either.
    -- Each declaration solves its own constraints (`withSolveAll`) and the
    -- resulting substitution is never propagated back into the schemes already
    -- stored in the environment, so a free variable in a binding's type could be
    -- unified with `Int` in one later declaration and with `String` in another --
    -- exactly the unsoundness we are ruling out.  Report them instead.
    if !(Exp.isValue (← read).valueCtx e') && !scheme.tyVars.isEmpty then
      throwErrorAt dstx s!"This declaration would create a reference with a polymorphic type,\
       such as Ref<List<a>>; this is disallowed. Give {name} a type annotation so that it isn't polymorphic."
    Check.runMetaM (addHoverInfo dstx s!"{scheme.pretty}")
    withDefName dstx name scheme k
  | _, _, .mk _ (.DeclEval e), k => do
    let _ ← withSolveAll (Exp.infer e)
    k
  | _, _, .mk dstx (.DeclTest e1 e2), k => do
    let _ ← withSolveAll do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      addConstraint dstx t1 t2
    k
  | _, _, .mk _ (.DeclTestError e _), k => do
    let _ ← withSolveAll (Exp.infer e)
    k
  | _, _, .mk stx (.DeclCheck e), k => do
    let (sbst, res) ← withSolveAll (Exp.infer e)
    let t ← applySubstTy sbst res
    let envFV ← envFVars
    let scheme := Ty.generalize envFV t
    -- `#check` binds nothing, so an un-generalizable type is not an error here;
    -- it just reports the weak variables as such (see the `DeclDef` case above).
    let rendered := if Exp.isValue (← read).valueCtx e then scheme.pretty else scheme.prettyWeak
    logInfoAt stx rendered
    k
  | _, _, .mk dstx (.DeclTypeAlias tname alias), k => do
    checkTyNameFresh dstx tname
    if alias.hasDupFVars then
      throwErrorAt dstx s!"Type alias cannot have duplicate type variables"
    let _ <- normalizeTy alias.ty
    withReader (fun env => { env with tyMap := env.tyMap.insert tname (.Alias alias) }) k
  | _, _, .mk dstx (.DeclInductive tname tvars cs), k => do
    -- Constructor names must be globally unique: reject re-defining an existing
    -- operator/constructor, or repeating a name within this declaration, so we
    -- never silently overwrite an `opMap` entry.
    checkTyNameFresh dstx tname
    if tvars.hasDup then
      throwErrorAt dstx s!"Type definition cannot have duplicate type variables"
    let env ← read
    let mut declared : List String := []
    for (cname, _) in cs do
      if declared.contains cname then
        throwErrorAt dstx s!"Error when defining {tname}: Constructor {cname} is defined twice in type {tname}"
      if env.opMap.contains cname then
        throwErrorAt dstx s!"Error when defining {tname}: Constructor {cname} is already defined"
      declared := cname :: declared
    -- Generate FVar names for the inductive's tyVars; same names are used
    -- across all constructors so that uses of e.g. 'a in arg vs out types
    -- are linked.
    let (σ, names) ← freshSubst tvars.length
    -- outTy: TApp tname [FVar n0, FVar n1, ...]
    let outArgs : List (Ty 0) := names.map fun n => .mk .missing (.FVar n)
    let outTy : Ty 0 := .mk .missing (.TApp tname outArgs)
    let argTysList : List (String × List (Ty 0)) :=
      cs.map (fun (cname, args) => (cname, args.map fun (_, ty) => Ty.subst σ ty))
    withReader (fun env =>
      let opMap' := argTysList.foldl (fun m (cname, argTys) =>
        m.insert cname ({ tyVars := names, argTys := argTys, outTy := outTy } : OpSig))
        env.opMap
      { env with opMap := opMap', tyMap := env.tyMap.insert tname (.Inductive tvars.length (cs.map (·.1))) }) k
