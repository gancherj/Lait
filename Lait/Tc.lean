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
  -- The explicit type variables scoped at an enclosing declaration: the `U` component
  -- of an SML context (Definition, sections 4.6 and 4.10, rule 15).  A declaration's
  -- own type variables -- the ones it declares, plus every one written in an
  -- annotation that is not part of a smaller declaration (`Exp.unguardedTyVars`) --
  -- are *rigid* while its bound expression is checked: the caller chooses them, so
  -- unification may not instantiate them (`solveAux`) and an inner `let` may not
  -- generalize them (`envFVars`).  The declaration that scopes them quantifies them
  -- itself, which is why its closure is taken in the enclosing environment, where
  -- they are absent.
  tyVarScope : Lean.NameSet

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
  -- The solution of every constraint solved so far, in the declaration being checked.
  -- Generalizing at a `let` (`Exp.infer`) means knowing the bound expression's type
  -- there, so constraints are solved at each `let` rather than once per declaration,
  -- and each solution has to be kept: it applies to the types the surrounding
  -- expressions have already built.  Idempotent, and extended only by `solveAll`.
  subst : Lean.NameMap (TyX 0) := {}
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
  | .Arrow t1 t2 | .Prod t1 t2 => (Ty.fvars t1).union (Ty.fvars t2)
  | .Ref t => Ty.fvars t
  | .TApp _ ts => ts.foldl (fun s t => s.union (Ty.fvars t)) {}
  | .Var _ | .Int | .Bool | .Str | .Unit => {}
end

-- ---- Explicit type variables ----

-- The explicit type variables that this expression contributes to the `tyvarseq` of the
-- declaration it belongs to.  Section 4.6 of the Definition: an occurrence of a type
-- variable is *unguarded* in a declaration when it is not part of a smaller declaration
-- inside it, and a variable is scoped at the innermost declaration in which it occurs
-- unguarded.
--
-- Lait's declarations are `def` and `let`, and its only annotation positions are the
-- ones on `fun` and `let` binders.  So this collects the variables of every `fun`
-- annotation, and descends into a `let`'s body but not into its bound expression or
-- annotation -- those belong to the `let`'s own declaration, which scopes them itself.
--
-- Every `FVar` reached here was written by the user: the internal unification variables
-- `freshTyName` makes only come into existence during inference.
--
-- One wrinkle: a `let` a surface pass synthesized stands for no declaration the user
-- wrote, so it scopes nothing.  `elabDefMutual` pins a function's declared return type
-- with a `let`, and the variables of *that* annotation belong to the `def` -- otherwise
-- `def newStack () : Stack<a> := alloc []` would be read as SML reads
-- `fn () => let val ret : 'a stack = ref [] in ret end`, whose inner declaration the
-- value restriction forbids.  A `$` cannot occur in a source name.
def isSyntheticBinder (x : String) : Bool := x.startsWith "$"

mutual
partial def Exp.unguardedTyVars : Exp n m → Lean.NameSet
  | .mk _ x => ExpX.unguardedTyVars x

partial def ExpX.unguardedTyVars : ExpX n m → Lean.NameSet
  | .Lam _ oty e => ((oty.map Ty.fvars).getD {}).union (Exp.unguardedTyVars e)
  | .Let x oty e1 e2 =>
    if isSyntheticBinder x then
      (Exp.letTyVars x oty e1).union (Exp.unguardedTyVars e2)
    else Exp.unguardedTyVars e2
  | .App e1 e2 | .Pair e1 e2 | .Assign e1 e2 | .Try e1 e2 =>
    (Exp.unguardedTyVars e1).union (Exp.unguardedTyVars e2)
  | .If e1 e2 e3 =>
    ((Exp.unguardedTyVars e1).union (Exp.unguardedTyVars e2)).union (Exp.unguardedTyVars e3)
  | .Rec _ e | .Error e | .Print e | .Fst e | .Snd e | .Alloc e | .Deref e =>
    Exp.unguardedTyVars e
  | .Op _ es => ExpList.unguardedTyVars es
  | .Match e cs => (Exp.unguardedTyVars e).union (ExpMatchCases.unguardedTyVars cs)
  | .Const _ | .Var _ | .Loc _ => {}

partial def ExpList.unguardedTyVars : ExpList n m → Lean.NameSet
  | .Nil => {}
  | .Cons e es => (Exp.unguardedTyVars e).union (ExpList.unguardedTyVars es)

partial def ExpMatchCases.unguardedTyVars : ExpMatchCases n m → Lean.NameSet
  | .Nil => {}
  | .Wild e => Exp.unguardedTyVars e
  | .Cons _ _ e cs => (Exp.unguardedTyVars e).union (ExpMatchCases.unguardedTyVars cs)

-- The explicit type variables scoped at the declaration `let x : oty := e1`, before
-- removing the ones an enclosing declaration already scopes.
partial def Exp.letTyVars (x : String) (oty : Option (Ty n)) (e1 : Exp n m) : Lean.NameSet :=
  if isSyntheticBinder x then {}
  else ((oty.map Ty.fvars).getD {}).union (Exp.unguardedTyVars e1)
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
    tyVarScope := env.tyVarScope,
    -- The binding being pushed sits at index 0, i.e. at level `n`.
    ctorLevels := if isCtor then env.ctorLevels.insert n else env.ctorLevels
  }

/-- Bring the explicit type variables `us` into scope, i.e. SML's `C ⊕ U`.  Used by
every declaration form for the variables it scopes; see `TcEnv.tyVarScope`. -/
def withTyVarScope (us : Lean.NameSet) (k : Check n α) : Check n α :=
  withReader (fun env => { env with tyVarScope := env.tyVarScope.union us }) k

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
end




-- ---- Pretty-printing ----

def tyVarNames := ["a", "b", "c", "s", "t", "u"]

def tyVarName (i : Nat) :=
  if h : i < tyVarNames.length then
    tyVarNames[i]
  else
    s!"a{i}"



-- Types print with only the parentheses their structure needs, following the same
-- grammar `lait_ty` parses: `->` and `*` are both right-associative and `*` binds
-- tighter, so `a * b -> c -> d` reads as `(a * b) -> (c -> d)` and prints back that
-- way.  `prec` is the level the surrounding context requires -- 0 anywhere, 1 tighter
-- than `->`, 2 atomic -- and a type is parenthesized when its own level is lower.
mutual
partial def Ty.prettyPrec (prec : Nat) : Ty 0 → String
  | .mk _ t => TyX.prettyPrec prec t

partial def TyX.prettyPrec (prec : Nat) : TyX 0 → String
  | .Int => "Int"
  | .Bool => "Bool"
  | .Str => "String"
  | .Unit => "Unit"
  | .Arrow t1 t2 =>
    let s := s!"{Ty.prettyPrec 1 t1} -> {Ty.prettyPrec 0 t2}"
    if prec > 0 then s!"({s})" else s
  | .Prod t1 t2 =>
    let s := s!"{Ty.prettyPrec 2 t1} * {Ty.prettyPrec 1 t2}"
    if prec > 1 then s!"({s})" else s
  | .Ref t => s!"Ref<{Ty.prettyPrec 0 t}>"
  | .Var i => s!"#{i.val}"
  | .FVar n => s!"{n}"
  | .TApp s [] => s
  | .TApp s ts => s!"{s}<{",".intercalate (ts.attach.map fun ⟨x, _⟩ => Ty.prettyPrec 0 x)}>"
end

def Ty.pretty (t : Ty 0) : String := Ty.prettyPrec 0 t
def TyX.pretty (t : TyX 0) : String := TyX.prettyPrec 0 t

-- Render a type scheme, naming its quantified variables `a`, `b`, ... prefixed by
-- `pfx`.  There is no `∀`: a scheme is written just like the type it generalizes, as
-- SML writes it (`val id = fn : 'a -> 'a`), and it is the *names* that say which
-- variables are quantified -- see `TyScheme.prettyWeak`.
def TyScheme.prettyWith (pfx : String) : TyScheme → String
  | { tyVars := _, ty := ty } =>
    Ty.pretty (ty.subst (fun i => .mk .missing $ TyX.FVar (Name.mkSimple (pfx ++ tyVarName i))))

def TyScheme.pretty : TyScheme → String := TyScheme.prettyWith ""

-- Render the type of a binding whose variables the value restriction refused to
-- generalize.  Those variables are not quantified -- each is an as-yet-unknown but
-- fixed type -- so they print as `_a`, `_b`, ..., following OCaml's notation for the
-- same thing.
def TyScheme.prettyWeak : TyScheme → String := TyScheme.prettyWith "_"

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
end

-- ---- Unification ----

-- Internal unification variables are created by `freshTyName`/`freshSubst` as
-- `` Name.mkNum `_tcFresh i ``.  User-written type variables (e.g. `a`) keep
-- their source name, so when unifying two FVars we prefer to eliminate the
-- internal one and keep the user-facing name in the resulting types/hovers.
def Lean.Name.isTcFresh : Lean.Name → Bool
  | .num (.str .anonymous "_tcFresh") _ => true
  | _ => false

-- Assumes the type is already normalized.  `rigid` holds the explicit type variables
-- in scope (`TcEnv.tyVarScope`): those stand for a type the caller of the enclosing
-- declaration chooses, so unification may not instantiate them -- an SML type variable
-- is a semantic object of its own, not an unknown to be solved for.
partial def solveAux (rigid : Lean.NameSet) : List Constraint → List (Lean.Name × TyX 0) →
    Check n (List (Lean.Name × TyX 0))
  | [], sbst => pure sbst
  | (stx, t1, t2) :: cs, sbst => do
    if t1 == t2 then solveAux rigid cs sbst
    else
      let elimFVar {k} (n : Lean.Name) (t : TyX 0) :
          Check k (List (Lean.Name × TyX 0)) := do
        if rigid.contains n then
          throwErrorAt stx s!"Cannot make the type variable {n} equal to {TyX.pretty t}: \
            {n} is chosen by whoever uses this definition, so its body cannot require \
            it to be {TyX.pretty t}"
        else if t.occurs n then
          throwErrorAt stx s!"Occurs check failed: {n} occurs in {TyX.pretty t}"
        else
          let sbst1 : Lean.NameMap (TyX 0) := Lean.NameMap.insert {} n t
          let cs' : List Constraint := cs.map (fun ⟨s, x, y⟩ =>
            (s, TyX.substFVarsP' sbst1 x, TyX.substFVarsP' sbst1 y))
          let sbst' : List (Lean.Name × TyX 0) :=
            sbst.map fun (m, u) => (m, TyX.substFVarsP' sbst1 u)
          solveAux rigid cs' ((n, t) :: sbst')
      match t1, t2 with
      | .FVar n, .FVar m =>
        -- Eliminate a variable that is free to be instantiated -- never a rigid one --
        -- and among those the internal one, so that a user-facing name survives into
        -- the types shown in errors and hovers.
        if rigid.contains n && rigid.contains m then
          throwErrorAt stx s!"Cannot make the type variables {n} and {m} equal: each is \
            chosen separately by whoever uses this definition"
        else if rigid.contains n then elimFVar m (.FVar n)
        else if rigid.contains m then elimFVar n (.FVar m)
        else if n.isTcFresh then elimFVar n (.FVar m) else elimFVar m (.FVar n)
      | .FVar n, t => elimFVar n t
      | t, .FVar n => elimFVar n t
      | .Var i, _ => nomatch i
      | _, .Var i => nomatch i
      | .Arrow a1 b1, .Arrow a2 b2 =>
        solveAux rigid ((stx, a1.get, a2.get) :: (stx, b1.get, b2.get) :: cs) sbst
      | .Prod a1 b1, .Prod a2 b2 =>
        solveAux rigid ((stx, a1.get, a2.get) :: (stx, b1.get, b2.get) :: cs) sbst
      | .Ref a, .Ref b =>
        solveAux rigid ((stx, a.get, b.get) :: cs) sbst
      | .TApp s1 t1s, .TApp s2 t2s => do
        if s1 = s2 ∧ t1s.length = t2s.length then
          let extra : List Constraint :=
            ((t1s.map Ty.get).zip (t2s.map Ty.get)).map (fun ⟨a, b⟩ => (stx, a, b))
          solveAux rigid (extra ++ cs) sbst
        else
          throwErrorAt stx s!"Cannot unify {TyX.pretty t1} with {TyX.pretty t2}"
      | _, _ =>
        throwErrorAt stx s!"Cannot unify {TyX.pretty t1} with {TyX.pretty t2}"

-- Solve all currently-buffered constraints and fold the solution into the substitution
-- accumulated in the state, which is returned.  This runs wherever a type has to be
-- *known* rather than merely built: at every `let`, whose bound expression is
-- generalized there, and at the end of a declaration.
def solveAll : Check n (Lean.NameMap (TyX 0)) := do
  let st ← get
  let sbst0 := st.subst
  -- A constraint may have been recorded before an earlier solve resolved some of its
  -- variables, so the solution so far applies to it first.
  let cs <- st.constraints.mapM fun (stx, t1, t2) => do
    pure (stx, ← normalizeTyX stx (TyX.substFVarsP' sbst0 t1),
               ← normalizeTyX stx (TyX.substFVarsP' sbst0 t2))
  modify fun s => { s with constraints := [] }
  let solved ← solveAux (← read).tyVarScope cs []
  -- Those constraints had `sbst0` applied, so no variable `sbst0` resolves can appear
  -- in `solved`'s domain: composing the two is `solved` on `sbst0`'s range, then union.
  let solved : Lean.NameMap (TyX 0) :=
    solved.foldl (fun (m : Lean.NameMap (TyX 0)) (n, t) => m.insert n t)
      (Lean.mkNameMap (TyX 0))
  let composed := sbst0.foldl
    (fun (m : Lean.NameMap (TyX 0)) n t => m.insert n (TyX.substFVarsP' solved t)) solved
  modify fun s => { s with subst := composed }
  pure composed

-- The type variables that generalization here must leave alone: those free in the type
-- of an in-scope binding, and the explicit ones an enclosing declaration scopes --
-- together, `tyvars(C)` of the Definition's closure operation (section 4.8).
--
-- `TcEnv.frozen` records each binding's variables as they stood when it was pushed, so
-- the substitution accumulated since has to be applied before they are read: a variable
-- that has since been resolved is no longer free in the environment, but the variables
-- of the type it was resolved to are.
def envFVars : Check n Lean.NameSet := do
  let env ← read
  let sbst := (← get).subst
  pure (env.frozen.foldl (init := env.tyVarScope) fun acc nm =>
    match sbst.get? nm with
    | some t => acc.union (TyX.fvars t)
    | none => acc.insert nm)

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
    | .Fst e | .Snd e => Exp.isValue c e
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

-- Apply the substitution accumulated so far.  A type is built before the constraints
-- that determine it are solved, so anything that gets *inspected* -- generalized,
-- printed, or compared against the environment -- has to be run through it first.
def applyCurSubst (t : Ty 0) : Check n (Ty 0) := do
  applySubstTy (← get).subst t

-- The Definition's closure operation `Clos_{C,valbind}` (section 4.8) for one binding.
--
-- `t` is the type inferred for the bound expression, with the constraints in scope
-- already solved; `envFV` the type variables of the enclosing context `C` (`envFVars`);
-- `us` the explicit type variables this declaration scopes, which `C` therefore does
-- not contain; and `isVal` whether the bound expression is non-expansive.  A
-- non-expansive binding quantifies every variable not fixed by `C`; an expansive one
-- quantifies nothing -- the value restriction.
--
-- Rule 15's side condition `U ∩ tyvars(VE') = ∅` is what the check below enforces: a
-- type variable the user wrote must come out quantified.  If the value restriction left
-- it un-quantified it would instead escape as a fixed-but-unknown type, and the
-- signature would silently mean something other than what it says.
def closeBinding (stx : Lean.Syntax) (name : String) (us envFV : Lean.NameSet)
    (isVal : Bool) (t : Ty 0) : Check n TyScheme := do
  let scheme := if isVal then Ty.generalize envFV t else TyScheme.mono t
  unless us.isEmpty do
    let escaped := (Ty.fvars scheme.ty).toList.filter us.contains
    unless escaped.isEmpty do
      let vars := ", ".intercalate (escaped.map toString)
      let why := if isVal then "the surrounding context already fixes it"
        else s!"the body of {name} is not a value, so the value restriction cannot \
          quantify it"
      let out := if isVal then "" else
        ", or make its body a value (for instance by turning it into a function)"
      throwErrorAt stx s!"The type variable(s) {vars} written in the type of {name} \
        cannot be generalized here: {why}.  Give {name} a type that does not mention \
        {vars}{out}."
  pure scheme

-- Drop the part of the accumulated substitution that nothing can refer to any more.
-- Called once a top-level declaration is finished, when the only types left are the
-- schemes in the environment: `TcEnv.frozen` names their free variables, and one that
-- is not among them can never be looked up again.  In practice every top-level scheme
-- is closed -- `Decl.check` rejects a declaration that would leave a free variable
-- behind -- so this empties the substitution between declarations.
def pruneSubst : Check n Unit := do
  let frozen := (← read).frozen
  modify fun s => { s with subst := s.subst.filter (fun nm _ => frozen.contains nm) }

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
        -- `let n : oty := e1 in e2` is the Definition's `let val n : oty = e1 in e2 end`
        -- (rules 4 and 15): a declaration, so its bound expression is generalized here.
        --
        -- The explicit type variables this declaration scopes are rigid while `e1` is
        -- checked, and quantified by the closure below; the ones an enclosing
        -- declaration already scopes are not among them (section 4.6).
        let outerUs := (← read).tyVarScope
        let us := (Exp.letTyVars n oty e1).filter (fun nm => !outerUs.contains nm)
        let t1 ← withTyVarScope us do
          let t1 ← Exp.infer e1
          match oty with
          | none => pure ()
          | some t => do let t ← normalizeTy t; addConstraint stx t1 t
          -- Closing over `t1` means knowing it, so the constraints in scope are solved
          -- here rather than at the end of the declaration.
          let _ ← solveAll
          applyCurSubst t1
        -- `envFVars` is read outside `withTyVarScope`, since the closure is taken in
        -- the context `C` that this declaration extends -- `us` is what it quantifies.
        let envFV ← envFVars
        let isVal := Exp.isValue (← read).valueCtx e1
        let scheme ← closeBinding stx n us envFV isVal t1
        withVar scheme (← Check.locOf stx) (Exp.infer e2)
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

-- ---- Decl checking ----

-- Render a type for a hover.  What is left of a unification variable once the
-- declaration is solved is a type nothing determined -- either because the expression
-- really is used at only one, unconstrained, type, or because the `let` that binds it
-- generalized it.  Printing the internal name (`_tcFresh.137`) says nothing and shifts
-- whenever an earlier declaration changes, so those variables are numbered `_a`, `_b`,
-- ... within the type being shown, as `TyScheme.prettyWeak` does.
def prettyHover (t : Ty 0) : String :=
  let unknowns := (Ty.fvars t).toList.filter (·.isTcFresh)
  let m : Lean.NameMap (TyX 0) := unknowns.zipIdx.foldl
    (fun m (nm, i) => m.insert nm (.FVar (Name.mkSimple s!"_{tyVarName i}")))
    (Lean.mkNameMap (TyX 0))
  Ty.pretty (Ty.substFVarsP' m t)

def addStxMapHovers (sbst : NameMap (TyX 0)) : Check n Unit := do
  forM ((<- get).stxMap) fun (stx, ty, loc?) => do
    let ty' <- applySubstTy sbst ty
    Check.runMetaM (addHoverInfo stx (prettyHover ty') loc?)
  modify fun s => { s with stxMap := [] }


-- Run `k`, solve whatever constraints it leaves buffered, and attach the hovers it
-- recorded.  Inner `let`s have solved their own constraints already; their solutions
-- are in `TcState.subst`, which is what the hovers are rendered with.
def withSolveAll (k : Check n α) : Check n α := do
  let res <- k
  let _ <- solveAll
  addStxMapHovers (← get).subst
  pure res

partial def Decl.check : {n m : Nat} → (d : Decl n m) → Check m α → Check n α
  | _, _, .mk _ .DeclNil, k => k
  | _, _, .mk _ (.DeclConcat d1 d2), k => Decl.check d1 (Decl.check d2 k)
  | _, _, .mk dstx (.DeclDef name tvars oty e), k => do
    -- Open the type variables of the scheme with FVars that keep the user-written
    -- names, so hovers inside the body show e.g. `k`/`v`.
    if tvars.hasDup then throwErrorAt dstx s!"Duplicate type variable in declaration"
    checkDefNameFresh dstx name
    let (σ, skolems) ← namedSubst tvars
    let e' := Exp.substTy σ e
    let oty' : Option (Ty 0) := oty.map (Ty.subst σ)
    -- The `tyvarseq` of the Definition's rule 15: the variables this declaration
    -- declares, plus the ones implicitly scoped at it -- those written in an annotation
    -- inside the body that no inner `let` scopes first (section 4.6).  They are rigid
    -- while the body is checked, and quantified by the closure afterwards.
    let us := skolems.foldl (fun (acc : Lean.NameSet) nm => acc.insert nm)
      (((oty'.map Ty.fvars).getD {}).union (Exp.unguardedTyVars e'))
    let inferredTy ← withSolveAll do
      withTyVarScope us do
        let inferredTy ← Exp.infer e'
        match oty' with
        | none => pure ()
        | some t => do
          let t ← normalizeTy t
          addConstraint dstx inferredTy t
        pure inferredTy
    let finalTy ← applyCurSubst inferredTy
    -- Read outside `withTyVarScope`: the closure quantifies `us`, so `C` excludes it.
    let envFV ← envFVars
    let isVal := Exp.isValue (← read).valueCtx e'
    -- The value restriction.  Generalizing the type of an expression that allocates is
    -- unsound once `Ref` is in the language: `def r := builtin_alloc([])` at type
    -- `∀ a. Ref<List<a>>` would let one use of `r` store `Int`s into the single
    -- underlying cell and another read them back as `String`s.  So only a syntactic
    -- value may be generalized (`Exp.isValue`).
    --
    -- Unlike at a `let`, the left-over variables of a top-level non-value cannot simply
    -- stay free: rule 87 of the Definition lets no free type variable into the basis a
    -- top-level declaration produces, and here they could not be resolved even in
    -- principle -- each command is elaborated on its own, so nothing later can
    -- determine them.  Report them instead.
    if !isVal then
      let weak := Ty.generalize envFV finalTy
      if !weak.tyVars.isEmpty then
        throwErrorAt dstx s!"Value restriction: the body of {name} is not a value, so \
          its type {weak.prettyWeak} cannot be generalized.  Give {name} a type \
          annotation that fixes the remaining type variable(s), or make its body a \
          value (for instance by turning it into a function)."
    let scheme ← closeBinding dstx name us envFV isVal finalTy
    Check.runMetaM (addHoverInfo dstx s!"{scheme.pretty}")
    pruneSubst
    withDefName dstx name scheme k
  -- `#eval e`, `#test e1 === e2` and `#check e` each stand for a declaration of the
  -- Definition's `val it = e` shape, so each scopes the explicit type variables written
  -- in its expressions, exactly as a `def` does.
  | _, _, .mk _ (.DeclEval e), k => do
    let _ ← withSolveAll (withTyVarScope (Exp.unguardedTyVars e) (Exp.infer e))
    pruneSubst
    k
  | _, _, .mk dstx (.DeclTest e1 e2), k => do
    let us := (Exp.unguardedTyVars e1).union (Exp.unguardedTyVars e2)
    let _ ← withSolveAll do
      withTyVarScope us do
        let t1 ← Exp.infer e1
        let t2 ← Exp.infer e2
        addConstraint dstx t1 t2
    pruneSubst
    k
  | _, _, .mk _ (.DeclTestError e _), k => do
    let _ ← withSolveAll (withTyVarScope (Exp.unguardedTyVars e) (Exp.infer e))
    pruneSubst
    k
  | _, _, .mk stx (.DeclCheck e), k => do
    let res ← withSolveAll (withTyVarScope (Exp.unguardedTyVars e) (Exp.infer e))
    let t ← applyCurSubst res
    let envFV ← envFVars
    let scheme := Ty.generalize envFV t
    -- `#check` binds nothing, so an un-generalizable type is not an error here;
    -- it just reports the weak variables as such (see the `DeclDef` case above).
    let rendered := if Exp.isValue (← read).valueCtx e then scheme.pretty else scheme.prettyWeak
    logInfoAt stx rendered
    pruneSubst
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
