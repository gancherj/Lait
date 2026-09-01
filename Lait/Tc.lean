import Lait.Syntax
import Lait.Utils
import Lean

open Lean Elab Command

-- Signatures of builtins
structure OpSig where
  -- Free variables
  tyVars : List Lean.Name
  argTys : List (Ty 0)
  outTy : Ty 0

inductive TyVal where
  -- Arity, plus this type's constructor names in declaration order (for `match`
  -- exhaustiveness checking).
  | Inductive : Nat -> List String -> TyVal
  | Alias : TyScheme -> TyVal
  -- A primitive type (`Int`, `Bool`, ...).  These have their own `TyX` constructors, so
  -- the entry carries nothing and exists only to reserve the name.
  | Builtin : TyVal

structure TcEnv (n : Nat) where
  opMap : Std.TreeMap String OpSig
  tyMap : Std.TreeMap String TyVal
  curSyntax : Lean.Syntax
  -- In-scope variable schemes, innermost (de Bruijn index 0) first.  A length-indexed
  -- vector rather than `Fin n → TyScheme`: building the latter from nested `Fin.cases`
  -- closures in `withVar` loses sharing, making deep lookups exponential.
  varMap : Vec n TyScheme
  -- Where "go to definition" jumps for each in-scope variable, ordered like `varMap`.
  -- `none` when the binding has no usable source position.
  varLocs : Vec n (Option DeclarationLocation)
  -- Where each top-level name spliced in by `#include` was defined.  Its syntax carries
  -- no positions of its own (it belongs to another file), so `#include` records this.
  defLocs : Std.TreeMap String DeclarationLocation
  -- Running union of `Ty.fvars` over every in-scope scheme, maintained by `withVar` so
  -- that `envFVars` is O(1).
  frozen : Lean.NameSet
  -- Top-level `def` names so far, including the defs generated for constructors.  A
  -- top-level definition may not shadow one (`withDefName`); `let`/`fun`/`match` binders
  -- go through `withVar` and shadow freely.
  defNames : Std.TreeSet String
  -- De Bruijn *levels* (not indices, which shift) of the in-scope variables standing for
  -- data constructors.  Applying one is non-expansive, so the value restriction has to
  -- tell them from ordinary functions; see `Exp.isValue`.
  ctorLevels : Std.TreeSet Nat
  -- Explicit type variables scoped at an enclosing declaration: the `U` of an SML context
  -- (Definition 4.6, 4.10, rule 15).  They are *rigid* while that declaration's body is
  -- checked -- the caller chooses them, so unification may not instantiate them
  -- (`solveAux`) and an inner `let` may not generalize them (`envFVars`).
  tyVarScope : Lean.NameSet

-- Does `s` name a data constructor, as opposed to a primitive operator (`+`, `==`, ...)
-- that also lives in `opMap`?
def TcEnv.isCtorName (env : TcEnv n) (s : String) : Bool :=
  match env.opMap.get? s with
  | some { outTy := .mk _ (.TApp tname _), .. } =>
    match env.tyMap.get? tname with
    | some (.Inductive ..) => true
    | _ => false
  | _ => false

-- Is the variable at index `i` a constructor function?  Index `i` of `n` bindings is
-- level `n - 1 - i`.
def TcEnv.isCtorVar (env : TcEnv n) (i : Fin n) : Bool :=
  env.ctorLevels.contains (n - 1 - i.val)

abbrev Constraint := Lean.Syntax × TyX 0 × TyX 0

structure TcState where
  constraints : List Constraint := []
  -- Every solution found so far in the declaration being checked.  Constraints are solved
  -- at each `let` rather than once per declaration, and each solution has to be kept: it
  -- applies to types the surrounding expressions have already built.  Idempotent, and
  -- extended only by `solveAll`.
  subst : Lean.NameMap (TyX 0) := {}
  freshCounter : Nat := 0
  -- Hovers to attach once the constraints are solved: an expression's syntax, its type,
  -- and -- for a variable occurrence -- the binding it resolves to.
  stxMap : List (Lean.Syntax × Ty 0 × Option DeclarationLocation) := []
  -- Variables some binding inside the declaration being checked was refused
  -- generalization over -- the value restriction's leftovers.  A hover must not show one
  -- as polymorphic (`hoverSubst`); like `TcEnv.frozen`, the entries are the names as of
  -- when they were recorded, so the substitution has to be applied before they are used
  -- (`weakFVars`).  Cleared with the rest of the declaration's state by `pruneSubst`.
  weakVars : Lean.NameSet := {}

abbrev Check n := ReaderT (TcEnv n) (StateT TcState TermElabM)

instance : MonadExcept String (Check n) where
  throw s := throwError s
  tryCatch _ _ := throwError "Unhandled exception"

def List.hasDup [BEq α] : List α → Bool
  | [] => false
  | x :: xs => xs.contains x || xs.hasDup

-- ---- Fresh type variables ----

def freshTyName : Check n Lean.Name := do
  let s ← get
  set { s with freshCounter := s.freshCounter + 1 }
  pure (Lean.Name.mkNum `_tcFresh s.freshCounter)

def freshTy (stx : Lean.Syntax := .missing) : Check n (Ty 0) := do
  pure (.mk stx (.FVar (← freshTyName)))

-- Was this name made by `freshTyName`?  User-written type variables keep their source
-- name, so unification prefers to eliminate the internal one and keep the readable name
-- in the resulting types and hovers.
def Lean.Name.isTcFresh : Lean.Name → Bool
  | .num (.str .anonymous "_tcFresh") _ => true
  | _ => false

def addConstraint (stx : Lean.Syntax) (t1 t2 : Ty 0) : Check n Unit :=
  modify fun s => { s with constraints := (stx, t1.get, t2.get) :: s.constraints }

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

-- The free variables of a type in the order they print, with repeats.  Used wherever they
-- are given names to show -- a message (`weakSubst`), a hover (`hoverSubst`), a scheme
-- (`Ty.generalize`) -- since the order has to be the reader's, not the order the solver
-- happened to allocate them in.
mutual
partial def Ty.fvarsInOrder : Ty n → List Lean.Name
  | .mk _ t => TyX.fvarsInOrder t

partial def TyX.fvarsInOrder : TyX n → List Lean.Name
  | .FVar n => [n]
  | .Arrow t1 t2 | .Prod t1 t2 => Ty.fvarsInOrder t1 ++ Ty.fvarsInOrder t2
  | .Ref t => Ty.fvarsInOrder t
  | .TApp _ ts => (ts.attach.map fun ⟨x, _⟩ => Ty.fvarsInOrder x).flatten
  | .Var _ | .Int | .Bool | .Str | .Unit => []
end

-- The type variables of an optional annotation.
def annFVars (oty : Option (Ty n)) : Lean.NameSet := (oty.map Ty.fvars).getD {}

mutual
  partial def Ty.occurs (s : Lean.Name) : Ty n → Bool
    | .mk _ t => t.occurs s

  partial def TyX.occurs (s : Lean.Name) : TyX n → Bool
    | .FVar n => n == s
    | .Arrow t1 t2 | .Prod t1 t2 => Ty.occurs s t1 || Ty.occurs s t2
    | .Ref t => Ty.occurs s t
    | .TApp _ ts => ts.attach.any (fun ⟨x, _⟩ => Ty.occurs s x)
    | .Var _ | .Int | .Bool | .Str | .Unit => false
end

-- ---- Substitution and normalization ----

-- Apply an FVar substitution.  Unlike `Ty.substFVars`, a name the map does not mention is
-- left alone rather than being an error.
mutual
partial def Ty.substFVarsP' (m : Lean.NameMap (TyX 0)) : Ty 0 → Ty 0
  | .mk stx x => .mk stx (TyX.substFVarsP' m x)

partial def TyX.substFVarsP' (m : Lean.NameMap (TyX 0)) : TyX 0 → TyX 0
  | .FVar j => (m.get? j).getD (.FVar j)
  | .Arrow t1 t2 => .Arrow (Ty.substFVarsP' m t1) (Ty.substFVarsP' m t2)
  | .Prod t1 t2 => .Prod (Ty.substFVarsP' m t1) (Ty.substFVarsP' m t2)
  | .Ref t => .Ref (Ty.substFVarsP' m t)
  | .TApp s ts => .TApp s (ts.attach.map fun ⟨x, _⟩ => Ty.substFVarsP' m x)
  | .Int => .Int
  | .Unit => .Unit
  | .Bool => .Bool
  | .Str => .Str
  | .Var i => .Var i
end

-- Expand type aliases and check the arity of every type application.
mutual
partial def normalizeTy : Ty k → Check n (Ty k)
  | .mk stx t => do pure (.mk stx (← normalizeTyX stx t))

partial def normalizeTyX (stx : Lean.Syntax) (t : TyX k) : Check n (TyX k) :=
  match t with
  | .Int | .Unit | .Str | .Bool | .Var _ | .FVar _ => pure t
  | .Arrow t1 t2 => do pure (.Arrow (← normalizeTy t1) (← normalizeTy t2))
  | .Prod t1 t2 => do pure (.Prod (← normalizeTy t1) (← normalizeTy t2))
  | .Ref t => do pure (.Ref (← normalizeTy t))
  | .TApp s ts => do
      let ts ← ts.mapM normalizeTy
      match (← read).tyMap.get? s with
      | some (.Alias { tyVars, ty }) =>
        if h : ts.length = tyVars.length then
          normalizeTyX stx (ty.subst (h ▸ ts.get)).get
        else throwErrorAt stx s!"Wrong number of arguments to {s}"
      | some (.Inductive arity _) =>
        if arity == ts.length then pure (.TApp s ts)
        else throwErrorAt stx s!"Wrong number of arguments to {s}"
      | some .Builtin => throwErrorAt stx s!"{s} is a built-in type and takes no arguments"
      | none => throwErrorAt stx s!"Unknown type constructor: {s}"
end

def applySubstTy (sbst : Lean.NameMap (TyX 0)) (t : Ty 0) : Check n (Ty 0) :=
  normalizeTy (Ty.substFVarsP' sbst t)

-- Apply the substitution accumulated so far.  A type is built before the constraints that
-- determine it are solved, so anything *inspected* -- generalized, printed, or compared
-- against the environment -- has to be run through this first.
def applyCurSubst (t : Ty 0) : Check n (Ty 0) := do
  applySubstTy (← get).subst t

-- ---- Pretty-printing ----

def tyVarNames := ["a", "b", "c", "s", "t", "u"]

def tyVarName (i : Nat) :=
  if h : i < tyVarNames.length then tyVarNames[i] else s!"a{i}"

-- Print with only the parentheses the structure needs, matching the grammar `lait_ty`
-- parses: `->` and `*` are right-associative and `*` binds tighter, so `a * b -> c -> d`
-- reads as `(a * b) -> (c -> d)` and prints back that way.  `prec` is the level the
-- context requires -- 0 anywhere, 1 tighter than `->`, 2 atomic -- and a type is
-- parenthesized when its own level is lower.
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

-- Render a scheme behind `pfx`, calling each quantified variable what the scheme calls
-- it: the name the user wrote where there was one, and `a`, `b`, ... for the rest
-- (`genNames`).  There is no `∀`: a scheme is written just like the type it generalizes,
-- as SML writes it (`val id = fn : 'a -> 'a`), and it is the *names* that say which
-- variables are quantified.
def TyScheme.prettyWith (pfx : String) (sch : TyScheme) : String :=
  Ty.pretty (sch.ty.subst fun i => .mk .missing (.FVar (Name.mkSimple (pfx ++ sch.tyVars.get i))))

def TyScheme.pretty : TyScheme → String := TyScheme.prettyWith ""

-- Render a binding whose variables the value restriction refused to generalize.  They are
-- not quantified -- each is an as-yet-unknown but fixed type -- so they print as `_a`,
-- `_b`, ..., following OCaml's notation for the same thing.
def TyScheme.prettyWeak : TyScheme → String := TyScheme.prettyWith "_"

-- Rename the internal unification variables of `ts` to `_a`, `_b`, ..., as
-- `TyScheme.prettyWeak` names un-quantified ones.  An internal name (`_tcFresh.137`) says
-- nothing to a reader and its number shifts whenever anything elaborated earlier changes.
--
-- Names are handed out in order of first appearance, so the result depends only on the
-- shape of what is printed -- never on which numbers the solver happened to allocate.
-- The map covers all of `ts` at once, so a variable shared by several types reads the
-- same in each.
def weakSubst (ts : List (TyX 0)) : Lean.NameMap (TyX 0) :=
  let unknowns := ((ts.flatMap TyX.fvarsInOrder).filter (·.isTcFresh)).eraseDups
  unknowns.zipIdx.foldl
    (fun m (nm, i) => m.insert nm (.FVar (Name.mkSimple s!"_{tyVarName i}")))
    (Lean.mkNameMap (TyX 0))

-- Name the unification variables left in a declaration's hovers.  `fixed` holds the ones
-- that must not read as polymorphic: those the enclosing environment fixes, and those an
-- inner binding's value restriction refused to generalize (`weakFVars`).  Everything else
-- still unsolved at the end of the declaration is what the declaration's own scheme
-- quantifies, so it is named like a quantified variable -- `a`, `b`, ... -- against `_a`,
-- `_b`, ... for the fixed ones, as `TyScheme.pretty` and `prettyWeak` name theirs.  This
-- is what makes a hover agree with the type reported for the declaration around it: an
-- occurrence of `mkPair : ∀ a b. a -> b -> a * b` reads `a -> b -> a * b`, not
-- `_a -> _b -> _a * _b`, which would claim the value restriction had hit it.
--
-- One map covers `ts`, i.e. every hover of the declaration at once, so a variable reads
-- the same in the hover of a subexpression as in the hover of the whole body.  Names go
-- out in order of first appearance -- with `ts` outermost-first, that is the order the
-- declaration's own signature uses (`Ty.generalize`), and it never depends on the numbers
-- the solver happened to allocate.
--
-- A variable the *user* wrote keeps its name, and the generated names skip anything so
-- written: in `def f (x : a) := fun y => (x, y)` the `a` of the hover is the user's `a`,
-- and `y`'s type is named `b`.
def hoverSubst (fixed : Lean.NameSet) (ts : List (Ty 0)) : Lean.NameMap (TyX 0) :=
  let names := (ts.flatMap Ty.fvarsInOrder).eraseDups
  let taken := names.foldl (fun s nm => if nm.isTcFresh then s else s.insert nm)
    Lean.NameSet.empty
  -- Enough candidates to survive dropping the taken ones: at most `names.length` of the
  -- first `2 * names.length + 1` are taken.
  let supply : List Lean.Name :=
    ((List.range (2 * names.length + 1)).map (Name.mkSimple ∘ tyVarName)).filter
      (fun nm => !taken.contains nm)
  -- One sequence of letters for both kinds, so that `a` and `_a` never turn up in the
  -- same hover reading like one variable: `fun z => let r := builtin_alloc([]) in (z, r)`
  -- is `a -> a * Ref<List<_b>>`, against the `a -> a * Ref<List<b>>` its `def` reports.
  ((names.filter (·.isTcFresh)).zip supply).foldl
    (fun m (nm, new) =>
      m.insert nm (.FVar (if fixed.contains nm then Name.mkSimple ("_" ++ new.toString)
                          else new)))
    (Lean.mkNameMap (TyX 0))

-- Render the two types of a unification failure, naming their internal variables
-- consistently: `Cannot unify List<_a> with _b -> Int`, never `_tcFresh.140`/`_tcFresh.142`.
def prettyPair (t1 t2 : TyX 0) : String × String :=
  let m := weakSubst [t1, t2]
  (TyX.pretty (TyX.substFVarsP' m t1), TyX.pretty (TyX.substFVarsP' m t2))

-- ---- Extending the environment ----

def withVar (ty : TyScheme) (loc? : Option DeclarationLocation)
    (k : Check (n + 1) α) (isCtor : Bool := false) : Check n α := fun env =>
  -- `TcEnv n` and `TcEnv (n + 1)` are different types, so the fields are copied out
  -- rather than updated with `{ env with .. }`.
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

/-- Bring the explicit type variables `us` into scope, i.e. SML's `C ⊕ U`.  Used by every
declaration form for the variables it scopes; see `TcEnv.tyVarScope`. -/
def withTyVarScope (us : Lean.NameSet) (k : Check n α) : Check n α :=
  withReader (fun env => { env with tyVarScope := env.tyVarScope.union us }) k

/-- The "go to definition" target of a binding introduced by `stx`.  `stx` belongs to the
file being elaborated, so its own start is the target. -/
def Check.locOf (stx : Lean.Syntax) : Check n (Option DeclarationLocation) := do
  mkStartLocation? (← getMainModule) stx

-- Top-level names are unique, so re-defining one is an error rather than shadowing.
-- Checked before the body is inferred, so a duplicate is reported instead of whatever
-- errors the (now unreachable) body may contain.  `_` is a wildcard, never a clash.
def checkDefNameFresh (stx : Lean.Syntax) (name : String) : Check n Unit := do
  if name != "_" && (← read).defNames.contains name then
    throwErrorAt stx s!"{name} is already defined"

-- Bind a top-level `def`.
def withDefName (stx : Lean.Syntax) (name : String) (ty : TyScheme)
    (k : Check (n + 1) α) : Check n α := do
  checkDefNameFresh stx name
  -- A name spliced in from another module is declared by position-less syntax; prefer
  -- where `#include` recorded it as defined.
  let loc? ← match (← read).defLocs.get? name with
    | some loc => pure (some loc)
    | none => Check.locOf stx
  -- A constructor's `def` is generated after the `type` declaring it, so `opMap` already
  -- knows the name by the time we bind it.
  let isCtor := (← read).isCtorName name
  withReader (fun env => { env with defNames := env.defNames.insert name })
    (withVar ty loc? k (isCtor := isCtor))

-- Type names are unique too: `type` may not re-declare an earlier or a primitive type
-- (`initTyMap` seeds those; `lait_ty` also lexes them as keywords, so in practice the
-- parser rejects them first).
def checkTyNameFresh (stx : Lean.Syntax) (tname : String) : Check n Unit := do
  if (← read).tyMap.contains tname then
    throwErrorAt stx s!"Type {tname} is already defined"

-- ---- Instantiation ----

def TyScheme.mono (t : Ty 0) : TyScheme := { tyVars := [], ty := t }

-- Open the bound type variables `xs` as FVars, `nameOf` choosing each one's name.
-- Returns the substitution together with the names used (position `i` ↔ `names[i]`).
def openTyVars (nameOf : String → Check n Lean.Name) :
    (xs : List String) → Check n ((Fin xs.length → Ty 0) × List Lean.Name)
  | [] => pure ((fun i => nomatch i), [])
  | x :: xs => do
    let nm ← nameOf x
    let (σ, ns) ← openTyVars nameOf xs
    pure (Fin.cases (.mk .missing (.FVar nm)) σ, nm :: ns)

-- Instantiate with fresh internal variables.
def freshSubst (xs : List String) : Check n ((Fin xs.length → Ty 0) × List Lean.Name) :=
  openTyVars (fun _ => freshTyName) xs

-- Instantiate keeping the user-written names, so hovers inside a `def` with an explicit
-- signature show `k`/`v` rather than internal `_tcFresh` ones.  A `def`'s declared
-- variables are distinct and are generalized away before the next declaration, so the
-- bare names cannot collide.
def namedSubst (xs : List String) : Check n ((Fin xs.length → Ty 0) × List Lean.Name) :=
  openTyVars (fun x => pure (Lean.Name.mkSimple x)) xs

def TyScheme.instantiate (sch : TyScheme) : Check n (Ty 0) := do
  let (σ, _) ← freshSubst sch.tyVars
  pure (Ty.subst σ sch.ty)

def OpSig.instantiate (sig : OpSig) : Check n (List (Ty 0) × Ty 0) := do
  let mut m : Lean.NameMap (TyX 0) := {}
  for nm in sig.tyVars do
    m := m.insert nm (.FVar (← freshTyName))
  pure (← sig.argTys.mapM (Ty.substFVars m), ← Ty.substFVars m sig.outTy)

-- ---- Unification ----

-- Assumes both types are normalized.  `rigid` holds the explicit type variables in scope
-- (`TcEnv.tyVarScope`): those stand for a type the *caller* of the enclosing declaration
-- picks, so unification may not instantiate them -- an SML type variable is a semantic
-- object of its own, not an unknown to be solved for.
partial def solveAux (rigid : Lean.NameSet) : List Constraint → List (Lean.Name × TyX 0) →
    Check n (List (Lean.Name × TyX 0))
  | [], sbst => pure sbst
  | (stx, t1, t2) :: cs, sbst => do
    if t1 == t2 then solveAux rigid cs sbst
    else
      let cannotUnify : Check n (List (Lean.Name × TyX 0)) :=
        let (s1, s2) := prettyPair t1 t2
        throwErrorAt stx s!"Cannot unify {s1} with {s2}"
      -- Solve `n := t`, propagating it into the remaining constraints and the solution.
      let elimFVar {k} (n : Lean.Name) (t : TyX 0) :
          Check k (List (Lean.Name × TyX 0)) := do
        -- `n` is named alongside `t` so that, when it occurs there, both read the same.
        let (ns, ts) := prettyPair (.FVar n) t
        if rigid.contains n then
          throwErrorAt stx s!"Cannot make the type variable {ns} equal to {ts}: \
            {ns} is chosen by whoever uses this definition, so its body cannot require \
            it to be {ts}"
        else if t.occurs n then
          throwErrorAt stx s!"Occurs check failed: {ns} occurs in {ts}"
        else
          let one : Lean.NameMap (TyX 0) := Lean.NameMap.insert {} n t
          solveAux rigid
            (cs.map fun (s, x, y) => (s, TyX.substFVarsP' one x, TyX.substFVarsP' one y))
            ((n, t) :: sbst.map fun (m, u) => (m, TyX.substFVarsP' one u))
      match t1, t2 with
      | .FVar n, .FVar m =>
        -- Eliminate a variable that is free to be instantiated -- never a rigid one --
        -- and among those the internal one, so a user-facing name survives into errors
        -- and hovers.
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
      | .Arrow a1 b1, .Arrow a2 b2 | .Prod a1 b1, .Prod a2 b2 =>
        solveAux rigid ((stx, a1.get, a2.get) :: (stx, b1.get, b2.get) :: cs) sbst
      | .Ref a, .Ref b => solveAux rigid ((stx, a.get, b.get) :: cs) sbst
      | .TApp s1 t1s, .TApp s2 t2s =>
        if s1 = s2 ∧ t1s.length = t2s.length then
          let extra : List Constraint :=
            ((t1s.map Ty.get).zip (t2s.map Ty.get)).map fun (a, b) => (stx, a, b)
          solveAux rigid (extra ++ cs) sbst
        else cannotUnify
      | _, _ => cannotUnify

-- Solve every buffered constraint and fold the solution into the substitution in the
-- state, which is returned.  Runs wherever a type has to be *known* rather than merely
-- built: at every `let`, and at the end of a declaration.
def solveAll : Check n (Lean.NameMap (TyX 0)) := do
  let sbst0 := (← get).subst
  -- A constraint may predate an earlier solve, so apply the solution so far to it first.
  let cs ← (← get).constraints.mapM fun (stx, t1, t2) => do
    pure (stx, ← normalizeTyX stx (TyX.substFVarsP' sbst0 t1),
               ← normalizeTyX stx (TyX.substFVarsP' sbst0 t2))
  modify fun s => { s with constraints := [] }
  let solved : Lean.NameMap (TyX 0) :=
    (← solveAux (← read).tyVarScope cs []).foldl (fun m (n, t) => m.insert n t)
      (Lean.mkNameMap (TyX 0))
  -- Those constraints had `sbst0` applied, so nothing `sbst0` resolves can appear in
  -- `solved`'s domain: composing is `solved` on `sbst0`'s range, then union.
  let composed := sbst0.foldl
    (fun (m : Lean.NameMap (TyX 0)) n t => m.insert n (TyX.substFVarsP' solved t)) solved
  modify fun s => { s with subst := composed }
  pure composed

-- The type variables generalization must leave alone: those free in an in-scope binding's
-- type, and the explicit ones an enclosing declaration scopes -- together `tyvars(C)` of
-- the Definition's closure operation (4.8).
--
-- `frozen` records each binding's variables as of when it was pushed, so the substitution
-- accumulated since has to be applied: a variable resolved in the meantime is no longer
-- free in the environment, but the variables of what it resolved to are.
def envFVars : Check n Lean.NameSet := do
  let env ← read
  let sbst := (← get).subst
  pure (env.frozen.foldl (init := env.tyVarScope) fun acc nm =>
    match sbst.get? nm with
    | some t => acc.union (TyX.fvars t)
    | none => acc.insert nm)

-- The variables recorded by `markWeak`, under the substitution found since -- the reading
-- `envFVars` gives of `TcEnv.frozen`, and for the same reason.
def weakFVars : Check n Lean.NameSet := do
  let sbst := (← get).subst
  pure ((← get).weakVars.foldl (init := {}) fun acc nm =>
    match sbst.get? nm with
    | some t => acc.union (TyX.fvars t)
    | none => acc.insert nm)

-- Record `t`'s variables as ones generalization has passed over: the bound expression of
-- this binding is expansive, so the value restriction quantified none of them and each is
-- one fixed but unknown type.  Only hovers read this (`hoverSubst`); the schemes
-- themselves already say as much by not quantifying them.
def markWeak (t : Ty 0) : Check n Unit :=
  modify fun s => { s with weakVars := s.weakVars.union (Ty.fvars t) }

-- Drop the part of the substitution nothing can refer to any more.  Called once a
-- top-level declaration is finished, when the only types left are the environment's
-- schemes: `frozen` names their free variables, and anything else can never be looked up
-- again.  Every top-level scheme is in practice closed, so this empties the substitution
-- between declarations.
def pruneSubst : Check n Unit := do
  let frozen := (← read).frozen
  modify fun s =>
    { s with subst := s.subst.filter (fun nm _ => frozen.contains nm), weakVars := {} }

-- ---- Initial environment ----

def initTcOpMap : Std.TreeMap String OpSig :=
  let int : Ty 0 := .mk .missing .Int
  let bool : Ty 0 := .mk .missing .Bool
  let str : Ty 0 := .mk .missing .Str
  -- A signature with no type variables of its own.
  let mono (argTys : List (Ty 0)) (outTy : Ty 0) : OpSig := { tyVars := [], argTys, outTy }
  let eqTy : Ty 0 := .mk .missing (.FVar `_laitEqTy)
  let anyTy : Ty 0 := .mk .missing (.FVar `_a)
  Std.TreeMap.ofList
    [ ("+", mono [int, int] int)
    , ("*", mono [int, int] int)
    , ("-", mono [int, int] int)
    , ("++", mono [str, str] str)
    , ("&&", mono [bool, bool] bool)
    , ("not", mono [bool] bool)
    , ("||", mono [bool, bool] bool)
    , ("<", mono [int, int] bool)
    , (">", mono [int, int] bool)
    , ("<=", mono [int, int] bool)
    , (">=", mono [int, int] bool)
    , ("==", { tyVars := [`_laitEqTy], argTys := [eqTy, eqTy], outTy := bool })
    , ("toString", { tyVars := [`_a], argTys := [anyTy], outTy := str })
    ]

-- The primitive types.  Listing them here keeps them out of reach of `type` declarations
-- (`checkTyNameFresh`) and puts them in every program's starting environment.
def initTyMap : Std.TreeMap String TyVal :=
  Std.TreeMap.ofList
    [ ("Int", TyVal.Builtin)
    , ("Bool", TyVal.Builtin)
    , ("String", TyVal.Builtin)
    , ("Unit", TyVal.Builtin)
    , ("Ref", TyVal.Builtin)
    ]

-- The term-level names built into the language.  All are `lait_exp` syntax rather than
-- definitions, so a `def` of the same name could never be referred to; `checkDefNameFresh`
-- rejects it instead of letting it be silently unusable.
def initDefNames : Std.TreeSet String :=
  Std.TreeSet.ofList
    [ "true", "false"
    , "fst", "snd", "not"
    , "builtin_alloc", "builtin_get", "builtin_set"
    ]

-- The inductive type a constructor belongs to, with that type's full set of constructor
-- names.  Used to check `match` exhaustiveness.
def ctorTypeInfo (cname : String) (stx : Lean.Syntax) : Check n (String × List String) := do
  let env ← read
  let notInductive : Check n (String × List String) :=
    throwErrorAt stx s!"Constructor {cname} does not belong to an inductive type"
  match env.opMap.get? cname with
  | none => throwErrorAt stx s!"Unknown constructor in match: {cname}"
  | some { outTy := .mk _ (.TApp tname _), .. } =>
    match env.tyMap.get? tname with
    | some (.Inductive _ ctors) => pure (tname, ctors)
    | _ => notInductive
  | some _ => notInductive

-- ---- Explicit type variables (Definition 4.6) ----

-- An occurrence of a type variable is *unguarded* in a declaration when it is not part of
-- a smaller declaration inside it, and a variable is scoped at the innermost declaration
-- in which it occurs unguarded.  Lait's declarations are `def` and `let`, and its only
-- annotation positions are on `fun` and `let` binders -- so this collects every `fun`
-- annotation, and descends into a `let`'s body but not into its bound expression or
-- annotation, which belong to the `let`'s own declaration.
--
-- Every `FVar` reached here was written by the user: `freshTyName`'s internal variables
-- only come into existence during inference.

-- A `let` a surface pass synthesized (`elabDefMutual`'s return-type pin) stands for no
-- declaration the user wrote, so it scopes nothing of its own.  A `$` cannot occur in a
-- source name.
def isSyntheticBinder (x : String) : Bool := x.startsWith "$"

mutual
partial def Exp.unguardedTyVars : Exp n m → Lean.NameSet
  | .mk _ x => ExpX.unguardedTyVars x

partial def ExpX.unguardedTyVars : ExpX n m → Lean.NameSet
  | .Lam _ oty e => (annFVars oty).union (Exp.unguardedTyVars e)
  -- A real `let` is its own declaration and scopes its annotation and bound expression
  -- itself, so only the body is descended into.  A synthetic one scopes nothing, so both
  -- fall to the enclosing declaration -- that is what puts the return type of a `def` in
  -- an `and` group (pinned by `elabDefMutual`'s `$mutual$ret`) into the `def`'s tyvarseq.
  | .Let x oty e1 e2 =>
    let body := Exp.unguardedTyVars e2
    if isSyntheticBinder x then
      ((annFVars oty).union (Exp.unguardedTyVars e1)).union body
    else body
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
end

-- The explicit type variables scoped at the declaration `let x : oty := e1`, before
-- removing the ones an enclosing declaration already scopes.  A synthetic `let` is no
-- declaration of the user's, so it scopes nothing.
def Exp.letTyVars (x : String) (oty : Option (Ty n)) (e1 : Exp n m) : Lean.NameSet :=
  if isSyntheticBinder x then {}
  else (annFVars oty).union (Exp.unguardedTyVars e1)

-- ---- The value restriction ----

-- What a value test needs from the environment: which `Op` names are data constructors
-- rather than primitives like `+`, and which in-scope variables are constructor
-- functions.  Packaged together so the mutual block can thread them under binders, where
-- `isCtorVar` shifts.
structure ValueCtx (m : Nat) where
  isCtor : String → Bool
  isCtorVar : Fin m → Bool

-- Under a binder the new variable, at index 0, is not a constructor, and every old index
-- shifts up by one.
def ValueCtx.under (c : ValueCtx m) : ValueCtx (m + 1) :=
  { isCtor := c.isCtor, isCtorVar := Fin.cases false c.isCtorVar }

def TcEnv.valueCtx (env : TcEnv n) : ValueCtx n :=
  { isCtor := env.isCtorName, isCtorVar := env.isCtorVar }

mutual
  -- Is `e` a syntactic value ("non-expansive")?  Evaluating one allocates no reference
  -- cells and has no other effect, which is what makes generalizing its type variables
  -- sound; see the `DeclDef` case of `Decl.check`.
  def Exp.isValue (c : ValueCtx m) : Exp n m → Bool
    | .mk _ x => ExpX.isValue c x

  def ExpX.isValue (c : ValueCtx m) : ExpX n m → Bool
    | .Const _ | .Var _ | .Lam .. | .Loc _ => true
    -- `rec x => e` builds a closure without running `e`, but a projection below may force
    -- it later, so `e` must be non-expansive too.
    | .Rec _ e => Exp.isValue c.under e
    | .Pair e1 e2 => Exp.isValue c e1 && Exp.isValue c e2
    -- Projecting out of a value neither allocates nor has an effect.  Not values in SML,
    -- which has no projection forms, but they are how `elabDefMutual` pulls each function
    -- out of its recursive bundle -- ruling them out would make every `and` group
    -- monomorphic.
    | .Fst e | .Snd e => Exp.isValue c e
    | .Let _ _ e1 e2 => Exp.isValue c e1 && Exp.isValue c.under e2
    | .Op s es => c.isCtor s && ExpList.isValue c es
    -- A constructor application is non-expansive when its arguments are: it only builds
    -- the constructed value (or, if partial, a closure).  Any other application may run
    -- arbitrary code.
    | .App e1 e2 => Exp.isCtorApp c e1 && Exp.isValue c e2
    | .If .. | .Error _ | .Print _ | .Match .. | .Alloc _ | .Deref _
    | .Assign .. | .Try .. => false

  -- Is `e` a constructor applied to (possibly zero) values, i.e. the head of a spine that
  -- is safe to apply one more value to?  Surface `Cons h t` reaches the type checker as
  -- nested `App`s of the generated `def Cons`, not as an `Op`, so this is what makes
  -- `def empty := Map []` generalize.
  def Exp.isCtorApp (c : ValueCtx m) : Exp n m → Bool
    | .mk _ (.Var i) => c.isCtorVar i
    | .mk _ (.App e1 e2) => Exp.isCtorApp c e1 && Exp.isValue c e2
    | _ => false

  def ExpList.isValue (c : ValueCtx m) : ExpList n m → Bool
    | .Nil => true
    | .Cons e es => Exp.isValue c e && ExpList.isValue c es
end

-- ---- Generalization ----

-- Close `gs[0]` outermost (`Var 0` in the resulting scheme), `gs[1]` next, and so on.
def closeMany : (gs : List Lean.Name) → Ty 0 → Ty gs.length
  | [], t => t
  | g :: gs, t => (closeMany gs t).close g

-- What to call each of the variables a scheme quantifies, in the order they are
-- quantified.  A variable the user wrote keeps its name -- `def swap (q : s * t) : t * s`
-- reports `s * t -> t * s`, not `a * b -> b * a`, which renames the declaration out from
-- under its own signature.  The solver's internal variables have no name worth showing,
-- so they take `a`, `b`, ..., skipping any the user has already used.
def genNames (gens : List Lean.Name) : List String :=
  let taken := gens.filterMap fun nm => if nm.isTcFresh then none else some nm.toString
  -- At most `gens.length` of the first `2 * gens.length + 1` candidates are taken, so
  -- what is left is long enough for the internal variables among `gens`.
  let supply := ((List.range (2 * gens.length + 1)).map tyVarName).filter (!taken.contains ·)
  gens.mapIdx fun i nm =>
    if nm.isTcFresh then
      -- The i-th name overall is the k-th generated one, where k counts the internal
      -- variables before it.
      supply[(gens.take i).countP (·.isTcFresh)]?.getD s!"a{i}"
    else nm.toString

def Ty.generalize (frozen : Lean.NameSet) (t : Ty 0) : TyScheme :=
  -- Quantified in order of first appearance, since that is the order `TyScheme.pretty`
  -- names them in: `a` is the first variable the reader meets.  A `NameSet`'s order is
  -- the internal names' *hash* order, which is no order at all to a reader -- and, for
  -- the internal variables an instantiation leaves behind, not even stable between two
  -- elaborations of the same expression (`#check mkPair` printed `b -> a -> b * a` in
  -- one file and `a -> b -> a * b` in the next).  Same reasoning as `weakSubst`.
  let gens := (Ty.fvarsInOrder t).eraseDups.filter (fun n => !frozen.contains n)
  let closed : Ty gens.length := closeMany gens t
  let tyVars : List String := genNames gens
  have hlen : tyVars.length = gens.length := by simp [tyVars, genNames]
  { tyVars := tyVars, ty := hlen ▸ closed }

/-- The Definition's closure operation `Clos_{C,valbind}` (4.8) for one binding.

`t` is the inferred type with the constraints in scope already solved, `envFV` the type
variables of the enclosing context `C` (`envFVars`), `us` the explicit type variables this
declaration scopes (so `C` does not contain them), and `isVal` whether the bound
expression is non-expansive.  A non-expansive binding quantifies everything `C` does not
fix; an expansive one quantifies nothing -- the value restriction. -/
def closeBinding (stx : Lean.Syntax) (name : String) (us envFV : Lean.NameSet)
    (isVal : Bool) (t : Ty 0) (topLevel : Bool := false) : Check n TyScheme := do
  -- What generalization would quantify.  Also what the value restriction refuses to,
  -- which is why it is computed either way.
  let generalized := Ty.generalize envFV t
  -- Generalizing an expression that allocates is unsound once `Ref` exists:
  -- `def r := builtin_alloc([])` at `∀ a. Ref<List<a>>` would let one use of `r` store
  -- `Int`s into the single underlying cell and another read them back as `String`s.
  --
  -- Unlike at a `let`, a top-level non-value's left-over variables cannot simply stay
  -- free: rule 87 lets no free type variable into the basis a top-level declaration
  -- produces, and nothing later could determine them -- each command elaborates alone.
  if topLevel && !isVal && !generalized.tyVars.isEmpty then
    throwErrorAt stx s!"Value restriction: the body of {name} is not a value, so \
      its type {generalized.prettyWeak} cannot be generalized.  Give {name} a type \
      annotation that fixes the remaining type variable(s), or make its body a \
      value (for instance by turning it into a function)."
  let scheme := if isVal then generalized else TyScheme.mono t
  -- Whatever generalization would have taken is now fixed-but-unknown, and the hovers
  -- inside this binding have to say so rather than showing it as quantified.
  unless isVal do markWeak t
  -- Rule 15's side condition `U ∩ tyvars(VE') = ∅`: a type variable the user wrote must
  -- come out quantified.  Left un-quantified it would escape as a fixed-but-unknown type,
  -- and the signature would silently mean something other than what it says.
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

-- ---- Inference (constraint generation) ----

def checkBannedLetName (stx : Lean.Syntax) (n : String) : Check m Unit := do
  match n with
  | "true" | "false" => throwErrorAt stx s!"Cannot redefine {n} here"
  | _ => pure ()

mutual
  -- Infer `e`'s type, recording a hover for it.
  partial def Exp.infer : Exp 0 m → Check m (Ty 0)
    | .mk stx x => do
      let ty ← ExpX.infer stx x
      -- A variable occurrence points at its binding; anything else has no target.
      let loc? ← match x with
        | .Var i => pure ((← read).varLocs.get i)
        | _ => pure none
      modify fun s => { s with stxMap := (stx, ty, loc?) :: s.stxMap }
      pure ty

  partial def ExpX.infer (stx : Lean.Syntax) : ExpX 0 m → Check m (Ty 0)
    | .Const (.Num _) => pure (.mk stx .Int)
    | .Const (.Bool _) => pure (.mk stx .Bool)
    | .Const (.String _) => pure (.mk stx .Str)
    | .Const .Unit => pure (.mk stx .Unit)
    | .Var i => do ((← read).varMap.get i).instantiate
    | .Lam _ oty e => do
      let argTy ← match oty with
        | none => freshTy stx
        | some t => normalizeTy t
      let bodyTy ← withVar (TyScheme.mono argTy) (← Check.locOf stx) (Exp.infer e)
      pure (.mk stx (.Arrow argTy bodyTy))
    | .App e1 e2 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      let r ← freshTy stx
      addConstraint stx t1 (.mk stx (.Arrow t2 r))
      pure r
    | .Let n oty e1 e2 => do
      checkBannedLetName stx n
      -- `let n : oty := e1 in e2` is the Definition's `let val n : oty = e1 in e2 end`
      -- (rules 4 and 15): a declaration, so `e1` is generalized right here.  The type
      -- variables this declaration scopes are rigid while `e1` is checked and quantified
      -- by the closure below; ones an enclosing declaration already scopes are not among
      -- them (4.6).
      let outerUs := (← read).tyVarScope
      let us := (Exp.letTyVars n oty e1).filter (fun nm => !outerUs.contains nm)
      let t1 ← withTyVarScope us do
        let t1 ← Exp.infer e1
        if let some t := oty then addConstraint stx t1 (← normalizeTy t)
        -- Closing over `t1` means knowing it, so solve here rather than at the end of
        -- the declaration.
        let _ ← solveAll
        applyCurSubst t1
      -- Read outside `withTyVarScope`: the closure is taken in the context `C` this
      -- declaration extends, and `us` is what it quantifies.
      let envFV ← envFVars
      let scheme ← closeBinding stx n us envFV (Exp.isValue (← read).valueCtx e1) t1
      withVar scheme (← Check.locOf stx) (Exp.infer e2)
    | .If e1 e2 e3 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      let t3 ← Exp.infer e3
      addConstraint stx t1 (.mk stx .Bool)
      addConstraint stx t2 t3
      pure t2
    | .Pair e1 e2 => do pure (.mk stx (.Prod (← Exp.infer e1) (← Exp.infer e2)))
    | .Fst e => do pure (← Exp.inferPair stx e).1
    | .Snd e => do pure (← Exp.inferPair stx e).2
    | .Alloc e => do pure (.mk stx (.Ref (← Exp.infer e)))
    | .Error e => do
      Exp.inferAgainst stx e (.mk stx .Str)
      freshTy stx
    | .Print e => do
      Exp.inferAgainst stx e (.mk stx .Str)
      pure (.mk stx .Unit)
    | .Rec _ e1 => do
      let r ← freshTy stx
      let res ← withVar (TyScheme.mono r) (← Check.locOf stx) (Exp.infer e1)
      addConstraint stx r res
      pure res
    | .Deref e => do
      let t ← Exp.infer e
      let a ← freshTy stx
      addConstraint stx t (.mk stx (.Ref a))
      pure a
    | .Assign e1 e2 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      addConstraint stx t1 (.mk stx (.Ref t2))
      pure (.mk stx .Unit)
    | .Try e1 e2 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      addConstraint stx t1 t2
      pure t1
    | .Op s es => do
      match (← read).opMap.get? s with
      | none => throwErrorAt stx s!"Unknown operator/constructor: {s}"
      | some sig => do
        let (argTys, outTy) ← sig.instantiate
        let argEs := es.toList
        if argEs.length ≠ argTys.length then
          throwErrorAt stx
            s!"Operator {s} expects {argTys.length} arguments but got {argEs.length}"
        for (a, t) in argEs.zip argTys do
          Exp.inferAgainst stx a t
        pure outTy
    | .Match e cases => do
      let scrutTy ← Exp.infer e
      let resTy ← freshTy stx
      Exp.inferCases cases scrutTy resTy stx []
      pure resTy
    | .Loc _ => throwError "Loc should not appear in source"

  -- Infer `e`'s type and require it to be `ty`.
  partial def Exp.inferAgainst (stx : Lean.Syntax) (e : Exp 0 m) (ty : Ty 0) : Check m Unit := do
    addConstraint stx (← Exp.infer e) ty

  -- The component types of `e`, which must be a pair.
  partial def Exp.inferPair (stx : Lean.Syntax) (e : Exp 0 m) : Check m (Ty 0 × Ty 0) := do
    let t ← Exp.infer e
    let a ← freshTy stx
    let b ← freshTy stx
    addConstraint stx t (.mk stx (.Prod a b))
    pure (a, b)

  -- `seen` accumulates the constructor names already matched (in reverse), used to reject
  -- duplicates and, once the arms run out, to check that every constructor is covered.
  partial def Exp.inferCases (cs : ExpMatchCases 0 m) (scrutTy resTy : Ty 0)
      (matchStx : Lean.Syntax) (seen : List String) : Check m Unit := do
    match cs with
    | .Nil =>
      match seen with
      | [] => throwErrorAt matchStx "Empty match: cannot determine the type being matched"
      | c :: _ =>
        let (tname, allCtors) ← ctorTypeInfo c matchStx
        let missing := allCtors.filter (fun c => !seen.contains c)
        unless missing.isEmpty do
          throwErrorAt matchStx
            s!"Non-exhaustive match on {tname}: missing constructor(s) {", ".intercalate missing}"
    -- A catch-all makes the match exhaustive; its body binds no variables.
    | .Wild body => Exp.inferAgainst matchStx body resTy
    | .Cons cname xs body rest => do
      match (← read).opMap.get? cname with
      | none => throwErrorAt matchStx s!"Unknown constructor in match: {cname}"
      | some sig => do
        if seen.contains cname then
          throwErrorAt matchStx s!"Duplicate constructor in match: {cname}"
        let (argTys, outTy) ← sig.instantiate
        if h : argTys.length = xs.length then
          addConstraint matchStx scrutTy outTy
          let body' : Exp 0 (m + argTys.length) := body.cast (by rw [h])
          -- Pattern variables are indexed with the first at index 0 (`casesFromSurface`
          -- binds `xs ++ vars`).  `withVar` pushes to index 0, so the argument types go
          -- in reversed, putting `argTys[i]` at index `i`.
          let bodyTy ← Exp.inferWithVars argTys.reverse (← Check.locOf matchStx)
            (body'.cast (by simp))
          addConstraint matchStx bodyTy resTy
          Exp.inferCases rest scrutTy resTy matchStx (cname :: seen)
        else
          throwErrorAt matchStx
            s!"Constructor {cname} expects {argTys.length} arguments but pattern has {xs.length}"

  -- Bind each type in `argTys` monomorphically, then infer `body`.
  partial def Exp.inferWithVars {m : Nat} :
      (argTys : List (Ty 0)) → Option DeclarationLocation → Exp 0 (m + argTys.length) →
      Check m (Ty 0)
    | [], _, body => Exp.infer (body.cast (by simp))
    | t :: ts, loc?, body =>
        withVar (TyScheme.mono t) loc? <|
          Exp.inferWithVars (m := m + 1) ts loc? (body.cast (by simp; omega))
end

-- ---- Declaration checking ----

-- Attach the hovers buffered for this declaration, now that its constraints are solved.
-- `stxMap` holds each expression paired with the type inference gave it; the solution is
-- applied here, and the variables that outlive it are named for the whole declaration at
-- once (`hoverSubst`) so that its hovers agree with each other and with its signature.
def addStxMapHovers (sbst : NameMap (TyX 0)) : Check n Unit := do
  let entries ← (← get).stxMap.mapM fun (stx, ty, loc?) => do
    pure (stx, ← applySubstTy sbst ty, loc?)
  -- `stxMap` is built by consing each expression after its subexpressions, so it runs
  -- outermost-first: the declaration's own type is what names `a`, `b`, ... .
  let m := hoverSubst ((← envFVars).union (← weakFVars)) (entries.map (·.2.1))
  for (stx, ty, loc?) in entries do
    addHoverInfo stx (Ty.pretty (Ty.substFVarsP' m ty)) loc?
  modify fun s => { s with stxMap := [] }

-- Run `k`, solve whatever constraints it leaves buffered, and attach the hovers it
-- recorded.  Inner `let`s have solved their own already; those solutions are in
-- `TcState.subst`, which is what the hovers are rendered with.
--
-- Must be called *inside* the declaration's `withTyVarScope`: this solve is the only one
-- a declaration with no inner `let` ever performs, so outside the scope its explicit type
-- variables would never be checked for rigidity at all.
def withSolveAll (k : Check n α) : Check n α := do
  let res ← k
  addStxMapHovers (← solveAll)
  pure res

-- `#eval e`, `#test e1 === e2`, `#test_error e` and `#check e` each stand for a
-- declaration of the Definition's `val it = e` shape, so each scopes the explicit type
-- variables written in its expressions, exactly as a `def` does.  The scope wraps the
-- solve, not the other way round; see `withSolveAll`.
def checkAnonDecl (us : Lean.NameSet) (body : Check n α) : Check n α :=
  withTyVarScope us (withSolveAll body)

-- Infer `e` as one of those anonymous declarations: like `closeBinding`, an expansive one
-- generalizes nothing, so its leftover variables are fixed rather than quantified and its
-- hovers have to read that way -- `#check builtin_alloc([])` reports `Ref<List<_a>>`, and
-- hovering the expression it reports on says the same.
def inferAnonBody (e : Exp 0 m) : Check m (Ty 0) := do
  let t ← Exp.infer e
  unless Exp.isValue (← read).valueCtx e do markWeak t
  pure t

partial def Decl.check : {n m : Nat} → (d : Decl n m) → Check m α → Check n α
  | _, _, .mk _ .DeclNil, k => k
  | _, _, .mk _ (.DeclConcat d1 d2), k => Decl.check d1 (Decl.check d2 k)
  | _, _, .mk dstx (.DeclDef name tvars oty e), k => do
    if tvars.hasDup then throwErrorAt dstx s!"Duplicate type variable in declaration"
    checkDefNameFresh dstx name
    -- Open the declared variables with FVars keeping the user-written names, so hovers
    -- inside the body show e.g. `k`/`v`.
    let (σ, skolems) ← namedSubst tvars
    let e' := Exp.substTy σ e
    let oty' : Option (Ty 0) := oty.map (Ty.subst σ)
    -- The `tyvarseq` of rule 15: what this declaration declares, plus what is implicitly
    -- scoped at it -- written in an annotation inside the body that no inner `let` scopes
    -- first (4.6).  Rigid while the body is checked, quantified by the closure after.
    let us := skolems.foldl (·.insert ·) ((annFVars oty').union (Exp.unguardedTyVars e'))
    -- The scope wraps the solve: `us` has to be rigid when these constraints are
    -- discharged, not merely while they are generated (`withSolveAll`).
    let inferredTy ← withTyVarScope us <| withSolveAll do
      let inferredTy ← Exp.infer e'
      if let some t := oty' then addConstraint dstx inferredTy (← normalizeTy t)
      pure inferredTy
    let finalTy ← applyCurSubst inferredTy
    -- Read outside `withTyVarScope`: the closure quantifies `us`, so `C` excludes it.
    let envFV ← envFVars
    let isVal := Exp.isValue (← read).valueCtx e'
    let scheme ← closeBinding dstx name us envFV isVal finalTy (topLevel := true)
    addHoverInfo dstx s!"{scheme.pretty}"
    pruneSubst
    withDefName dstx name scheme k
  | _, _, .mk _ (.DeclEval e), k
  | _, _, .mk _ (.DeclTestError e _), k => do
    let _ ← checkAnonDecl (Exp.unguardedTyVars e) (inferAnonBody e)
    pruneSubst
    k
  | _, _, .mk dstx (.DeclTest e1 e2), k => do
    let us := (Exp.unguardedTyVars e1).union (Exp.unguardedTyVars e2)
    let _ ← checkAnonDecl us do
      let t1 ← inferAnonBody e1
      let t2 ← inferAnonBody e2
      addConstraint dstx t1 t2
    pruneSubst
    k
  | _, _, .mk stx (.DeclCheck e), k => do
    let res ← checkAnonDecl (Exp.unguardedTyVars e) (inferAnonBody e)
    let scheme := Ty.generalize (← envFVars) (← applyCurSubst res)
    -- `#check` binds nothing, so an un-generalizable type is not an error here; it just
    -- reports the weak variables as such (see `DeclDef` above).
    logInfoAt stx (if Exp.isValue (← read).valueCtx e then scheme.pretty else scheme.prettyWeak)
    pruneSubst
    k
  | _, _, .mk dstx (.DeclTypeAlias tname alias), k => do
    checkTyNameFresh dstx tname
    if alias.tyVars.hasDup then
      throwErrorAt dstx s!"Type alias cannot have duplicate type variables"
    let _ ← normalizeTy alias.ty
    withReader (fun env => { env with tyMap := env.tyMap.insert tname (.Alias alias) }) k
  | _, _, .mk dstx (.DeclInductive tname tvars cs), k => do
    checkTyNameFresh dstx tname
    if tvars.hasDup then
      throwErrorAt dstx s!"Type definition cannot have duplicate type variables"
    -- Constructor names are global: reject a repeat within this declaration or a clash
    -- with an existing operator/constructor, so no `opMap` entry is silently overwritten.
    let env ← read
    let mut declared : List String := []
    for (cname, _) in cs do
      if declared.contains cname then
        throwErrorAt dstx s!"Error when defining {tname}: Constructor {cname} is defined twice in type {tname}"
      if env.opMap.contains cname then
        throwErrorAt dstx s!"Error when defining {tname}: Constructor {cname} is already defined"
      declared := cname :: declared
    -- One FVar per type parameter, shared across all constructors so that a variable used
    -- in an argument type and in the output type is the same one.
    let (σ, names) ← freshSubst tvars
    let outTy : Ty 0 := .mk .missing (.TApp tname (names.map fun n => .mk .missing (.FVar n)))
    let sigs : List (String × OpSig) := cs.map fun (cname, args) =>
      (cname, { tyVars := names, argTys := args.map fun (_, ty) => Ty.subst σ ty, outTy })
    withReader (fun env =>
      { env with
        opMap := sigs.foldl (fun m (cname, sig) => m.insert cname sig) env.opMap,
        tyMap := env.tyMap.insert tname (.Inductive tvars.length (cs.map (·.1))) }) k
