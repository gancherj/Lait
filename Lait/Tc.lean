import Lait.Syntax
import Lait.Utils
import Lean

open Lean Elab Command

/-!
# The Lait type checker

Hindley-Milner inference, in the order the file is written:

* **Types.** A `Ty` is either a concrete shape, a *bound* variable (`Var`, only inside a
  `TyScheme`), or a *free* variable (`FVar`).  A free variable is either one the user
  wrote (`a`) or one the solver invented as a placeholder (`_tcFresh.7`).
* **Normalizing.** `normalizeTy` expands type aliases and checks arities.  Every `Ty` the
  checker handles has been through it.
* **Inferring.** `Exp.infer` walks an expression, invents a placeholder wherever it does
  not yet know a type, and calls `unify` to say which types must be equal.
* **Solving.** `unify` records its answers in `TcState.subst`, one entry per solved
  variable.  `Ty.resolve` reads them back.
* **Generalizing.** At a `def` or a `let`, `closeBinding` turns the resolved type into a
  `TyScheme` by quantifying the variables the surrounding context does not fix.
* **Showing.** Before any type reaches the user, `displaySubst` renames the solver's
  placeholders to `a`, `b`, `c`, ... .
-/

-- Signature of a builtin operator or a data constructor.
structure OpSig where
  tyVars : List Lean.Name
  argTys : List (Ty 0)
  outTy : Ty 0

inductive TyVal where
  -- Arity, plus the constructor names in declaration order (for `match` exhaustiveness).
  | Inductive : Nat -> List String -> TyVal
  | Alias : TyScheme -> TyVal
  -- A primitive type (`Int`, `Bool`, ...); the entry exists only to reserve the name.
  | Builtin : TyVal

-- What the checker knows about one variable in scope.
structure VarInfo where
  scheme : TyScheme
  -- Where "go to definition" jumps; `none` when the binding has no source position.
  loc? : Option DeclarationLocation
  -- Is this a data constructor?  Applying one is non-expansive; see `Exp.isValue`.
  isCtor : Bool

structure TcEnv (n : Nat) where
  opMap : Std.TreeMap String OpSig
  tyMap : Std.TreeMap String TyVal
  curSyntax : Lean.Syntax
  -- In-scope variables, innermost (de Bruijn index 0) first.  A length-indexed vector
  -- rather than `Fin n → VarInfo`: building the latter from nested `Fin.cases` closures
  -- loses sharing, making deep lookups exponential.
  vars : Vec n VarInfo
  -- Where each top-level name spliced in by `#include` was defined.  Its syntax carries no
  -- positions of its own, so `#include` records this.
  defLocs : Std.TreeMap String DeclarationLocation
  -- Every type variable free in an in-scope scheme, so `envFVars` is O(1) to start from.
  frozen : Lean.NameSet
  -- Top-level `def` names so far.  A top-level definition may not shadow one; `let`/`fun`/
  -- `match` binders go through `withVar` and shadow freely.
  defNames : Std.TreeSet String
  -- Type variables the user wrote at an enclosing declaration.  They are *rigid*: the
  -- caller of that declaration chooses them, so the body may not solve for them.
  tyVarScope : Lean.NameSet

-- Does `s` name a data constructor, as opposed to a primitive operator (`+`, `==`, ...)?
def TcEnv.isCtorName (env : TcEnv n) (s : String) : Bool :=
  match env.opMap.get? s with
  | some { outTy := .mk _ (.TApp tname _), .. } =>
    match env.tyMap.get? tname with
    | some (.Inductive ..) => true
    | _ => false
  | _ => false

structure TcState where
  -- What unification has worked out: `a ↦ t` means "the variable `a` turned out to be `t`".
  -- Read it with `Ty.resolve`, which follows chains.
  subst : Lean.NameMap (TyX 0) := {}
  freshCounter : Nat := 0
  -- Hovers to attach once the declaration is finished: an expression's syntax, its type,
  -- and -- for a variable occurrence -- the binding it resolves to.
  stxMap : List (Lean.Syntax × Ty 0 × Option DeclarationLocation) := []

abbrev Check n := ReaderT (TcEnv n) (StateT TcState TermElabM)

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

-- Did the solver invent this name, or did the user write it?  The two are treated
-- differently everywhere: unification prefers to solve the solver's own, and printing
-- renames only the solver's own.
def Lean.Name.isSolverVar : Lean.Name → Bool
  | .num (.str .anonymous "_tcFresh") _ => true
  | _ => false

-- ---- Free variables ----

-- A type's free variables, in the order they print, with repeats.  Everything else about a
-- type's variables is derived from this, so every listing a reader sees is in *their*
-- order, not the order the solver happened to allocate them in.
mutual
partial def Ty.fvars : Ty n → List Lean.Name
  | .mk _ t => TyX.fvars t

partial def TyX.fvars : TyX n → List Lean.Name
  | .FVar a => [a]
  | .Arrow t1 t2 | .Prod t1 t2 => Ty.fvars t1 ++ Ty.fvars t2
  | .Ref t => Ty.fvars t
  | .TApp _ ts => (ts.attach.map fun ⟨x, _⟩ => Ty.fvars x).flatten
  | .Var _ | .Int | .Bool | .Str | .Unit => []
end

def Ty.fvarSet (t : Ty n) : Lean.NameSet := t.fvars.foldl (·.insert ·) {}
def TyX.fvarSet (t : TyX n) : Lean.NameSet := t.fvars.foldl (·.insert ·) {}
def TyX.occurs (a : Lean.Name) (t : TyX n) : _root_.Bool := t.fvars.contains a

def annFVars (oty : Option (Ty n)) : Lean.NameSet := (oty.map Ty.fvarSet).getD {}

-- ---- Substituting for free variables ----

-- Replace the variables `m` mentions; leave the others alone.
mutual
partial def Ty.substFVars (m : Lean.NameMap (TyX 0)) : Ty 0 → Ty 0
  | .mk stx x => .mk stx (TyX.substFVars m x)

partial def TyX.substFVars (m : Lean.NameMap (TyX 0)) : TyX 0 → TyX 0
  | .FVar a => (m.get? a).getD (.FVar a)
  | .Arrow t1 t2 => .Arrow (Ty.substFVars m t1) (Ty.substFVars m t2)
  | .Prod t1 t2 => .Prod (Ty.substFVars m t1) (Ty.substFVars m t2)
  | .Ref t => .Ref (Ty.substFVars m t)
  | .TApp s ts => .TApp s (ts.attach.map fun ⟨x, _⟩ => Ty.substFVars m x)
  | .Int => .Int
  | .Unit => .Unit
  | .Bool => .Bool
  | .Str => .Str
  | .Var i => .Var i
end

-- ---- Normalizing ----

-- Expand type aliases and check the arity of every type application.  Every `Ty` the rest
-- of the checker handles has been through this: it runs wherever a user-written type
-- enters, which is a `fun` annotation, a `let` annotation, a `def` signature, and
-- `OpSig.instantiate`.
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

-- ---- Reading the substitution ----

-- Replace every solved variable by what it was solved to, following chains.  A type is
-- built before the unifications that determine it have happened, so anything we want to
-- *look at* -- print it, generalize it -- has to be resolved first.
mutual
partial def Ty.resolve : Ty 0 → Check n (Ty 0)
  | .mk stx t => do pure (.mk stx (← TyX.resolve t))

partial def TyX.resolve : TyX 0 → Check n (TyX 0)
  | .FVar a => do
    match (← get).subst.get? a with
    | some t => TyX.resolve t
    | none => pure (.FVar a)
  | .Arrow t1 t2 => do pure (.Arrow (← Ty.resolve t1) (← Ty.resolve t2))
  | .Prod t1 t2 => do pure (.Prod (← Ty.resolve t1) (← Ty.resolve t2))
  | .Ref t => do pure (.Ref (← Ty.resolve t))
  | .TApp s ts => do pure (.TApp s (← ts.attach.mapM fun ⟨x, _⟩ => Ty.resolve x))
  | .Int => pure .Int
  | .Bool => pure .Bool
  | .Str => pure .Str
  | .Unit => pure .Unit
  | .Var i => pure (.Var i)
end

-- ---- Pretty-printing ----

-- Print with only the parentheses the structure needs, matching the grammar `lait_ty`
-- parses: `->` and `*` are right-associative and `*` binds tighter, so `a * b -> c -> d`
-- reads as `(a * b) -> (c -> d)`.  `prec` is the level the context requires -- 0 anywhere,
-- 1 tighter than `->`, 2 atomic -- and a type is parenthesized when its own level is lower.
mutual
partial def Ty.prettyPrec (prec : Nat) : Ty 0 -> String
  | .mk _ t => TyX.prettyPrec prec t

partial def TyX.prettyPrec (prec : Nat) : TyX 0 -> String
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

-- Render a scheme, calling each quantified variable what the scheme calls it.  There is no
-- `∀`: a scheme is written just like the type it generalizes, as SML writes it
-- (`val id = fn : 'a -> 'a`), and it is the *names* that say which are quantified.
def TyScheme.pretty (sch : TyScheme) : String :=
  Ty.pretty (sch.ty.subst fun i => .mk .missing (.FVar (Name.mkSimple (sch.tyVars.get i))))

-- ---- Naming type variables ----
--
-- A solver name (`_tcFresh.137`) says nothing to a reader, and its number shifts whenever
-- anything elaborated earlier changes, so a type is renamed before it is shown.  One rule
-- serves errors, hovers and schemes alike: the solver's variables become `a`, `b`, `c`,
-- ... in the order they first appear, and a variable the user wrote keeps its own name.

-- Enough letters that no real type runs out.
def tyVarLetters : List Lean.Name :=
  let alphabet := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m",
                   "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"]
  (["", "1", "2"].flatMap fun sfx => alphabet.map (· ++ sfx)).map Name.mkSimple

-- Hand out `supply`, in order, to the solver's variables among `vars`.
def assignNames : List Lean.Name -> List Lean.Name -> List (Lean.Name × Lean.Name)
  | [], _ => []
  | v :: vs, supply =>
    if v.isSolverVar then
      match supply with
      | new :: rest => (v, new) :: assignNames vs rest
      -- Out of letters, which no real type manages; keep the solver's name.
      | [] => (v, v) :: assignNames vs []
    else (v, v) :: assignNames vs supply

-- What to show each of `vars` as.  The generated names skip every name the user wrote, so
-- `def f (x : a) := fun y => (x, y)` shows the user's `a` and calls `y`'s type `b`.
def displayNames (vars : List Lean.Name) : List (Lean.Name × Lean.Name) :=
  let taken := vars.filter (!·.isSolverVar)
  assignNames vars (tyVarLetters.filter (!taken.contains ·))

-- The renaming to apply before printing `ts`.  One map covers all of `ts` at once, so a
-- variable shared by several of them reads the same in each.
def displaySubst (ts : List (TyX 0)) : Lean.NameMap (TyX 0) :=
  (displayNames (ts.flatMap TyX.fvars).eraseDups).foldl
    (fun m (old, new) => m.insert old (.FVar new)) (Lean.mkNameMap (TyX 0))

-- Render the two types of a unification failure, naming their variables together:
-- `Cannot unify List<a> with b -> Int`, never `_tcFresh.140`/`_tcFresh.142`.
def prettyPair (t1 t2 : TyX 0) : String × String :=
  let m := displaySubst [t1, t2]
  (TyX.pretty (TyX.substFVars m t1), TyX.pretty (TyX.substFVars m t2))

-- ---- Extending the environment ----

def withVar (scheme : TyScheme) (loc? : Option DeclarationLocation)
    (k : Check (n + 1) α) (isCtor : Bool := false) : Check n α := fun env =>
  -- `TcEnv n` and `TcEnv (n + 1)` are different types, so the fields are copied out rather
  -- than updated with `{ env with .. }`.
  k {
    opMap := env.opMap,
    tyMap := env.tyMap,
    curSyntax := env.curSyntax,
    defLocs := env.defLocs,
    defNames := env.defNames,
    tyVarScope := env.tyVarScope,
    frozen := env.frozen.union (Ty.fvarSet scheme.ty),
    vars := env.vars.cons { scheme, loc?, isCtor }
  }

-- Bring the type variables `us` into scope as rigid ones.
def withTyVarScope (us : Lean.NameSet) (k : Check n α) : Check n α :=
  withReader (fun env => { env with tyVarScope := env.tyVarScope.union us }) k

-- The "go to definition" target of a binding introduced by `stx`.
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

-- `type` may not re-declare an earlier or a primitive type.
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

-- Instantiate with fresh solver variables.
def freshSubst (xs : List String) : Check n ((Fin xs.length → Ty 0) × List Lean.Name) :=
  openTyVars (fun _ => freshTyName) xs

-- Instantiate keeping the user-written names, so hovers inside a `def` with an explicit
-- signature show `k`/`v` rather than solver names.
def namedSubst (xs : List String) : Check n ((Fin xs.length → Ty 0) × List Lean.Name) :=
  openTyVars (fun x => pure (Lean.Name.mkSimple x)) xs

def TyScheme.instantiate (sch : TyScheme) : Check n (Ty 0) := do
  let (σ, _) ← freshSubst sch.tyVars
  pure (Ty.subst σ sch.ty)

-- Constructor signatures come straight from a user-written `type`, so this is where their
-- aliases get expanded -- normalizing at the `type` itself would fail on a mutually
-- recursive group, whose siblings are not in `tyMap` yet.
def OpSig.instantiate (sig : OpSig) : Check n (List (Ty 0) × Ty 0) := do
  let mut m : Lean.NameMap (TyX 0) := {}
  for nm in sig.tyVars do
    m := m.insert nm (.FVar (← freshTyName))
  let argTys ← sig.argTys.mapM fun t => normalizeTy (Ty.substFVars m t)
  pure (argTys, ← normalizeTy (Ty.substFVars m sig.outTy))

-- ---- Unification ----

def cannotUnify (stx : Lean.Syntax) (t1 t2 : TyX 0) : Check n α :=
  let (s1, s2) := prettyPair t1 t2
  throwErrorAt stx s!"Cannot unify {s1} with {s2}"

-- Record that the variable `a` is the type `t`.  `t` must already be resolved, so that the
-- occurs check sees everything.  Both error paths name `a` alongside `t`, so that when it
-- occurs there the two read the same.
def solveVar (stx : Lean.Syntax) (a : Lean.Name) (t : TyX 0) : Check n Unit := do
  if (← read).tyVarScope.contains a then
    let (as, ts) := prettyPair (.FVar a) t
    throwErrorAt stx s!"Cannot make the type variable {as} equal to {ts}: \
      {as} is chosen by whoever uses this definition, so its body cannot require \
      it to be {ts}"
  if t.occurs a then
    let (as, ts) := prettyPair (.FVar a) t
    throwErrorAt stx s!"Occurs check failed: {as} occurs in {ts}"
  modify fun s => { s with subst := s.subst.insert a t }

-- Require `t1` and `t2` to be the same type, reporting at `stx` if they cannot be.
partial def unify (stx : Lean.Syntax) (t1 t2 : Ty 0) : Check n Unit := do
  let u1 ← TyX.resolve t1.get
  let u2 ← TyX.resolve t2.get
  match u1, u2 with
  | .FVar a, .FVar b =>
    if a == b then pure ()
    else
      let rigid := (← read).tyVarScope
      if rigid.contains a && rigid.contains b then
        throwErrorAt stx s!"Cannot make the type variables {a} and {b} equal: each is \
          chosen separately by whoever uses this definition"
      -- Never solve a rigid variable, and among the rest prefer the solver's own, so that
      -- a name the user wrote survives into errors and hovers.
      else if rigid.contains a then solveVar stx b (.FVar a)
      else if rigid.contains b then solveVar stx a (.FVar b)
      else if a.isSolverVar then solveVar stx a (.FVar b)
      else solveVar stx b (.FVar a)
  | .FVar a, t | t, .FVar a => solveVar stx a t
  | .Arrow a1 b1, .Arrow a2 b2
  | .Prod a1 b1, .Prod a2 b2 => do unify stx a1 a2; unify stx b1 b2
  | .Ref a, .Ref b => unify stx a b
  | .TApp s1 ts1, .TApp s2 ts2 =>
    if s1 == s2 && ts1.length == ts2.length then
      (ts1.zip ts2).forM fun (a, b) => unify stx a b
    else cannotUnify stx (.TApp s1 ts1) (.TApp s2 ts2)
  | .Int, .Int | .Bool, .Bool | .Str, .Str | .Unit, .Unit => pure ()
  | v1, v2 => cannotUnify stx v1 v2

-- The type variables generalization must leave alone: those free in an in-scope binding's
-- type, and the rigid ones an enclosing declaration scopes.
def envFVars : Check n Lean.NameSet := do
  let env ← read
  -- `frozen` records each binding's variables as of when it was pushed, so one solved
  -- since is no longer free in the environment -- but the variables of what it became are.
  let resolved ← env.frozen.toList.mapM fun nm => do
    pure (TyX.fvarSet (← TyX.resolve (.FVar nm)))
  pure (resolved.foldl (·.union ·) env.tyVarScope)

-- ---- Initial environment ----

def initTcOpMap : Std.TreeMap String OpSig :=
  let int : Ty 0 := .mk .missing .Int
  let bool : Ty 0 := .mk .missing .Bool
  let str : Ty 0 := .mk .missing .Str
  let mono (argTys : List (Ty 0)) (outTy : Ty 0) : OpSig := { tyVars := [], argTys, outTy }
  let eqTy : Ty 0 := .mk .missing (.FVar `_laitEqTy)
  let anyTy : Ty 0 := .mk .missing (.FVar `_laitAnyTy)
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
    , ("toString", { tyVars := [`_laitAnyTy], argTys := [anyTy], outTy := str })
    ]

-- The primitive types.  Listing them here keeps them out of reach of `type` declarations.
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

-- ---- Where a user-written type variable is scoped ----
--
-- A type variable belongs to the innermost declaration -- `def` or `let` -- in which it
-- occurs *unguarded*, meaning not inside a smaller declaration.  It is rigid while that
-- declaration's body is checked and quantified by its closure.  So this collects every
-- `fun` annotation and descends into a `let`'s body, but not into the `let`'s own bound
-- expression or annotation.

-- A `let` a surface pass synthesized (`elabDefMutual`'s return-type pin) is no declaration
-- of the user's, so it scopes nothing.  A `$` cannot occur in a source name.
def isSyntheticBinder (x : String) : Bool := x.startsWith "$"

mutual
partial def Exp.unguardedTyVars : Exp n m → Lean.NameSet
  | .mk _ x => ExpX.unguardedTyVars x

partial def ExpX.unguardedTyVars : ExpX n m → Lean.NameSet
  | .Lam _ oty e => (annFVars oty).union (Exp.unguardedTyVars e)
  -- A synthetic `let` scopes nothing, so its annotation and bound expression fall to the
  -- enclosing declaration -- which is what puts the return type of a `def` in an `and`
  -- group into that `def`'s scope.
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

-- What `let x : oty := e1` scopes, before removing what an enclosing declaration already
-- scopes.
def Exp.letTyVars (x : String) (oty : Option (Ty n)) (e1 : Exp n m) : Lean.NameSet :=
  if isSyntheticBinder x then {}
  else (annFVars oty).union (Exp.unguardedTyVars e1)

-- ---- The value restriction ----

-- What a value test needs from the environment: which `Op` names are data constructors
-- rather than primitives like `+`, and which in-scope variables are constructor functions.
structure ValueCtx (m : Nat) where
  isCtor : String → Bool
  isCtorVar : Fin m → Bool

-- Under a binder the new variable, at index 0, is not a constructor.
def ValueCtx.under (c : ValueCtx m) : ValueCtx (m + 1) :=
  { isCtor := c.isCtor, isCtorVar := Fin.cases false c.isCtorVar }

def TcEnv.valueCtx (env : TcEnv n) : ValueCtx n :=
  { isCtor := env.isCtorName, isCtorVar := fun i => (env.vars.get i).isCtor }

mutual
  -- Is `e` a syntactic value ("non-expansive")?  Evaluating one allocates no reference
  -- cells and has no other effect, which is what makes generalizing it sound: see
  -- `closeBinding`.
  def Exp.isValue (c : ValueCtx m) : Exp n m → Bool
    | .mk _ x => ExpX.isValue c x

  def ExpX.isValue (c : ValueCtx m) : ExpX n m → Bool
    | .Const _ | .Var _ | .Lam .. | .Loc _ => true
    -- `rec x => e` builds a closure without running `e`, but a projection below may force
    -- it later, so `e` must be non-expansive too.
    | .Rec _ e => Exp.isValue c.under e
    | .Pair e1 e2 => Exp.isValue c e1 && Exp.isValue c e2
    -- Projecting out of a value neither allocates nor has an effect.  Not values in SML,
    -- but they are how `elabDefMutual` pulls each function out of its recursive bundle --
    -- ruling them out would make every `and` group monomorphic.
    | .Fst e | .Snd e => Exp.isValue c e
    | .Let _ _ e1 e2 => Exp.isValue c e1 && Exp.isValue c.under e2
    | .Op s es => c.isCtor s && ExpList.isValue c es
    -- A constructor application only builds the constructed value (or, if partial, a
    -- closure).  Any other application may run arbitrary code.
    | .App e1 e2 => Exp.isCtorApp c e1 && Exp.isValue c e2
    | .If .. | .Error _ | .Print _ | .Match .. | .Alloc _ | .Deref _
    | .Assign .. | .Try .. => false

  -- Is `e` a constructor applied to (possibly zero) values?  Surface `Cons h t` reaches
  -- the type checker as nested `App`s of the generated `def Cons`, not as an `Op`, so this
  -- is what makes `def empty := Map []` generalize.
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

-- Close `t` over the variables the context does not fix, and give each of them the name it
-- will print under.  Quantified in order of first appearance, since that is the order
-- `TyScheme.pretty` names them in: `a` is the first variable the reader meets.
def Ty.generalize (frozen : Lean.NameSet) (t : Ty 0) : TyScheme :=
  let vars := t.fvars.eraseDups
  -- Over *all* of `t`'s variables, not just the quantified ones, so a generated name also
  -- avoids colliding with a user-written variable the context fixes.
  let shown := displayNames vars
  let gens := vars.filter (fun n => !frozen.contains n)
  let closed : Ty gens.length := closeMany gens t
  let tyVars : List String := gens.map fun g => (List.lookup g shown).getD g |>.toString
  have hlen : tyVars.length = gens.length := by simp [tyVars]
  { tyVars := tyVars, ty := hlen ▸ closed }

/-- Turn one binding's inferred type into the scheme it is bound at.

`t` is the resolved type, `envFV` the variables the surrounding context fixes, `us` the
type variables the user wrote at this declaration, and `isVal` whether the bound expression
is non-expansive.  A non-expansive binding quantifies everything the context does not fix;
an expansive one quantifies nothing -- the value restriction. -/
def closeBinding (stx : Lean.Syntax) (name : String) (us envFV : Lean.NameSet)
    (isVal : Bool) (t : Ty 0) (topLevel : Bool := false) : Check n TyScheme := do
  -- What generalization would quantify.  Also what the value restriction refuses to.
  let generalized := Ty.generalize envFV t
  -- Generalizing an expression that allocates is unsound once `Ref` exists:
  -- `def r := builtin_alloc([])` at `∀ a. Ref<List<a>>` would let one use of `r` store
  -- `Int`s into the single underlying cell and another read them back as `String`s.
  --
  -- Unlike at a `let`, a top-level non-value's left-over variables cannot simply stay
  -- free: nothing later could determine them, since each command elaborates alone.
  if topLevel && !isVal && !generalized.tyVars.isEmpty then
    throwErrorAt stx s!"Value restriction: the body of {name} is not a value, so \
      its type {generalized.pretty} cannot be generalized.  Give {name} a type \
      annotation that fixes the remaining type variable(s), or make its body a \
      value (for instance by turning it into a function)."
  let scheme := if isVal then generalized else TyScheme.mono t
  -- A type variable the user wrote must come out quantified.  Left un-quantified it would
  -- escape as a fixed-but-unknown type, and the signature would silently mean something
  -- other than what it says.
  unless us.isEmpty do
    let escaped := scheme.ty.fvars.eraseDups.filter us.contains
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

-- ---- Inference ----

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
        | .Var i => pure ((← read).vars.get i).loc?
        | _ => pure none
      modify fun s => { s with stxMap := (stx, ty, loc?) :: s.stxMap }
      pure ty

  partial def ExpX.infer (stx : Lean.Syntax) : ExpX 0 m → Check m (Ty 0)
    | .Const (.Num _) => pure (.mk stx .Int)
    | .Const (.Bool _) => pure (.mk stx .Bool)
    | .Const (.String _) => pure (.mk stx .Str)
    | .Const .Unit => pure (.mk stx .Unit)
    | .Var i => do ((← read).vars.get i).scheme.instantiate
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
      unify stx t1 (.mk stx (.Arrow t2 r))
      pure r
    | .Let n oty e1 e2 => do
      checkBannedLetName stx n
      -- A `let` is a declaration, so `e1` is generalized right here.  The type variables
      -- this declaration scopes are rigid while `e1` is checked and quantified by the
      -- closure below; ones an enclosing declaration already scopes are not among them.
      let outerUs := (← read).tyVarScope
      let us := (Exp.letTyVars n oty e1).filter (fun nm => !outerUs.contains nm)
      let t1 ← withTyVarScope us do
        let t1 ← Exp.infer e1
        if let some t := oty then unify stx t1 (← normalizeTy t)
        -- Closing over `t1` means knowing it.
        Ty.resolve t1
      -- Read outside `withTyVarScope`: the closure is taken in the context this
      -- declaration extends, and `us` is what it quantifies.
      let envFV ← envFVars
      let scheme ← closeBinding stx n us envFV (Exp.isValue (← read).valueCtx e1) t1
      withVar scheme (← Check.locOf stx) (Exp.infer e2)
    | .If e1 e2 e3 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      let t3 ← Exp.infer e3
      unify stx t1 (.mk stx .Bool)
      unify stx t2 t3
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
      unify stx r res
      pure res
    | .Deref e => do
      let t ← Exp.infer e
      let a ← freshTy stx
      unify stx t (.mk stx (.Ref a))
      pure a
    | .Assign e1 e2 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      unify stx t1 (.mk stx (.Ref t2))
      pure (.mk stx .Unit)
    | .Try e1 e2 => do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      unify stx t1 t2
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
    unify stx (← Exp.infer e) ty

  -- The component types of `e`, which must be a pair.
  partial def Exp.inferPair (stx : Lean.Syntax) (e : Exp 0 m) : Check m (Ty 0 × Ty 0) := do
    let t ← Exp.infer e
    let a ← freshTy stx
    let b ← freshTy stx
    unify stx t (.mk stx (.Prod a b))
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
    | .Wild body => do unify matchStx resTy (← Exp.infer body)
    | .Cons cname xs body rest => do
      match (← read).opMap.get? cname with
      | none => throwErrorAt matchStx s!"Unknown constructor in match: {cname}"
      | some sig => do
        if seen.contains cname then
          throwErrorAt matchStx s!"Duplicate constructor in match: {cname}"
        let (argTys, outTy) ← sig.instantiate
        if h : argTys.length = xs.length then
          unify matchStx scrutTy outTy
          let body' : Exp 0 (m + argTys.length) := body.cast (by rw [h])
          -- Pattern variables are indexed with the first at index 0.  `withVar` pushes to
          -- index 0, so the argument types go in reversed, putting `argTys[i]` at index `i`.
          let bodyTy ← Exp.inferWithVars argTys.reverse (← Check.locOf matchStx)
            (body'.cast (by simp))
          unify matchStx resTy bodyTy
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

-- Attach the hovers buffered for this declaration.  `stxMap` holds each expression paired
-- with the type inference gave it; the types are resolved here, and the whole declaration
-- is named at once so that its hovers agree with each other and with its signature.
def attachHovers : Check n Unit := do
  let entries ← (← get).stxMap.mapM fun (stx, ty, loc?) => do
    pure (stx, ← Ty.resolve ty, loc?)
  -- `stxMap` is built by consing each expression after its subexpressions, so it runs
  -- outermost-first: the declaration's own type is what names `a`, `b`, ... .
  let m := displaySubst (entries.map (·.2.1.get))
  for (stx, ty, loc?) in entries do
    addHoverInfo stx (Ty.pretty (Ty.substFVars m ty)) loc?
  modify fun s => { s with stxMap := [] }

def withHovers (k : Check n α) : Check n α := do
  let res ← k
  attachHovers
  pure res

-- Nothing can refer to a finished declaration's type variables again: the only thing it
-- leaves behind is its scheme, and `closeBinding` rejects a top-level scheme that still
-- has a free variable in it.
def finishDecl : Check n Unit :=
  modify fun s => { s with subst := {}, stxMap := [] }

-- `#eval e`, `#test e1 === e2`, `#test_error e` and `#check e` each stand for a
-- declaration binding `e`, so each scopes the type variables written in its expressions
-- exactly as a `def` does.
def checkAnonDecl (us : Lean.NameSet) (body : Check n α) : Check n α :=
  withHovers (withTyVarScope us body)

partial def Decl.check : {n m : Nat} → (d : Decl n m) → Check m α → Check n α
  | _, _, .mk _ .DeclNil, k => k
  | _, _, .mk _ (.DeclConcat d1 d2), k => Decl.check d1 (Decl.check d2 k)
  | _, _, .mk dstx (.DeclDef name tvars oty e), k => do
    if tvars.hasDup then throwErrorAt dstx s!"Duplicate type variable in declaration"
    checkDefNameFresh dstx name
    -- Open the declared variables keeping the user-written names, so hovers inside the
    -- body show e.g. `k`/`v`.
    let (σ, declared) ← namedSubst tvars
    let e' := Exp.substTy σ e
    let oty' : Option (Ty 0) := oty.map (Ty.subst σ)
    -- What this declaration declares, plus what is implicitly scoped at it: written in an
    -- annotation inside the body that no inner `let` scopes first.
    let us := declared.foldl (·.insert ·) ((annFVars oty').union (Exp.unguardedTyVars e'))
    let inferredTy ← withHovers <| withTyVarScope us do
      let inferredTy ← Exp.infer e'
      if let some t := oty' then unify dstx inferredTy (← normalizeTy t)
      pure inferredTy
    let finalTy ← Ty.resolve inferredTy
    -- Read outside `withTyVarScope`: the closure quantifies `us`, so the context excludes it.
    let envFV ← envFVars
    let isVal := Exp.isValue (← read).valueCtx e'
    let scheme ← closeBinding dstx name us envFV isVal finalTy (topLevel := true)
    addHoverInfo dstx s!"{scheme.pretty}"
    finishDecl
    withDefName dstx name scheme k
  | _, _, .mk _ (.DeclEval e), k
  | _, _, .mk _ (.DeclTestError e _), k => do
    let _ ← checkAnonDecl (Exp.unguardedTyVars e) (Exp.infer e)
    finishDecl
    k
  | _, _, .mk dstx (.DeclTest e1 e2), k => do
    let us := (Exp.unguardedTyVars e1).union (Exp.unguardedTyVars e2)
    let _ ← checkAnonDecl us do
      let t1 ← Exp.infer e1
      let t2 ← Exp.infer e2
      unify dstx t1 t2
    finishDecl
    k
  | _, _, .mk stx (.DeclCheck e), k => do
    let res ← checkAnonDecl (Exp.unguardedTyVars e) (Exp.infer e)
    -- `#check` binds nothing, so an un-generalizable type is not an error here.
    let scheme := Ty.generalize (← envFVars) (← Ty.resolve res)
    logInfoAt stx scheme.pretty
    finishDecl
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
