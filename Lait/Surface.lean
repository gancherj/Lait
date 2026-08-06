import Std.Data.TreeMap
import Lean

deriving instance Lean.ToExpr for String.Pos.Raw
deriving instance Lean.ToExpr for Substring.Raw
deriving instance Lean.ToExpr for Lean.SourceInfo
deriving instance Lean.ToExpr for Lean.Syntax

namespace Surface

mutual
inductive Ty where
  | mk : Lean.Syntax -> TyX -> Ty
  deriving Repr, Lean.ToExpr

inductive TyX where
  | Int : TyX
  | Bool : TyX
  | Str : TyX
  | Unit : TyX
  | Arrow : Ty -> Ty -> TyX
  | Prod : Ty -> Ty -> TyX
  | TApp : String -> List Ty -> TyX
  | Ref : Ty -> TyX
  -- Ticked type variables
  | Var : String -> TyX
  | Record : List (String × Ty) -> TyX
  deriving Repr, Lean.ToExpr
end

namespace Ty

def Arrow (t1 t2 : Ty) : Ty := .mk .missing (.Arrow t1 t2)
def TApp (s : String) (ts : List Ty) : Ty := .mk .missing (.TApp s ts)
def Var (s : String) : Ty := .mk .missing (.Var s)

private partial def collectTyVars (t : Ty) : List String :=
  match t with
  | .mk _ (.Var x) => [x]
  | .mk _ (.Arrow t1 t2) => t1.collectTyVars ++ t2.collectTyVars
  | .mk _ (.Prod t1 t2) => t1.collectTyVars ++ t2.collectTyVars
  | .mk _ (.TApp _ ts) => (ts.attach.map fun ⟨x, _⟩ => x.collectTyVars).flatten
  | .mk _ (.Ref t) => t.collectTyVars
  | .mk _ .Int => []
  | .mk _ .Bool => []
  | .mk _ .Str => []
  | .mk _ .Unit => []
  | .mk _ (.Record xs) =>
      (xs.attach.map fun ⟨x, _⟩ => x.2.collectTyVars).flatten

def tyVars (t : Ty) : List String :=
  t.collectTyVars.eraseDups.mergeSort

end Ty

inductive Const where
  | Num : Int -> Const
  | Bool : Bool -> Const
  | String : String -> Const
  | Unit : Const
  deriving Repr, Lean.ToExpr


mutual
inductive Exp where
  | mk : Lean.Syntax -> ExpX -> Exp
  deriving Repr, Lean.ToExpr

inductive ExpX where
  | Const : Const -> ExpX
  | Lam : String -> Option Ty -> Exp -> ExpX
  | App : Exp -> Exp -> ExpX
  | Let : String -> Option Ty -> Exp -> Exp -> ExpX
  | If : Exp -> Exp -> Exp -> ExpX
  | Pair : Exp -> Exp -> ExpX
  | Fst : Exp -> ExpX
  | Rec : String -> Exp -> ExpX
  | Snd : Exp -> ExpX
  | Error : Exp -> ExpX
  | Print : Exp -> ExpX
  -- Constructor arms, plus an optional trailing catch-all wildcard body.
  | Match : Exp -> List (String × List String × Exp) -> Option Exp -> ExpX
  | Var : String -> ExpX
  | Op : String -> List Exp -> ExpX -- Primitive operators; datatype constructors
  | Alloc : Exp -> ExpX
  | Deref : Exp -> ExpX
  | Assign : Exp -> Exp -> ExpX
  -- `try e1 with e2 end`: evaluate e1; if it raises an error, evaluate e2.
  | Try : Exp -> Exp -> ExpX
  | RecordGet : Exp -> String -> ExpX
  | MkRecord : List (String × Exp) -> ExpX
  deriving Repr, Lean.ToExpr
end

namespace Exp

def Lam (x : String) (oty : Option Ty) (e : Exp) : Exp := .mk .missing (.Lam x oty e)
def Var (x : String) : Exp := .mk .missing (.Var x)
def Op (s : String) (es : List Exp) : Exp := .mk .missing (.Op s es)

-- Capture-avoiding substitution of (free) variables by name.  `m` maps variable
-- names to replacement expressions; whenever a binder shadows one of those names
-- the mapping is dropped for that subtree.  Used to wire mutually-recursive
-- functions to projections of their shared fixpoint bundle.
partial def substVars (m : List (String × Exp)) : Exp -> Exp
  | .mk stx ex =>
    let rem (xs : List String) := m.filter (fun (n, _) => !xs.contains n)
    match ex with
    | .Var s =>
      match m.find? (fun (n, _) => n == s) with
      | some (_, e') => e'
      | none => .mk stx (.Var s)
    | .Const c => .mk stx (.Const c)
    | .Lam x oty e => .mk stx (.Lam x oty (substVars (rem [x]) e))
    | .App e1 e2 => .mk stx (.App (substVars m e1) (substVars m e2))
    | .Let x oty e1 e2 => .mk stx (.Let x oty (substVars m e1) (substVars (rem [x]) e2))
    | .If e1 e2 e3 => .mk stx (.If (substVars m e1) (substVars m e2) (substVars m e3))
    | .Pair e1 e2 => .mk stx (.Pair (substVars m e1) (substVars m e2))
    | .Fst e => .mk stx (.Fst (substVars m e))
    | .Snd e => .mk stx (.Snd (substVars m e))
    | .Rec x e => .mk stx (.Rec x (substVars (rem [x]) e))
    | .Error e => .mk stx (.Error (substVars m e))
    | .Print e => .mk stx (.Print (substVars m e))
    | .Op s es => .mk stx (.Op s (es.map (substVars m)))
    | .Alloc e => .mk stx (.Alloc (substVars m e))
    | .Deref e => .mk stx (.Deref (substVars m e))
    | .Assign e1 e2 => .mk stx (.Assign (substVars m e1) (substVars m e2))
    | .Try e1 e2 => .mk stx (.Try (substVars m e1) (substVars m e2))
    | .Match e cases owild =>
      .mk stx (.Match (substVars m e)
        (cases.map fun (c, xs, b) => (c, xs, substVars (rem xs) b))
        (owild.map (substVars m)))
    | .RecordGet e x => .mk stx (.RecordGet (substVars m e) x)
    | .MkRecord xs => .mk stx (.MkRecord (xs.map fun (n, e) => (n, substVars m e)))

-- Right-nested tuple of a non-empty list (a singleton is the element itself).
def mkTuple : List Exp -> Exp
  | [] => .mk .missing (.Const .Unit)
  | [e] => e
  | e :: es => .mk .missing (.Pair e (mkTuple es))

-- Apply `snd` `i` times.
def sndN : Nat -> Exp -> Exp
  | 0, e => e
  | k + 1, e => .mk .missing (.Snd (sndN k e))

-- Project the `i`-th component (0-based) out of a `k`-element `mkTuple`.
def nthProj (i k : Nat) (e : Exp) : Exp :=
  if i + 1 == k then sndN i e else .mk .missing (.Fst (sndN i e))

end Exp

mutual

inductive DeclEntryX where
  | DeclEntryDef : String -> Option Ty -> Exp -> DeclEntryX
  | DeclEntryDefFn : String -> List (String × Ty) -> Exp -> Ty -> DeclEntryX
  -- A group of mutually-recursive function definitions linked with `and`.  Each
  -- clause is (syntax, name, args, return type, body).  Argument and return-type
  -- annotations are optional (`none` means "infer").  Lowered to a single shared
  -- fixpoint bundle by `elabDefMutual`.
  | DeclEntryDefMutual : List (Lean.Syntax × String × List (String × Option Ty) × Option Ty × Exp) -> DeclEntryX
  | DeclEntryTypeAlias : String -> List String -> Ty -> DeclEntryX
  | DeclList : List DeclEntry -> DeclEntryX
  | DeclEntryInductive :
     String ->  -- Type name
     List String  ->  -- Type argument variables
     List (String × List (String × Ty)) -> -- Constructor names and their arguments
     DeclEntryX
  -- A group of mutually-recursive inductive types linked with `and`.  Each entry
  -- is (name, type variables, constructors).  Lowered by `elabConstrFns` so that
  -- every type is registered before any constructor function is elaborated.
  | DeclEntryMutualTypes : List (String × List String × List (String × List (String × Ty))) -> DeclEntryX
  | DeclEval : Exp -> DeclEntryX
  | DeclTest : Exp -> Exp -> DeclEntryX
  -- Assert that evaluating the expression aborts with an error whose message
  -- contains the given substring.
  | DeclTestError : Exp -> String -> DeclEntryX
  | DeclCheck : Exp -> DeclEntryX
  deriving Repr, Lean.ToExpr

structure DeclEntry where
  stx : Lean.Syntax
  val : DeclEntryX
  deriving Repr, Lean.ToExpr

end

namespace DeclEntry

def DeclEntryDef (s : String) (oty : Option Ty) (e : Exp) : DeclEntry :=
  ⟨.missing, .DeclEntryDef s oty e⟩

def doPass (f : DeclEntry -> List DeclEntry) : List DeclEntry -> List DeclEntry :=
  fun xs =>
    match xs with
    | [] => []
    | d::ds => (f d) ++ doPass f ds

def flattenDecls (d : DeclEntry) : List DeclEntry :=
  match d.val with
  | .DeclList ds => ds
  | _ => [d]

-- The constructor functions for one inductive type: each constructor `C` of
-- arity n becomes `def C : T1 -> ... -> Tn -> Out := fun x0 ... x_{n-1} => C x0 ...`.
def mkConstrFns (c : String) (tvs : List String) (cs : List (String × List (String × Ty))) : List DeclEntry :=
  let outTy : Ty := .TApp c (tvs.map .Var)
  cs.map fun (cname, args) =>
    let rec go (args : List (String × Ty)) (vars : List String) (i : Nat) : Exp :=
      match args with
      | [] => .Op cname (vars.map .Var)
      | (_, argTy) :: args' =>
        let v := s!"x{i}"
        .Lam v (some argTy) $ go args' (vars ++ [v]) (i + 1)
    let fullTy : Ty := args.foldr (fun (_, argTy) acc => .Arrow argTy acc) outTy
    .DeclEntryDef cname (some fullTy) (go args [] 0)

def elabConstrFns (d : DeclEntry) : List DeclEntry :=
  match d.val with
  | .DeclEntryInductive c tvs cs => d :: mkConstrFns c tvs cs
  | .DeclEntryMutualTypes inds =>
    -- All type declarations first, so every type is in scope before any
    -- constructor function (whose signature may reference a sibling type).
    let indDecls := inds.map fun (c, tvs, cs) => (⟨d.stx, .DeclEntryInductive c tvs cs⟩ : DeclEntry)
    let ctorFns := inds.flatMap fun (c, tvs, cs) => mkConstrFns c tvs cs
    indDecls ++ ctorFns
  | _ => [d]

def elabDefFn (d : DeclEntry) : List DeclEntry :=
  match d.val with
  | .DeclEntryDefFn s args e oty =>
    -- Elaborates to def s : (arg types to output type) := rec f.  fun args => e
    let rec go_e (args : List (String × Ty)) (body : Exp) :=
     match args with
     | [] => body
     | (x, argTy) :: args' =>
      .Lam x (some argTy) $ go_e args' body
    let fn_ty := args.foldr (fun (_, argTy) acc => .Arrow argTy acc) oty
    let fn_exp : Exp := Exp.mk d.stx (.Rec s (go_e args e))
    [.DeclEntryDef s (some fn_ty) fn_exp]
  | _ => [d]

-- Lower a group of mutually-recursive functions to a single self-recursive
-- bundle.  The functions f₁ … f_k are packed into a right-nested tuple built by
-- one `fix`; inside each body every reference to a sibling fᵢ is rewritten to a
-- projection of the bundle (`self`).  Those projections sit under the function's
-- own lambdas, so they are only forced when the function is called (never while
-- building the tuple), which is what makes the recursion terminate.  Each
-- top-level name is then defined as its own projection of the (inlined) bundle,
-- so each may be generalized independently.
def elabDefMutual (d : DeclEntry) : List DeclEntry :=
  match d.val with
  | .DeclEntryDefMutual clauses =>
    let k := clauses.length
    let selfName := "$mutual$self"
    let names := clauses.map (fun (_, name, _, _, _) => name)
    let projMap : List (String × Exp) :=
      names.mapIdx (fun j name => (name, Exp.nthProj j k (.Var selfName)))
    let mkF := fun (clause : Lean.Syntax × String × List (String × Option Ty) × Option Ty × Exp) =>
      let (_, _, args, ret, body) := clause
      let argNames := args.map (·.1)
      -- A parameter shadows a sibling function of the same name.
      let projMap' := projMap.filter (fun (n, _) => !argNames.contains n)
      let body' := Exp.substVars projMap' body
      -- Pin the body to the declared return type, when one is given.
      let bodyRet : Exp := match ret with
        | some _ => .mk .missing (.Let "$mutual$ret" ret body' (.Var "$mutual$ret"))
        | none => body'
      args.foldr (fun (x, ty) acc => Exp.Lam x ty acc) bodyRet
    let tuple := Exp.mkTuple (clauses.map mkF)
    -- The bundle node is synthetic: give it no source span so its (pair) type
    -- doesn't get recorded as a hover on the first function's identifier, which
    -- shares `d.stx`.  Each function's own hover comes from its `DeclEntryDef`.
    let fixExp : Exp := .mk .missing (.Rec selfName tuple)
    clauses.mapIdx (fun i clause =>
      let (stx, name, _, _, _) := clause
      ⟨stx, .DeclEntryDef name none (Exp.nthProj i k fixExp)⟩)
  | _ => [d]

def doAllPasses (ds : List DeclEntry) :=
  doPass elabDefFn $ doPass elabDefMutual $ doPass elabConstrFns $ doPass flattenDecls ds

end DeclEntry

end Surface
