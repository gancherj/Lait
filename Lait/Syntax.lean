import Lean
import Lait.Surface

mutual
inductive Ty : Nat -> Type where
  | mk : Lean.Syntax -> TyX n -> Ty n
  deriving Repr, Lean.ToExpr, BEq

inductive TyX : Nat -> Type where
  | Int : TyX n
  | Bool : TyX n
  | Str : TyX n
  | Unit : TyX n
  | Arrow : Ty n -> Ty n -> TyX n
  | Prod : Ty n -> Ty n -> TyX n
  | TApp : String -> List (Ty n) -> TyX n
  | Ref : Ty n -> TyX n
  -- Ticked type variables
  | Var : Fin n -> TyX n
  -- evars
  | FVar : Lean.Name -> TyX n
  deriving Repr, Lean.ToExpr, BEq
end

namespace Ty

def Int {n : Nat} : Ty n := .mk .missing .Int
def Var {n : Nat} (i : Fin n) : Ty n := .mk .missing (.Var i)

def get : Ty n -> TyX n
  | .mk _ x => x

end Ty

instance {n : Nat} : Inhabited (Ty n) := ⟨Ty.Int⟩
instance {n : Nat} : Inhabited (TyX n) := ⟨.Int⟩

structure TyScheme where
  tyVars : List String
  ty : Ty tyVars.length
  deriving Lean.ToExpr

inductive Const where
  | Num : Int -> Const
  | Bool : Bool -> Const
  | String : String -> Const
  | Unit : Const
  deriving Repr, Lean.ToExpr


mutual
inductive Exp : Nat -> Nat -> Type where
  | mk : Lean.Syntax -> ExpX n m -> Exp n m
  deriving Repr, Lean.ToExpr

inductive ExpX : Nat -> Nat -> Type where
  | Const : Const -> ExpX n m
  | Lam : String -> Option (Ty n) -> Exp n (m + 1) -> ExpX n m
  | App : Exp n m -> Exp n m -> ExpX n m
  | Let : String -> Option (Ty n) -> Exp n m -> Exp n (m + 1) -> ExpX n m
  | If : Exp n m -> Exp n m -> Exp n m -> ExpX n m
  | Pair : Exp n m -> Exp n m -> ExpX n m
  | Rec : String -> Exp n (m + 1) -> ExpX n m
  | Var : Fin m -> ExpX n m
  | Error : Exp n m -> ExpX n m
  | Print : Exp n m -> ExpX n m
  | Op : String -> (ExpList n m) -> ExpX n m
  | Fst : Exp n m -> ExpX n m
  | Match : Exp n m -> ExpMatchCases n m -> ExpX n m
  | Snd : Exp n m -> ExpX n m
  | Alloc : Exp n m -> ExpX n m
  | Deref : Exp n m -> ExpX n m
  | Assign : Exp n m -> Exp n m -> ExpX n m
  | Try : Exp n m -> Exp n m -> ExpX n m
  -- Runtime terms
  | Loc : Nat -> ExpX n m
  deriving Repr, Lean.ToExpr

inductive ExpList : Nat -> Nat -> Type where
  | Nil : ExpList n m
  | Cons : Exp n m -> ExpList n m -> ExpList n m
  deriving Repr, Lean.ToExpr

inductive ExpMatchCases : Nat -> Nat -> Type where
  | Nil : ExpMatchCases n m
  -- A catch-all wildcard arm.  It binds no variables (body lives in the same
  -- context `m`) and, having no continuation, is structurally always last.
  | Wild : Exp n m -> ExpMatchCases n m
  | Cons : String -> (xs : List String) -> Exp n (m + xs.length) -> ExpMatchCases n m -> ExpMatchCases n m

end

namespace Exp

def Const {n m : Nat} (c : Const) : Exp n m := .mk .missing (.Const c)
def Lam {n m : Nat} (x : String) (oty : Option (Ty n)) (e : Exp n (m + 1)) : Exp n m := .mk .missing (.Lam x oty e)
def Pair {n m : Nat} (e1 e2 : Exp n m) : Exp n m := .mk .missing (.Pair e1 e2)
def Var {n m : Nat} (i : Fin m) : Exp n m := .mk .missing (.Var i)
def Op {n m : Nat} (s : String) (es : ExpList n m) : Exp n m := .mk .missing (.Op s es)
def Loc {n m : Nat} (i : Nat) : Exp n m := .mk .missing (.Loc i)

end Exp


def ExpList.fromList (es : List (Exp n m)) : ExpList n m :=
  es.foldr ExpList.Cons ExpList.Nil

def ExpList.toList (es : ExpList n m) : List (Exp n m) :=
  match es with
  | ExpList.Nil => []
  | ExpList.Cons e es => e :: toList es

def ExpMatchCases.toList (es : ExpMatchCases n m) : List (String × (xs : List String) × Exp n (m + xs.length)) :=
  match es with
  | .Nil => []
  | .Wild _ => []
  | .Cons x xs e k =>  ⟨x, xs, e⟩ :: k.toList

-- The body of the catch-all wildcard arm, if the match has one.
def ExpMatchCases.wild? (es : ExpMatchCases n m) : Option (Exp n m) :=
  match es with
  | .Nil => none
  | .Wild e => some e
  | .Cons _ _ _ k => k.wild?

def Exp.cast (e : Exp n m) (h : m = m') : Exp n m' := h ▸ e

def up_ren (f : Fin n -> Fin m) : Fin (n + 1) -> Fin (m + 1) :=
  Fin.cases 0 (Fin.succ ∘ f)

def up_ren_sum (f : Fin n -> Fin m) (k : Nat) : Fin (n + k) -> Fin (m + k) :=
  match k with
  | 0 => f
  | k' + 1 => up_ren $  up_ren_sum f k'

partial def Ty.rename (σ : Fin n -> Fin n') (ty : Ty n) : Ty n' :=
  match ty with
  | .mk stx .Int => .mk stx .Int
  | .mk stx .Bool => .mk stx .Bool
  | .mk stx .Str => .mk stx .Str
  | .mk stx .Unit => .mk stx .Unit
  | .mk stx (.Arrow ty1 ty2) => .mk stx (.Arrow (rename σ ty1) (rename σ ty2))
  | .mk stx (.Prod ty1 ty2) => .mk stx (.Prod (rename σ ty1) (rename σ ty2))
  | .mk stx (.Ref ty) => .mk stx (.Ref (rename σ ty))
  | .mk stx (.Var i) => .mk stx (.Var (σ i))
  | .mk stx (.TApp s ts) => .mk stx (.TApp s (ts.attach.map fun ⟨x, _⟩ => x.rename σ))
  | .mk stx (.FVar n) => .mk stx (.FVar n)

mutual
  def Exp.rename (σ : Fin n -> Fin n') (σ' : Fin m -> Fin m')
    (exp : Exp n m) : Exp n' m' :=
    match exp with
    | .mk stx (.Const c) => .mk stx (.Const c)
    | .mk stx (.Lam x oty e) => .mk stx (.Lam x (oty.map (·.rename σ)) (Exp.rename σ (up_ren σ') e))
    | .mk stx (.App e1 e2) => .mk stx (.App (Exp.rename σ σ' e1) (Exp.rename σ σ' e2))
    | .mk stx (.Let x oty e1 e2) => .mk stx (.Let x (oty.map (·.rename σ)) (Exp.rename σ σ' e1) (Exp.rename σ (up_ren σ') e2))
    | .mk stx (.If e1 e2 e3) => .mk stx (.If (Exp.rename σ σ' e1) (Exp.rename σ σ' e2) (Exp.rename σ σ' e3))
    | .mk stx (.Op s es) => .mk stx (.Op s (ExpList.rename σ σ' es))
    | .mk stx (.Pair e1 e2) => .mk stx (.Pair (Exp.rename σ σ' e1) (Exp.rename σ σ' e2))
    | .mk stx (.Error e) => .mk stx (.Error (Exp.rename σ σ' e))
    | .mk stx (.Print e) => .mk stx (.Print (Exp.rename σ σ' e))
    | .mk stx (.Fst e) => .mk stx (.Fst (Exp.rename σ σ' e))
    | .mk stx (.Snd e) => .mk stx (.Snd (Exp.rename σ σ' e))
    | .mk stx (.Var i) => .mk stx (.Var (σ' i))
    | .mk stx (.Alloc e) => .mk stx (.Alloc (Exp.rename σ σ' e))
    | .mk stx (.Deref e) => .mk stx (.Deref (Exp.rename σ σ' e))
    | .mk stx (.Assign e1 e2) => .mk stx (.Assign (Exp.rename σ σ' e1) (Exp.rename σ σ' e2))
    | .mk stx (.Try e1 e2) => .mk stx (.Try (Exp.rename σ σ' e1) (Exp.rename σ σ' e2))
    | .mk stx (.Loc i) => .mk stx (.Loc i)
    | .mk stx (.Match e cases) => .mk stx (.Match (Exp.rename σ σ' e) (ExpMatchCases.rename σ σ' cases))
    | .mk stx (.Rec x e) => .mk stx (.Rec x (Exp.rename σ (up_ren σ') e))

  def ExpList.rename (σ : Fin n -> Fin n') (σ' : Fin m -> Fin m')
    (expList : ExpList n m) : ExpList n' m' :=
    match expList with
    | ExpList.Nil => ExpList.Nil
    | ExpList.Cons e es => ExpList.Cons (Exp.rename σ σ' e) (ExpList.rename σ σ' es)

  def ExpMatchCases.rename (σ : Fin n -> Fin n') (σ' : Fin m -> Fin m')
    (cases : ExpMatchCases n m) : ExpMatchCases n' m' :=
    match cases with
    | ExpMatchCases.Nil => ExpMatchCases.Nil
    | ExpMatchCases.Wild e => ExpMatchCases.Wild (Exp.rename σ σ' e)
    | ExpMatchCases.Cons x xs e cases => ExpMatchCases.Cons x xs (Exp.rename σ (up_ren_sum σ' xs.length) e) (ExpMatchCases.rename σ σ' cases)
end

partial def Ty.subst (σ : Fin n -> Ty n') (ty : Ty n) : Ty n' :=
  match ty with
  | .mk stx .Int => .mk stx .Int
  | .mk stx .Bool => .mk stx .Bool
  | .mk stx .Str => .mk stx .Str
  | .mk stx .Unit => .mk stx .Unit
  | .mk stx (.Arrow ty1 ty2) => .mk stx (.Arrow (subst σ ty1) (subst σ ty2))
  | .mk stx (.Prod ty1 ty2) => .mk stx (.Prod (subst σ ty1) (subst σ ty2))
  | .mk stx (.Ref ty) => .mk stx (.Ref (subst σ ty))
  | .mk _ (.Var i) => σ i
  | .mk stx (.TApp s ts) => .mk stx (.TApp s (ts.attach.map fun ⟨x, _⟩  => x.subst σ))
  | .mk stx (.FVar n) => .mk stx (.FVar n)

partial def Ty.close (s : Lean.Name) (t : Ty n) : Ty (n + 1) :=
  match t with
  | .mk stx .Int => .mk stx .Int
  | .mk stx .Bool => .mk stx .Bool
  | .mk stx .Str => .mk stx .Str
  | .mk stx .Unit => .mk stx .Unit
  | .mk stx (.Arrow ty1 ty2) => .mk stx (.Arrow (close s ty1) (close s ty2))
  | .mk stx (.Prod ty1 ty2) => .mk stx (.Prod (close s ty1) (close s ty2))
  | .mk stx (.Ref ty1) => .mk stx (.Ref (close s ty1))
  | .mk stx (.Var i) => .mk stx (.Var (Fin.succ i))
  | .mk stx (.TApp o ts) => .mk stx (.TApp o (ts.attach.map fun ⟨x, _⟩ => x.close s))
  | .mk stx (.FVar n) => if n = s then .mk stx (.Var 0) else .mk stx (.FVar n)

mutual
  partial def Ty.substFVars [Monad M] [MonadExcept String M] (m : Lean.NameMap (TyX 0)) (t : Ty 0) : M (Ty 0) :=
    match t with
    | .mk stx inner => do pure (.mk stx (<- TyX.substFVars m inner))

  partial def TyX.substFVars [Monad M] [MonadExcept String M] (m : Lean.NameMap (TyX 0)) (t : TyX 0) : M (TyX 0) :=
      match t with
      | .Int => pure .Int
      | .Unit => pure .Unit
      | .Bool => pure .Bool
      | .Str => pure .Str
      | .FVar j =>
        match m.get? j with
        | some t => pure t
        | _ => throw $ s!"Unknown type variable: {j}"
      | .Var i => pure $ .Var i
      | .Arrow t1 t2 => do pure $ .Arrow (← Ty.substFVars m t1) (← Ty.substFVars m t2)
      | .Prod t1 t2 => do pure $ .Prod (← Ty.substFVars m t1) (← Ty.substFVars m t2)
      | .Ref t => do pure $ .Ref (← Ty.substFVars m t)
      | .TApp s ts => do pure $ .TApp s (← ts.attach.mapM fun ⟨x, _⟩ => Ty.substFVars m x)
end



-- Substitute the *type* variables of an expression (`Fin n → Ty n'`), leaving
-- the term structure and its de Bruijn indices untouched.  Term binders never
-- bind type variables, so `σ` is threaded unchanged under them — there is no
-- `up_subst`, hence none of the naive-de-Bruijn renaming that makes the general
-- `Exp.subst` blow up super-linearly with the term's variable depth.
mutual
def Exp.substTy (σ : Fin n -> Ty n') : Exp n m -> Exp n' m
  | .mk stx x => .mk stx (ExpX.substTy σ x)

def ExpX.substTy (σ : Fin n -> Ty n') : ExpX n m -> ExpX n' m
  | .Const c => .Const c
  | .Lam x oty e => .Lam x (oty.map (Ty.subst σ)) (Exp.substTy σ e)
  | .App e1 e2 => .App (Exp.substTy σ e1) (Exp.substTy σ e2)
  | .Let x oty e1 e2 => .Let x (oty.map (Ty.subst σ)) (Exp.substTy σ e1) (Exp.substTy σ e2)
  | .If e1 e2 e3 => .If (Exp.substTy σ e1) (Exp.substTy σ e2) (Exp.substTy σ e3)
  | .Pair e1 e2 => .Pair (Exp.substTy σ e1) (Exp.substTy σ e2)
  | .Rec x e => .Rec x (Exp.substTy σ e)
  | .Var i => .Var i
  | .Error e => .Error (Exp.substTy σ e)
  | .Print e => .Print (Exp.substTy σ e)
  | .Op s es => .Op s (ExpList.substTy σ es)
  | .Fst e => .Fst (Exp.substTy σ e)
  | .Match e cases => .Match (Exp.substTy σ e) (ExpMatchCases.substTy σ cases)
  | .Snd e => .Snd (Exp.substTy σ e)
  | .Alloc e => .Alloc (Exp.substTy σ e)
  | .Deref e => .Deref (Exp.substTy σ e)
  | .Assign e1 e2 => .Assign (Exp.substTy σ e1) (Exp.substTy σ e2)
  | .Try e1 e2 => .Try (Exp.substTy σ e1) (Exp.substTy σ e2)
  | .Loc i => .Loc i

def ExpList.substTy (σ : Fin n -> Ty n') : ExpList n m -> ExpList n' m
  | .Nil => .Nil
  | .Cons e es => .Cons (Exp.substTy σ e) (ExpList.substTy σ es)

def ExpMatchCases.substTy (σ : Fin n -> Ty n') : ExpMatchCases n m -> ExpMatchCases n' m
  | .Nil => .Nil
  | .Wild e => .Wild (Exp.substTy σ e)
  | .Cons x xs e cases => .Cons x xs (Exp.substTy σ e) (ExpMatchCases.substTy σ cases)
end

--- Conversion between surface and DB-indexed


mutual
inductive Decl : Nat -> Nat -> Type where
  | mk : Lean.Syntax -> DeclX n m -> Decl n m
  deriving Lean.ToExpr

inductive DeclX : Nat -> Nat -> Type where
  | DeclDef : String -> (tvars : List String) -> Option (Ty tvars.length) -> Exp tvars.length n -> DeclX n (n + 1)
  | DeclTypeAlias : String -> TyScheme -> DeclX n n
  | DeclEval : Exp 0 n -> DeclX n n
  | DeclTest : Exp 0 n -> Exp 0 n -> DeclX n n
  | DeclTestError : Exp 0 n -> String -> DeclX n n
  | DeclCheck : Exp 0 n -> DeclX n n
  | DeclInductive : String ->  (tvars : List String) ->
    List (String × List (String × Ty tvars.length)) ->
    DeclX n n
  | DeclNil : DeclX n n
  | DeclConcat : Decl n m -> Decl m k -> DeclX n k
  deriving Lean.ToExpr

end

def Exp.bump (e : Exp t n) (k : Nat) : Exp t (n + k) :=
 e.rename id (fun i => ⟨i.val + k, by grind⟩ )

def DeclX.castR (d : DeclX n m) (h : m = m') : DeclX n m' := h ▸ d

def Decl.cast (d : Decl n m) (h : n = n') (h' : m = m') : Decl n' m' :=
  h ▸ h' ▸ d

namespace Decl

def DeclNil {n : Nat} : Decl n n :=
  .mk .missing .DeclNil

def DeclConcat {n m k : Nat} (d1 : Decl n m) (d2 : Decl m k) : Decl n k :=
  .mk .missing (.DeclConcat d1 d2)

def bump (d : Decl n m) (k : Nat) : Decl (n + k) (m + k) :=
  match d with
  | .mk stx .DeclNil => .mk stx .DeclNil
  | .mk stx (.DeclConcat d1 d2) => .mk stx (.DeclConcat (bump d1 k) (bump d2 k))
  | .mk stx (.DeclDef s tvars oty e) => .mk stx $ (DeclX.DeclDef s tvars oty (Exp.bump e k)).castR (by grind)
  | .mk stx (.DeclTypeAlias s ty) => .mk stx $ (DeclX.DeclTypeAlias s ty)
  | .mk stx (.DeclEval e) => .mk stx $ (DeclX.DeclEval (Exp.bump e k)).castR (by grind)
  | .mk stx (.DeclTest e1 e2) => .mk stx $ (DeclX.DeclTest (Exp.bump e1 k) (Exp.bump e2 k)).castR (by grind)
  | .mk stx (.DeclTestError e s) => .mk stx $ (DeclX.DeclTestError (Exp.bump e k) s).castR (by grind)
  | .mk stx (.DeclCheck e) => .mk stx $ (DeclX.DeclCheck (Exp.bump e k)).castR (by grind)
  | .mk stx (.DeclInductive n tvars cs) => .mk stx $ (DeclX.DeclInductive n tvars cs)

end Decl
