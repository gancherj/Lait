import Lait.Surface
import Lait.Syntax

open Lean Elab Command


partial def Ty.fromSurface (ty : Surface.Ty) (tvars : List String) : CommandElabM (Ty tvars.length) :=
  match ty with
  | .mk stx .Int => pure (.mk stx .Int)
  | .mk stx .Bool => pure (.mk stx .Bool)
  | .mk stx .Str => pure (.mk stx .Str)
  | .mk stx .Unit => pure (.mk stx .Unit)
  | .mk stx (.Arrow ty1 ty2) => do
      pure (.mk stx (.Arrow (<- fromSurface ty1 tvars) (<- fromSurface ty2 tvars)))
  | .mk stx (.Prod ty1 ty2) => do
      pure (.mk stx (.Prod (<- fromSurface ty1 tvars) (<- fromSurface ty2 tvars)))
  | .mk stx (.TApp s ts) => do
      let tys <- ts.mapM (fromSurface · tvars)
      pure $ .mk stx (.TApp s tys)
  | .mk stx (.Ref ty) => do
      pure (.mk stx (.Ref (<- fromSurface ty tvars)))
  | .mk stx (.Var s) =>
    match tvars.findFinIdx? (· == s) with
    | some i => pure (.mk stx (.Var i))
    | none => pure (.mk stx (.FVar (s.toName)))
  | .mk stx (.Record xs) => do
    let xs' <- xs.mapM (fun (x, y) => do
      let y' <- fromSurface y tvars
      pure (x, y'))
    pure (.mk stx (.Record xs'))

mutual
partial def Exp.fromSurface (exp : Surface.Exp) (tvars : List String) (vars : List String) : CommandElabM (Exp tvars.length vars.length) :=
  match exp with
  | .mk stx (.Const (Surface.Const.Num n)) => pure (.mk stx (.Const (Const.Num n)))
  | .mk stx (.Const (Surface.Const.Bool b)) => pure (.mk stx (.Const (Const.Bool b)))
  | .mk stx (.Const (Surface.Const.String s)) => pure (.mk stx (.Const (Const.String s)))
  | .mk stx (.Const Surface.Const.Unit) => pure (.mk stx (.Const Const.Unit))
  | .mk stx (.Lam x oty e) => do
      pure (.mk stx (.Lam x (<- oty.mapM (Ty.fromSurface · tvars)) (<- Exp.fromSurface e tvars (x :: vars))))
  | .mk stx (.App e1 e2) => do
      pure (.mk stx (.App (<- Exp.fromSurface e1 tvars vars) (<- Exp.fromSurface e2 tvars vars)))
  | .mk stx (.Let x oty e1 e2) => do
      pure (.mk stx (.Let x (<- oty.mapM (Ty.fromSurface · tvars)) (<- Exp.fromSurface e1 tvars vars) (<- Exp.fromSurface e2 tvars (x :: vars))))
  | .mk stx (.If e1 e2 e3) => do
      pure (.mk stx (.If (<- Exp.fromSurface e1 tvars vars) (<- Exp.fromSurface e2 tvars vars) (<- Exp.fromSurface e3 tvars vars)))
  | .mk stx (.Pair e1 e2) => do
      pure (.mk stx (.Pair (<- Exp.fromSurface e1 tvars vars) (<- Exp.fromSurface e2 tvars vars)))
  | .mk stx (.Error e) => do
      pure (.mk stx (.Error (<- Exp.fromSurface e tvars vars)))
  | .mk stx (.Print e) => do
      pure (.mk stx (.Print (<- Exp.fromSurface e tvars vars)))
  | .mk stx (.Var s) =>
    match vars.findFinIdx? (· == s) with
    | some i => pure (.mk stx (.Var i))
    | none => throwErrorAt stx s!"Variable {s} not found"
  | .mk stx (.Alloc e) => do
      pure (.mk stx (.Alloc (<- Exp.fromSurface e tvars vars)))
  | .mk stx (.Deref e) => do
      pure (.mk stx (.Deref (<- Exp.fromSurface e tvars vars)))
  | .mk stx (.Assign e1 e2) => do
      pure (.mk stx (.Assign (<- Exp.fromSurface e1 tvars vars) (<- Exp.fromSurface e2 tvars vars)))
  | .mk stx (.Try e1 e2) => do
      pure (.mk stx (.Try (<- Exp.fromSurface e1 tvars vars) (<- Exp.fromSurface e2 tvars vars)))
  | .mk stx (.Op s es) => do
      let es' <- es.mapM (Exp.fromSurface · tvars vars)
      pure $ .mk stx (.Op s (ExpList.fromList es'))
  | .mk stx (.Fst e) => do
      pure (.mk stx (.Fst (<- Exp.fromSurface e tvars vars)))
  | .mk stx (.Snd e) => do
      pure (.mk stx (.Snd (<- Exp.fromSurface e tvars vars)))
  | .mk stx (.Match e cases owild) => do
    let cases' <- casesFromSurface cases owild tvars vars
    pure (.mk stx (.Match (<- Exp.fromSurface e tvars vars) cases'))
  | .mk stx (.Rec x e) => do
      pure (.mk stx (.Rec x (<- Exp.fromSurface e tvars (x :: vars))))
  | .mk stx (.RecordGet e x) => do
      pure (.mk stx (.RecordGet (<- Exp.fromSurface e tvars vars) x))
  | .mk stx (.MkRecord xs) => do
      let xs' <- xs.mapM (fun (x, e) => do
        let e' <- Exp.fromSurface e tvars vars
        pure (x, e'))
      pure (.mk stx (.MkRecord (ExpRecord.fromList xs')))

partial def casesFromSurface (cases : List (String × List String × Surface.Exp)) (owild : Option Surface.Exp) (tvars : List String) (vars : List String) : CommandElabM (ExpMatchCases tvars.length vars.length) :=
  match cases with
  | [] =>
    match owild with
    | none => pure ExpMatchCases.Nil
    | some bdy => do
        pure (ExpMatchCases.Wild (<- Exp.fromSurface bdy tvars vars))
  | ((x, xs, bdy) :: cases) => do
      let cases' <- casesFromSurface cases owild tvars vars
      let bdy <- Exp.fromSurface bdy tvars (xs ++ vars)
      pure (ExpMatchCases.Cons x xs (bdy.cast (by grind)) cases')
end

mutual

partial def Decl.fromSurfaceEntry (d : Surface.DeclEntry) (vars : List String) : CommandElabM ((vars' : List String) × (Decl vars.length vars'.length)) :=
  match d.val with
  | .DeclEntryDef s oty e => do
    let tvars := match oty with
                  | none => []
                  | some ty => ty.tyVars
    let oty' <- oty.mapM (Ty.fromSurface · tvars)
    let e' <- Exp.fromSurface e tvars vars
    pure ⟨s :: vars, .mk d.stx (.DeclDef s tvars oty' e')⟩
  | .DeclEval e => do
    let e' <- Exp.fromSurface e [] vars
    pure ⟨vars, .mk d.stx (.DeclEval e')⟩
  | .DeclTest e1 e2 => do
    let e1' <- Exp.fromSurface e1 [] vars
    let e2' <- Exp.fromSurface e2 [] vars
    pure ⟨vars, .mk d.stx (.DeclTest e1' e2')⟩
  | .DeclTestError e s => do
    let e' <- Exp.fromSurface e [] vars
    pure ⟨vars, .mk d.stx (.DeclTestError e' s)⟩
  | .DeclCheck e => do
    let e' <- Exp.fromSurface e [] vars
    pure ⟨vars, .mk d.stx (.DeclCheck e')⟩
  | .DeclEntryTypeAlias s tvars ty => do
    let tvars := if tvars.isEmpty then ty.tyVars else tvars
    let ty' <- Ty.fromSurface ty tvars
    pure ⟨vars, .mk d.stx (.DeclTypeAlias s ⟨tvars, ty'⟩)⟩
  | .DeclEntryDefFn _ _ _ _ => throwError "DefFn: should be eliminated via surface pass"
  | .DeclEntryDefMutual _ => throwError "DefMutual: should be eliminated via surface pass"
  | .DeclEntryMutualTypes _ => throwError "MutualTypes: should be eliminated via surface pass"
  | .DeclList ds => Decl.fromSurface ds vars
  | .DeclEntryInductive n tvars cs => do
    let cs' <- cs.mapM (fun (cname, args) => do
      let args' <- args.mapM (fun (argname, argty) => do
         let argty' <- Ty.fromSurface argty tvars
         pure (argname, argty'))
      pure (cname, args'))
    pure ⟨vars, .mk d.stx (.DeclInductive n tvars cs')⟩

partial def Decl.fromSurface (ds : List Surface.DeclEntry) (vars : List String) : CommandElabM ((vars' : List String) × (Decl vars.length vars'.length)) :=
  match ds with
  | [] => pure ⟨vars, .DeclNil⟩
  | d :: ds => do
    let ⟨vars', d'⟩ <- Decl.fromSurfaceEntry d vars
    let ⟨vars'', ds'⟩ <- Decl.fromSurface ds vars'
    pure ⟨vars'', .DeclConcat d' ds'⟩

end
