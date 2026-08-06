import Lean

open Lean Elab Meta

def Vec (n : Nat) a := {l : List a // l.length = n}

def Vec.nil : Vec 0 a := ⟨[], rfl⟩

def Vec.get (v : Vec n a) (i : Fin n) : a :=
  v.val.get (i.cast (by
    cases v
    simp
    grind
  ))

def Vec.cons (v : Vec n a) (x : a) : Vec (n + 1) a :=
  ⟨x :: v.val, by
    cases v
    simp
    grind
 ⟩

def addHoverInfoDelab (stx : Syntax) (s : String) : MetaM Unit :=
  withEnableInfoTree true do
    pushInfoLeaf <| .ofDelabTermInfo {
      elaborator := `Lait.addHoverInfo
      stx := stx
      lctx := (← getLCtx)
      expectedType? := none
      expr := mkConst ``Unit
      mkDocString? := some (fun _ => pure s!"`{s}`")
    }

def strGadget (_ : String) : Unit := ()

open Lean PrettyPrinter Delaborator SubExpr

@[delab app.strGadget]
def delabStrGadget : Delab := do
  let e <- getExpr
  match_expr e with
  | strGadget s => delab s
  | _ => failure

def addHoverInfoTerm (stx : Syntax) (s : String) : MetaM Unit :=
  withEnableInfoTree true do
    pushInfoLeaf <| .ofTermInfo {
      elaborator := `laitElab
      stx := stx
      lctx := {}
      expectedType? := none
      expr := (mkApp (mkConst ``strGadget) (mkStrLit s))
    }

def addHoverInfo (stx : Syntax) (s : String) : MetaM Unit :=
  addHoverInfoDelab stx s


abbrev LogT (T : Type) (m : Type -> Type) (a : Type) := m (List T × a)

def LogT.mk [Monad m] (x : m (List T × a)) : LogT T m a := x


instance [Monad m] : Monad (LogT T m) where
  bind {a} {b} (c : m (List T × a)) (f : a -> m (List T × b)) : m (List T × b) := do
    let (logs, a) <- c
    let (logs', b) <- f a
    pure (logs ++ logs', b)
  pure {a} (x : a) := (pure ([], x) : m (List T × a))

def LogT.lift [Monad m] (x : m α) : LogT T m α := LogT.mk do
  let v <- x
  pure ([], v)

def LogT.run (c : LogT T m a) : m (List T × a) := c

instance [Monad m] : MonadLift m (LogT T m) where
  monadLift {α} (x : m α) : LogT T m α := LogT.lift x
