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

/-- Keep only `stx`'s source range, dropping its tree.  Syntax without a range -- a
declaration synthesized by a surface pass, or one spliced in from another module -- stays
position-less, so that nothing is attached to position 0 of the file. -/
def Lean.Syntax.strip (stx : Syntax) : Syntax :=
  match stx.getRange? with
  | some r => Syntax.ofRange r
  | none => .missing

/-- `stx`'s source range collapsed to its start.  Marks a source location -- for
"go to definition" -- without covering a range that a hover could attach to. -/
def Lean.Syntax.startMarker (stx : Syntax) : Syntax :=
  match stx.getRange? with
  | some r => Syntax.ofRange ⟨r.start, r.start⟩
  | none => .missing

/-- Erase every source position in `stx`.  Applied to the syntax of an `#include`d
declaration: those positions refer to the file that defined the module, so keeping them
would attach that declaration's hovers -- and their go-to-definition targets -- to
arbitrary offsets of the file being elaborated. -/
partial def Lean.Syntax.clearSourceInfo : Syntax → Syntax
  | .node _ kind args => .node .none kind (args.map clearSourceInfo)
  | .atom _ val => .atom .none val
  | .ident _ rawVal val preresolved => .ident .none rawVal val preresolved
  | .missing => .missing

/-- Carrier for the dummy expression of a Lait info-tree leaf (see `addHoverInfoDelab`),
with a delaborator that prints the string, so that Lait leaves are readable in
`trace.Elab.info` output.  Its result is a *sort*, so that neither an application of it nor
the type of that application is a constant -- which is what keeps go-to-definition, in any
of its flavours (`textDocument/definition`, `typeDefinition`, ...), from resolving a Lait
hover into Lean's own library. -/
def strGadget (_ : String) : Prop := True

section
open Lean PrettyPrinter Delaborator SubExpr

@[delab app.strGadget]
def delabStrGadget : Delab := do
  let e <- getExpr
  match_expr e with
  | strGadget s => delab s
  | _ => failure

end

/-- A `DeclarationLocation` collapsed to the start of `stx`, in module `mod`.  Used as the
"go to definition" target of a Lait hover: collapsing it means the client moves the cursor
to the start of the definition instead of selecting the whole declaration. -/
def mkStartLocation? [Monad m] [MonadFileMap m] (mod : Name) (stx : Syntax) :
    m (Option DeclarationLocation) := do
  let some r ← getDeclarationRange? stx
    | return none
  return some { module := mod, range := { r with endPos := r.pos, endCharUtf16 := r.charUtf16 } }

/-- Attach the Lait hover text `s` to `stx`.  `loc?` is where "go to definition" on `stx`
should jump; `none` means clicking it does nothing.

The `expr` is a dummy -- the hover of a `DelabTermInfo` comes from `mkDocString?` alone,
since `Info.fmtHover?` only pretty-prints the expression of a plain `TermInfo`.  It must
*not* be a constant or an fvar: when `location?` is `none`, Lean resolves go-to-definition
from the expression instead (`Lean.Server.locationLinksFromTermInfo`), so a `mkConst
``Unit`` here sends every ctrl+click in a Lait file to `Unit` in the prelude.  An
application is opaque to that fallback, and `strGadget`'s delaborator makes the infoview
popup show the Lait type rather than Lean internals. -/
def addHoverInfoDelab (stx : Syntax) (s : String)
    (loc? : Option DeclarationLocation := none) : MetaM Unit := do
  -- Declarations spliced in from another Lait module carry no source positions (see the
  -- `#include` case of `elabLaitDecl`), and a leaf without a range is never hoverable.
  if stx.getRange?.isNone then return
  withEnableInfoTree true do
    pushInfoLeaf <| .ofDelabTermInfo {
      elaborator := `Lait.addHoverInfo
      stx := stx
      lctx := (← getLCtx)
      expectedType? := none
      expr := mkApp (mkConst ``strGadget) (mkStrLit s)
      mkDocString? := some (fun _ => pure s!"`{s}`")
      location? := loc?
    }

def addHoverInfo (stx : Syntax) (s : String)
    (loc? : Option DeclarationLocation := none) : MetaM Unit :=
  addHoverInfoDelab stx s loc?

/-- Attach an info-tree leaf over `stx` that resolves "go to definition" to nothing.

Ctrl+clicking a part of a Lait declaration that carries no hover of its own -- a keyword,
`:=`, a comment -- otherwise resolves against the enclosing command's `CommandInfo`, and
`Lean.Server.locationLinksDefault` then offers that command's *elaborator*: the click lands
in Lait's own implementation.  This leaf has no target, and its `elaborator` field names no
real constant, so the fallback comes up empty too.

Leaves are preferred innermost-first and, among siblings, by smallest range
(`Lean.Server.HoverableInfoPrio`), so covering a whole declaration does not shadow the
hovers inside it.  It also carries no docstring, which makes `Info.fmtHover?` decline it,
so hovering a keyword still falls back to the docstring of its syntax. -/
def suppressGoToDefinition (stx : Syntax) : MetaM Unit := do
  if stx.getRange?.isNone then return
  withEnableInfoTree true do
    pushInfoLeaf <| .ofDelabTermInfo {
      elaborator := `Lait.addHoverInfo
      -- Only the range, not the tree: "go to declaration" additionally falls back to the
      -- *syntax declaration* of `Info.stx`'s kind, which would jump to the `syntax "type"
      -- ..." command in `Lait.Elab`.
      stx := stx.strip
      lctx := {}
      expectedType? := none
      expr := mkApp (mkConst ``strGadget) (mkStrLit "")
    }


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
