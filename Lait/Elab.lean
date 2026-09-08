import Lait.Surface
import Lait.Syntax
import Lait.FromSurface
import Lait.Eval
import Lait.Tc
import Lean
import Lean.EnvExtension

open Lean Elab Command

/-- One stored declaration of a Lait module: its syntax, plus the source location it was
written at.  The location is resolved when the declaration is stored, i.e. in the file that
defines it -- a module may be `#include`d from any other file, where the positions carried
by `stx` mean nothing (see the `#include` case of `elabLaitDecl`). -/
structure LaitStoredDecl where
  stx : TSyntax `lait_decl
  loc? : Option DeclarationLocation

/-- Entries *extend* the named module, so a module may be built up over several
commands (as a `#lait` file is: one command per top-level declaration). -/
initialize laitExt : SimplePersistentEnvExtension (Name × Array LaitStoredDecl) (NameMap (Array LaitStoredDecl)) ←
  registerSimplePersistentEnvExtension {
    -- applied to entries added in the current file
    addEntryFn    := fun m (n, s) => m.insert n ((m.find? n).getD #[] ++ s)
    -- applied once at import time to entries from all transitive imports
    addImportedFn := fun arrs =>
      arrs.foldl (fun m arr => arr.foldl (fun m (n, s) => m.insert n ((m.find? n).getD #[] ++ s)) m) {}
  }

def getModule (name : Name) : CoreM (Option (Array LaitStoredDecl)) := do
  return (laitExt.getState (← getEnv)).find? name

/-- Append `ds` to the declarations of the Lait module `name`. -/
def addModule (name : Name) (ds : Array LaitStoredDecl) : CoreM Unit := do
  modifyEnv (laitExt.addEntry · (name, ds))

/-- Results of the `#eval`s of each Lait module, keyed by module name.  Populated
as the module elaborates, so Lean code after it (or in an importing file) can read
the outputs back with `getEvalResults`.  As with `laitExt`, entries accumulate. -/
initialize laitEvalExt : SimplePersistentEnvExtension (Name × Array EvalResult) (NameMap (Array EvalResult)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := fun m (n, rs) => m.insert n ((m.find? n).getD #[] ++ rs)
    addImportedFn := fun arrs =>
      arrs.foldl (fun m arr => arr.foldl (fun m (n, rs) => m.insert n ((m.find? n).getD #[] ++ rs)) m) {}
  }

/-- Append `rs` to the recorded `#eval` results of the Lait module `name`. -/
def addEvalResults (name : Name) (rs : Array EvalResult) : CoreM Unit := do
  modifyEnv (laitEvalExt.addEntry · (name, rs))

/-- The `#eval` results of the Lait module `name`, in declaration order. -/
def getEvalResults (name : Name) : CoreM (Array EvalResult) := do
  return ((laitEvalExt.getState (← getEnv)).find? name).getD #[]

def getLastEvalResult (name : Name) : CoreM (Option EvalResult) := do
  return ((laitEvalExt.getState (← getEnv)).find? name).getD #[] |>.back?

declare_syntax_cat lait_ty

/--
The type of whole numbers: both negative and positive integers.
-/
syntax "Int" : lait_ty
/--
The type of booleans: either `true` or `false`.
You can use `if` to branch on a boolean value.
-/
syntax "Bool" : lait_ty
/--
The type of strings, written in quotes.
-/
syntax "String" : lait_ty
/--
The unit type, which has only one value: `()`.
-/
syntax "Unit" : lait_ty
/--
The type of functions: `t1 -> t2` means a function that takes an argument of type `t1` and returns a value of type `t2`.
Functions in Lait are _impure_, meaning that they can do things like access mutable state and throw errors.
-/
-- Right-associative and looser than `*`, as in ML: `a * b -> c -> d` is
-- `(a * b) -> (c -> d)`.
syntax:25 lait_ty:26 "->" lait_ty:25 : lait_ty
/--
The type of pairs: `t1 * t2` means a pair of values, one of type `t1` and one of type `t2`.
-/
-- Binds tighter than `->`, and right-associative: `a * b * c` is `a * (b * c)`, a pair
-- whose second component is a pair.
syntax:35 lait_ty:36 "*" lait_ty:35 : lait_ty
syntax "(" lait_ty ")" : lait_ty
syntax ident "<" lait_ty,* ">" : lait_ty
syntax ident : lait_ty
/--
The type of mutable references `Ref<t>` to values of type `t`.
- To create a new mutable reference of type `Ref<t>`, use `alloc e`, where `e` should have type `t`.
- To read from a mutable reference `r : Ref<t>`, use `get r`.
- To write to a mutable reference `r : Ref<t>`, use `set r e`, where `e` should have type `t`.

`alloc`, `get` and `set` are ordinary standard-library functions, defined in terms of
the primitives `builtin_alloc`, `builtin_get` and `builtin_set`.
-/
syntax "Ref" "<" lait_ty ">" : lait_ty

section LaitSurface

open Lean Parser


open Lean Elab Meta Command


def mkSurfaceTy (stx : Lean.Syntax) (x : Surface.TyX) : TermElabM Surface.Ty :=
  pure (.mk stx.strip x)

partial def firstCharUpper (i : Ident) : TermElabM _root_.Bool :=
  match (i.getId.toString.pos? 0).bind (·.get?) with
  | none => throwError "should be unreachable"
  | some c => pure c.isUpper

partial def elabLaitTy (t : Lean.TSyntax `lait_ty) : TermElabM Surface.Ty :=
  match t with
  | `(lait_ty | Int) => mkSurfaceTy t.raw .Int
  | `(lait_ty | Bool) => mkSurfaceTy t.raw .Bool
  | `(lait_ty | Unit) => mkSurfaceTy t.raw .Unit
  | `(lait_ty | String) => mkSurfaceTy t.raw .Str
  | `(lait_ty | $t1:lait_ty -> $t2:lait_ty) => do
      mkSurfaceTy t.raw (.Arrow (← elabLaitTy t1) (← elabLaitTy t2))
  | `(lait_ty | $t1:lait_ty * $t2:lait_ty) => do
      mkSurfaceTy t.raw (.Prod (← elabLaitTy t1) (← elabLaitTy t2))
  | `(lait_ty | ($t:lait_ty)) => elabLaitTy t
  | `(lait_ty | $id:ident < $ts:lait_ty,* > ) => do
      if <- firstCharUpper id then do
        let elabs <- ts.getElems.mapM elabLaitTy
        mkSurfaceTy t.raw (.TApp id.getId.toString elabs.toList)
      else  throwErrorAt t.raw "Cannot apply type arguments to a lower-case type variable"
  | `(lait_ty | $id:ident) => do
      if <- firstCharUpper id then do
        mkSurfaceTy t.raw (.TApp id.getId.toString [])
      else do
        mkSurfaceTy t.raw (.Var id.getId.toString)
  | `(lait_ty | Ref < $t:lait_ty >) => do
    mkSurfaceTy t.raw (.Ref (← elabLaitTy t))
  | _ => throwUnsupportedSyntax

elab "{lait_ty" t:lait_ty "}" : term => do
  return toExpr (← elabLaitTy t)


#check {lait_ty  Bool}
#check {lait_ty  Int}
-- Tick-prefixed type variables cannot appear raw in this `.lean` file (Lean's
-- lexer reads `'a` as a character literal). They are exercised in `Lait/Tests.lean`.


declare_syntax_cat lait_exp
declare_syntax_cat lait_match_arm
declare_syntax_cat lait_typed_var
declare_syntax_cat lait_param
declare_syntax_cat lait_ident

syntax "_" : lait_ident
syntax ident : lait_ident

syntax "(" lait_ident ":" lait_ty ")" : lait_typed_var

-- A function parameter: either typed `(x : T)`, an un-annotated name `x` (whose
-- type is inferred), or `()` as sugar for `(_ : Unit)`.
syntax lait_typed_var : lait_param
syntax lait_ident : lait_param
syntax "()" : lait_param

-- Use `"true"` not `&"true"`: the `&` prefix keeps the atom available to
-- `syntax lait_ident : lait_exp`, so `true`/`false` parse as variables instead.
syntax &"true" : lait_exp
syntax &"false" : lait_exp
syntax lait_ident : lait_exp
syntax "(" lait_exp ")" : lait_exp
syntax num : lait_exp
syntax:67 "-" num : lait_exp
syntax str : lait_exp
syntax "()" : lait_exp
syntax "..." : lait_exp
syntax "fun" lait_ident "=>" lait_exp : lait_exp
syntax "fun" lait_typed_var "=>" lait_exp : lait_exp
syntax:70 lait_exp:70 lait_exp:71 : lait_exp
syntax "let" lait_ident ":" lait_ty ":=" lait_exp "in" lait_exp : lait_exp
syntax "let" lait_ident ":=" lait_exp "in" lait_exp : lait_exp
syntax "error" lait_exp : lait_exp
syntax "internal_print" lait_exp : lait_exp
syntax "(" lait_exp "," lait_exp ")" : lait_exp
syntax:67 "fst" lait_exp:68 : lait_exp
syntax:67 "snd" lait_exp:68 : lait_exp
syntax:67 "not" lait_exp:68 : lait_exp
syntax "match" lait_exp "with" lait_match_arm* "end" : lait_exp
syntax "if" lait_exp "then" lait_exp "else" lait_exp : lait_exp
syntax "try" lait_exp "with" lait_exp "end" : lait_exp
-- The primitive operations on mutable references.  The stdlib wraps each as an
-- ordinary function, so `alloc`/`get`/`set` are plain identifiers rather than
-- reserved syntax:
--   alloc : forall a. a -> Ref<a>
--   get   : forall a. Ref<a> -> a
--   set   : forall a. Ref<a> -> a -> Unit
syntax "builtin_alloc" "(" lait_exp ")" : lait_exp
syntax "builtin_get" "(" lait_exp ")" : lait_exp
syntax "builtin_set" "(" lait_exp "," lait_exp ")" : lait_exp
-- Infix operators, stratified by precedence (all left-associative, and all
-- below `fst`/`snd`/`not` at 67 and application at 70 so those bind tighter):
--   *            62   (multiplication, tightest)
--   + ++         60   (additive)
--   < > <= >= == 55   (comparison / equality)
--   &&           50
--   ||           45   (loosest)
syntax:62 lait_exp:62 "*" lait_exp:63 : lait_exp
syntax:60 lait_exp:60 "+" lait_exp:61 : lait_exp
syntax:60 lait_exp:60 "-" lait_exp:61 : lait_exp
syntax:60 lait_exp:60 "++" lait_exp:61 : lait_exp
syntax:60 lait_exp:61 "::" lait_exp:60 : lait_exp
syntax:55 lait_exp:55 "<" lait_exp:56 : lait_exp
syntax:55 lait_exp:55 ">" lait_exp:56 : lait_exp
syntax:55 lait_exp:55 "<=" lait_exp:56 : lait_exp
syntax:55 lait_exp:55 ">=" lait_exp:56 : lait_exp
syntax:55 lait_exp:55 "==" lait_exp:56 : lait_exp
syntax:55 lait_exp:55 "!=" lait_exp:56 : lait_exp
syntax:50 lait_exp:50 "&&" lait_exp:51 : lait_exp
syntax:45 lait_exp:45 "||" lait_exp:46 : lait_exp
syntax "fix" lait_ident "." lait_exp : lait_exp
syntax "|" ident lait_ident* "=>" lait_exp : lait_match_arm
syntax "|" "[]" "=>" lait_exp : lait_match_arm
syntax "|" lait_ident "::" lait_ident "=>" lait_exp : lait_match_arm
syntax "|" "_" "=>" lait_exp : lait_match_arm
syntax "%" ident "{" lait_exp,* "}" : lait_exp
syntax "[]" : lait_exp
syntax "[" lait_exp,+ "]" : lait_exp

partial def elabLaitIdent (id : Lean.TSyntax `lait_ident) : TermElabM _root_.String :=
  match id with
  | `(lait_ident | _) => pure "_"
  | `(lait_ident | $id:ident) => pure id.getId.toString
  | _ => throwUnsupportedSyntax

partial def elabLaitTypedVar (a : Lean.TSyntax `lait_typed_var) : TermElabM (_root_.String × Surface.Ty) :=
  match a with
  | `(lait_typed_var | ($id:lait_ident : $t:lait_ty)) => do
    let ty ← elabLaitTy t
    let name ← elabLaitIdent id
    pure (name, ty)
  | _ => throwUnsupportedSyntax

-- A function parameter, yielding its name and an optional type annotation.
partial def elabLaitParam (a : Lean.TSyntax `lait_param) : TermElabM (_root_.String × Option Surface.Ty) :=
  match a with
  | `(lait_param | ()) => do
    pure ("_", some (← mkSurfaceTy a.raw .Unit))
  | `(lait_param | $tv:lait_typed_var) => do
    let (name, ty) ← elabLaitTypedVar tv
    pure (name, some ty)
  | `(lait_param | $id:lait_ident) => do
    let name ← elabLaitIdent id
    pure (name, none)
  | _ => throwUnsupportedSyntax

mutual
partial def mkSurfaceExp (stx : Lean.Syntax) (x : Surface.ExpX) : TermElabM Surface.Exp :=
  pure (.mk stx.strip x)

-- Build a binary `Op` node for one of the infix operators.
partial def mkLaitInfix (stx : Lean.Syntax) (op : _root_.String)
    (e1 e2 : Lean.TSyntax `lait_exp) : TermElabM Surface.Exp := do
  mkSurfaceExp stx (.Op op [← elabLaitExp e1, ← elabLaitExp e2])

partial def mkLaitUnary (stx : Lean.Syntax) (op : _root_.String)
    (e : Lean.TSyntax `lait_exp) : TermElabM Surface.Exp := do
  mkSurfaceExp stx (.Op op [← elabLaitExp e])

-- A constructor arm (`.inl`) or the catch-all wildcard arm (`.inr`).
partial def elabLaitMatchArm (a : Lean.TSyntax `lait_match_arm) : TermElabM (Sum (_root_.String × List _root_.String × Surface.Exp) Surface.Exp) :=
  match a with
  | `(lait_match_arm | | _ => $bdy:lait_exp) => do
    pure (.inr (<- elabLaitExp bdy))
  | `(lait_match_arm | | $c:ident $ids:lait_ident* => $bdy:lait_exp) => do
    let bdy <- elabLaitExp bdy
    let ids' ← ids.mapM elabLaitIdent
    if (ids'.toList.filter (· != "_")).hasDup then
      throwErrorAt a "Duplicate variables in pattern match"
    pure (.inl (c.getId.toString, ids'.toList, bdy))
  | `(lait_match_arm | | [] => $bdy:lait_exp) => do
    let bdy <- elabLaitExp bdy
    pure (.inl ("Nil", List.nil, bdy))
  | `(lait_match_arm | | $c:lait_ident :: $id:lait_ident => $bdy:lait_exp) => do
    let bdy <- elabLaitExp bdy
    let id' ← elabLaitIdent id
    let c' ← elabLaitIdent c
    pure (.inl ("Cons", [c', id'], bdy))
  | _ => throwUnsupportedSyntax

-- `[e1, ..., en]` is `Cons e1 (Cons ... Nil)`.  The spine is not written anywhere, so each
-- link is positioned over the stretch of the literal it stands for -- `[1, 2, 3]`, then
-- `2, 3]`, then `3]` -- rather than every link over the whole literal, which would stack
-- one hover per element on it, half of them the type of a half-applied `Cons`.  The
-- `Cons` itself, the half-application, and the final `Nil` correspond to nothing in the
-- source; they are collapsed to a point, which is too narrow for a hover to attach to but
-- still positions an error (`Cons` resolves against the environment, so it does fail --
-- "Variable Cons not found" -- in a block that never included the stdlib).
partial def elabLaitListExp (stx : Lean.Syntax) (es : List (Lean.TSyntax `lait_exp)) : TermElabM Surface.Exp :=
  match es with
  | List.nil => mkSurfaceExp stx (.Var "Nil")
  | List.cons e es => do
    let hd ← elabLaitExp e
    -- The tail runs from the next element to this node's own end, and after the last one
    -- collapses to the closing bracket.
    let tlStx := match es.head?.bind (·.raw.getRange?), stx.getRange? with
      | some r, some here => Lean.Syntax.ofRange ⟨r.start, here.stop⟩
      | none, some here => Lean.Syntax.ofRange ⟨here.stop, here.stop⟩
      | _, _ => .missing
    let tl ← elabLaitListExp tlStx es
    mkSurfaceExp stx $
       (.App (<- mkSurfaceExp stx.startMarker $
          .App (<- mkSurfaceExp stx.startMarker (.Var "Cons")) hd) tl)


partial def elabLaitExp (e : Lean.TSyntax `lait_exp) : TermElabM Surface.Exp :=
  match e with
  | `(lait_exp | true) =>
    mkSurfaceExp e.raw (.Const (.Bool Bool.true))
  | `(lait_exp | false) =>
    mkSurfaceExp e.raw (.Const (.Bool Bool.false))
  | `(lait_exp | $id:lait_ident) => do
    let name ← elabLaitIdent id
    mkSurfaceExp e.raw (.Var name)
  | `(lait_exp | ($e:lait_exp)) => elabLaitExp e
  | `(lait_exp | error $e1:lait_exp) => do
    mkSurfaceExp e.raw (.Error (← elabLaitExp e1))
  | `(lait_exp | ...) => do
    -- Built here rather than by re-elaborating a `(lait_exp| error ...)` quotation: a
    -- quotation's nodes are positioned at the elaborator's *ref*, which is the whole
    -- `{lait_decl …}` command, and `mkSurfaceExp` would then hang this expression's hover
    -- over the entire block.
    let msg ← match e.raw.getRange? with
      | none => pure "unimplemented"
      | some range =>
        let pos := (← getFileMap).toPosition range.start
        pure s!"unimplemented: {← getFileName}, Line {pos.line}, Column {pos.column}"
    -- The message is not written anywhere, so it is left position-less: hovering `...`
    -- reports the type of the `error`, not `String`.
    mkSurfaceExp e.raw (.Error (← mkSurfaceExp .missing (.Const (.String msg))))
  | `(lait_exp | internal_print $e1:lait_exp) => do
    mkSurfaceExp e.raw (.Print (← elabLaitExp e1))
  | `(lait_exp | $n:num) =>
    mkSurfaceExp e.raw (.Const (.Num (Int.ofNat n.getNat)))
  | `(lait_exp | - $n:num) =>
    mkSurfaceExp e.raw (.Const (.Num (- (Int.ofNat n.getNat))))
  | `(lait_exp | $s:str) =>
    mkSurfaceExp e.raw (.Const (.String s.getString))
  | `(lait_exp | ()) =>
    mkSurfaceExp e.raw (.Const .Unit)
  | `(lait_exp | if $e1:lait_exp then $e2:lait_exp else $e3:lait_exp) => do
    mkSurfaceExp e.raw (.If (← elabLaitExp e1) (← elabLaitExp e2) (← elabLaitExp e3))
  | `(lait_exp | try $e1:lait_exp with $e2:lait_exp end) => do
    mkSurfaceExp e.raw (.Try (← elabLaitExp e1) (← elabLaitExp e2))
  | `(lait_exp | fun $id:lait_ident => $e1:lait_exp) => do
    let name ← elabLaitIdent id
    mkSurfaceExp e.raw (.Lam name none (← elabLaitExp e1))
  | `(lait_exp | fun $tv:lait_typed_var => $e1:lait_exp) => do
    let (name, ty) <- elabLaitTypedVar tv
    mkSurfaceExp e.raw (.Lam name (some ty) (← elabLaitExp e1))
  | `(lait_exp | $e1:lait_exp $e2:lait_exp) => do
    mkSurfaceExp e.raw (.App (← elabLaitExp e1) (← elabLaitExp e2))
  | `(lait_exp | % $id:ident {$es:lait_exp,*}) => do
    let es <- es.getElems.mapM elabLaitExp
    mkSurfaceExp e.raw (.Op id.getId.toString es.toList)
  | `(lait_exp | let $id:lait_ident : $t:lait_ty := $e1:lait_exp in $e2:lait_exp) => do
    let name ← elabLaitIdent id
    let ty ← elabLaitTy t
    let val ← elabLaitExp e1
    let body ← elabLaitExp e2
    mkSurfaceExp e.raw (.Let name (some ty) val body)
  | `(lait_exp | let $id:lait_ident := $e1:lait_exp in $e2:lait_exp) => do
    let name ← elabLaitIdent id
    let val ← elabLaitExp e1
    let body ← elabLaitExp e2
    mkSurfaceExp e.raw (.Let name none val body)
  | `(lait_exp | ($e1:lait_exp, $e2:lait_exp)) => do
    mkSurfaceExp e.raw (.Pair (← elabLaitExp e1) (← elabLaitExp e2))
  | `(lait_exp | builtin_alloc($e1:lait_exp)) => do
    mkSurfaceExp e.raw (.Alloc (← elabLaitExp e1))
  | `(lait_exp | builtin_get($e1:lait_exp)) => do
    mkSurfaceExp e.raw (.Deref (← elabLaitExp e1))
  | `(lait_exp | builtin_set($e1:lait_exp, $e2:lait_exp)) => do
    mkSurfaceExp e.raw (.Assign (← elabLaitExp e1) (← elabLaitExp e2))
  | `(lait_exp | $e1:lait_exp * $e2:lait_exp) => mkLaitInfix e.raw "*" e1 e2
  | `(lait_exp | $e1:lait_exp + $e2:lait_exp) => mkLaitInfix e.raw "+" e1 e2
  | `(lait_exp | $e1:lait_exp - $e2:lait_exp) => mkLaitInfix e.raw "-" e1 e2
  | `(lait_exp | not $e1:lait_exp) => mkLaitUnary e.raw "not" e1
  | `(lait_exp | $e1:lait_exp ++ $e2:lait_exp) => mkLaitInfix e.raw "++" e1 e2
  | `(lait_exp | $e1:lait_exp :: $e2:lait_exp) => do
    -- Only the whole `e1 :: e2` is written; the `Cons` it applies and the half-application
    -- in between are not, and positioning them here too would put three hovers on the same
    -- range -- two of them types of a `Cons` that appears nowhere in the source.  They are
    -- collapsed to a point rather than dropped, as in `elabLaitListExp`, so that an
    -- unresolved `Cons` is still reported here.
    mkSurfaceExp e.raw $
      .App (<- mkSurfaceExp e.raw.startMarker $
         .App (<- mkSurfaceExp e.raw.startMarker (.Var "Cons")) (<- elabLaitExp e1))
         (<- elabLaitExp e2)
  | `(lait_exp | [] ) => mkSurfaceExp e.raw (.Var "Nil")
  | `(lait_exp | [$es:lait_exp,*]) => do
     elabLaitListExp e.raw es.getElems.toList
  | `(lait_exp | $e1:lait_exp < $e2:lait_exp) => mkLaitInfix e.raw "<" e1 e2
  | `(lait_exp | $e1:lait_exp > $e2:lait_exp) => mkLaitInfix e.raw ">" e1 e2
  | `(lait_exp | $e1:lait_exp <= $e2:lait_exp) => mkLaitInfix e.raw "<=" e1 e2
  | `(lait_exp | $e1:lait_exp >= $e2:lait_exp) => mkLaitInfix e.raw ">=" e1 e2
  | `(lait_exp | $e1:lait_exp == $e2:lait_exp) => mkLaitInfix e.raw "==" e1 e2
  | `(lait_exp | $e1:lait_exp != $e2:lait_exp) => do
     -- `not (e1 == e2)`, built directly so that both nodes are positioned at `e1 != e2`.
     -- Going through a quotation positions them at the elaborator's ref instead -- the
     -- whole `{lait_decl …}` command -- which puts a `Bool` hover over the entire block.
     mkSurfaceExp e.raw (.Op "not" [← mkLaitInfix e.raw "==" e1 e2])
  | `(lait_exp | $e1:lait_exp && $e2:lait_exp) => mkLaitInfix e.raw "&&" e1 e2
  | `(lait_exp | $e1:lait_exp || $e2:lait_exp) => mkLaitInfix e.raw "||" e1 e2
  | `(lait_exp | fst $e2:lait_exp) => do
    mkSurfaceExp e.raw (.Fst (← elabLaitExp e2))
  | `(lait_exp | snd $e1:lait_exp) => do
    mkSurfaceExp e.raw (.Snd (← elabLaitExp e1))
  | `(lait_exp | fix $id:lait_ident . $e1:lait_exp) => do
    let name ← elabLaitIdent id
    mkSurfaceExp e.raw (.Rec name (← elabLaitExp e1))
  | `(lait_exp | match $e1:lait_exp with $arms:lait_match_arm* end) => do
      let scrut ← elabLaitExp e1
      let args <- arms.mapM elabLaitMatchArm
      -- Split off the catch-all wildcard, which we require to be the last arm.
      let mut ctorArms : Array (_root_.String × List _root_.String × Surface.Exp) := #[]
      let mut owild : Option Surface.Exp := none
      for arm in args do
        if owild.isSome then
          throwErrorAt e "Wildcard pattern must be the last arm of a match"
        match arm with
        | .inl c => ctorArms := ctorArms.push c
        | .inr w => owild := some w
      mkSurfaceExp e.raw (.Match scrut ctorArms.toList owild)
  | _ => throwUnsupportedSyntax
end

elab "{lait_exp" e:lait_exp "}" : term => do
  return toExpr (← elabLaitExp e)


/-
#check {lait_exp  true}
#check {lait_exp  false}
#check {lait_exp  42}
#check {lait_exp  fun x => x}
#check {lait_exp  fun (x : Int) => x}
#check {lait_exp  (1, 2)}
#check {lait_exp  ()}
#check {lait_exp  let x := 1 in x}
#check {lait_exp  let x : Int := 1 in x}
#check {lait_exp  (fun x => x) 1}
#check {lait_exp  builtin_alloc(1)}
#check {lait_exp  builtin_get(x)}
#check {lait_exp  builtin_set(x, 1)}
-/

end LaitSurface


declare_syntax_cat lait_decl
declare_syntax_cat lait_inductive_constr

declare_syntax_cat lait_def_kw
declare_syntax_cat lait_type_kw

/--
Define a top-level value or function.
- `def x := e` binds `x` to the value of `e`; an optional type may be given with `def x : T := e`.
- `def f param_1 ... param_n := e` defines a function. Each `param` is either a bare identifier (e.g., `x`);
an identifier annotated with a type `(x : T)`, or `()` (standing for a parameter of type `Unit`).
- You can create mutually recursive functions using `and`, like so:
```
def isEven (n : Int) :=
  if n == 0 then true else isOdd (n - 1)
and isOdd (n : Int) :=
  if n == 0 then false else isEven (n - 1)
```
-/
syntax "def" : lait_def_kw

/--
Define a type.
Some examples:

```
type IntPair := Int * Int

type MyPair<a> := a * a

type NatTree :=
  | NTLeaf (v : Int)
  | NTNode (l : NatTree) (r : NatTree)

type BinTree<a> :=
  | BTLeaf (v : a)
  | BTNode (l : BinTree<a>) (r : BinTree<a>)
```

A type with exactly one constructor also gets a field accessor for each of that
constructor's named arguments.  For example

```
type Point := | MkPoint (x : Int) (y : Int)
```

defines `Point.x : Point -> Int` and `Point.y : Point -> Int` alongside `MkPoint`.
An argument named `_` gets no accessor.
-/
syntax "type" : lait_type_kw


syntax lait_def_kw lait_ident ":=" lait_exp : lait_decl

syntax lait_def_kw lait_ident ":" lait_ty ":=" lait_exp : lait_decl
syntax lait_type_kw ident ":=" lait_ty : lait_decl
syntax lait_type_kw ident "<" ident,* ">" ":=" lait_ty : lait_decl

-- Function and (inductive) type definitions.  Two or more clauses linked with
-- `and` form a mutually-recursive group; a single clause (no `and`) is the
-- ordinary case.  Folding both into one rule avoids parser ambiguity with a
-- separate `and`-only rule sharing the `def`/`type` prefix.
declare_syntax_cat lait_and_def
declare_syntax_cat lait_and_type
syntax "and" lait_ident lait_param+ (":" lait_ty)? ":=" lait_exp : lait_and_def

syntax lait_def_kw lait_ident lait_param+ (":" lait_ty)? ":=" lait_exp lait_and_def* : lait_decl
syntax "and" ident ("<" ident,* ">")? ":=" lait_inductive_constr* : lait_and_type
syntax lait_type_kw ident ("<" ident,* ">")? ":=" lait_inductive_constr* lait_and_type* : lait_decl

syntax "|" ident lait_typed_var* : lait_inductive_constr
/--
Evaluate a Lait expression.
The syntax is `#eval e` where `e` is the expression to evaluate.
-/
syntax "#eval" lait_exp : lait_decl
/--
Evaluate a test for equality between two expressions. The syntax is `#test e1 === e2` (note the use of three equal signs).
-/
syntax "#test" lait_exp "===" lait_exp : lait_decl
/--
Evaluate an expression and succeed if the given expression fails.
The syntax is `#test_error e ~ s`, where `e` is our given expression, and `s` is the expected string output by `error`.
-/
syntax "#test_error" lait_exp "~" str : lait_decl
/--
Check and expression to see its type.
The syntax is `#check e`.
-/
syntax "#check" lait_exp : lait_decl
/--
Include a Lait module. The most common use case is `#include stdlib`.
-/
syntax "#include" ident : lait_decl

open Lean Elab Meta

def mkSurfaceDeclEntry (stx : Lean.Syntax) (x : Surface.DeclEntryX) : TermElabM Surface.DeclEntry :=
  pure ⟨stx.strip, x⟩

partial def elabLaitDefClause (stx : Syntax) (id : Lean.TSyntax `lait_ident)
    (args : Array (Lean.TSyntax `lait_param)) (t : Option (Lean.TSyntax `lait_ty))
    (e : Lean.TSyntax `lait_exp) :
    TermElabM (Lean.Syntax × _root_.String × List (_root_.String × Option Surface.Ty) × Option Surface.Ty × Surface.Exp) := do
  let name ← elabLaitIdent id
  let args ← args.mapM elabLaitParam
  let ty ← t.mapM elabLaitTy
  let body ← elabLaitExp e
  pure (stx, name, args.toList, ty, body)

partial def elabLaitInductiveConstr (c : Lean.TSyntax `lait_inductive_constr) : TermElabM (Ident × List (_root_.String × Surface.Ty)) :=
  match c with
  | `(lait_inductive_constr | | $id:ident $args:lait_typed_var*) => do
    let args ← args.mapM elabLaitTypedVar
    pure (id, args.toList)
  | _ => throwUnsupportedSyntax

-- The `(name, tvars, constructors)` tuple for one inductive type.
partial def elabLaitInductiveTuple (id : Ident) (tvars : List Ident) (cs : TSyntaxArray `lait_inductive_constr) :
    TermElabM (_root_.String × List _root_.String × List (_root_.String × List (_root_.String × Surface.Ty))) := do
    let cs ← cs.mapM elabLaitInductiveConstr
    let cs' := cs.toList.map fun (cname, args) => (cname.getId.toString, args)
    pure (id.getId.toString, tvars.map (·.getId.toString), cs')

/-- What `#include` accumulates while a command elaborates. -/
structure IncludeState where
  /-- The Lait modules already spliced in, making `#include` idempotent; see the
  `#include` case of `elabLaitDecl`. -/
  included : NameSet := {}
  /-- Where each spliced-in top-level name was defined; see `TcEnv.defLocs`. -/
  defLocs : Std.TreeMap _root_.String DeclarationLocation := {}

partial def elabLaitDecl (st : IO.Ref IncludeState) (d : Lean.TSyntax `lait_decl) :
    TermElabM Surface.DeclEntry := do
  -- Covers the parts of the declaration that get no hover of their own, so that clicking
  -- them does not jump into Lait's implementation.  Declarations spliced in by `#include`
  -- have no positions here and are skipped.
  suppressGoToDefinition d.raw
  match d with
  | `(lait_decl | def $id:lait_ident := $e:lait_exp) => do
    let name ← elabLaitIdent id
    let e ← elabLaitExp e
    mkSurfaceDeclEntry id.raw (.DeclEntryDef name none e)
  | `(lait_decl | def $id:lait_ident : $t:lait_ty := $e:lait_exp) => do
    let name ← elabLaitIdent id
    let ty ← elabLaitTy t
    let e ← elabLaitExp e
    mkSurfaceDeclEntry id.raw (.DeclEntryDef name (some ty) e)
  | `(lait_decl | def $id:lait_ident $args:lait_param* $[: $t:lait_ty]? := $e:lait_exp $ands:lait_and_def*) => do
    let first ← elabLaitDefClause id.raw id args t e
    let rest ← ands.mapM fun a => match a with
      | `(lait_and_def | and $id:lait_ident $args:lait_param* $[: $t:lait_ty]? := $e:lait_exp) =>
          elabLaitDefClause id.raw id args t e
      | _ => throwUnsupportedSyntax
    mkSurfaceDeclEntry id.raw (.DeclEntryDefMutual (first :: rest.toList))
  | `(lait_decl | type $id:ident := $t:lait_ty) => do
    if Bool.not (<- firstCharUpper id) then do throwErrorAt d.raw "Declared types must begin with an upper-case letter"
    let ty ← elabLaitTy t
    mkSurfaceDeclEntry d.raw (.DeclEntryTypeAlias id.getId.toString List.nil ty)
  | `(lait_decl | type $id:ident < $ts:ident,* > := $t:lait_ty) => do
    if Bool.not (<- firstCharUpper id) then do throwErrorAt d.raw "Declared types must begin with an upper-case letter"
    if (<- ts.getElems.toList.anyM firstCharUpper) then do throwErrorAt d.raw "Type parameters must begin with a lower-case letter"
    let ty ← elabLaitTy t
    let tvars := ts.getElems.toList.map fun id => id.getId.toString
    mkSurfaceDeclEntry d.raw (.DeclEntryTypeAlias id.getId.toString tvars ty)
  | `(lait_decl | type $id:ident $[< $ts:ident,* >]? := $cs:lait_inductive_constr* $ands:lait_and_type*) => do
    let elabClause (stx : Syntax) (id : Ident) (ts : Option (Lean.Syntax.TSepArray `ident ","))
        (cs : TSyntaxArray `lait_inductive_constr) :
        TermElabM (_root_.String × List _root_.String × List (_root_.String × List (_root_.String × Surface.Ty))) := do
      if Bool.not (<- firstCharUpper id) then throwErrorAt stx "Declared types must begin with an upper-case letter"
      let tvars := (ts.map (·.getElems.toList)).getD List.nil
      if (<- tvars.anyM firstCharUpper) then throwErrorAt stx "Type parameters must begin with a lower-case letter"
      elabLaitInductiveTuple id tvars cs
    let first ← elabClause d.raw id ts cs
    let rest ← ands.mapM fun a => match a with
      | `(lait_and_type | and $id:ident $[< $ts:ident,* >]? := $cs:lait_inductive_constr*) =>
          elabClause a id ts cs
      | _ => throwUnsupportedSyntax
    let tys := first :: rest.toList
    let ind ← mkSurfaceDeclEntry d.raw (.DeclEntryMutualTypes tys)
    -- Every type in the group that has exactly one constructor also gets a field
    -- accessor per named constructor argument.  They are emitted after the whole
    -- group, so an accessor whose result type is a sibling still resolves.
    let getters := tys.flatMap fun (tname, tvs, cs) =>
      match cs with
      | [(cname, args)] => Surface.DeclEntry.mkGetters d.raw tname tvs cname args
      | _ => List.nil
    mkSurfaceDeclEntry d.raw (.DeclList (ind :: getters))
  | `(lait_decl | #eval $e:lait_exp) => do
    let e ← elabLaitExp e
    mkSurfaceDeclEntry d.raw (.DeclEval e)
  | `(lait_decl | #test $e:lait_exp === $e2:lait_exp) => do
    let e ← elabLaitExp e
    let e2 ← elabLaitExp e2
    mkSurfaceDeclEntry d.raw (.DeclTest e e2)
  | `(lait_decl | #test_error $e:lait_exp ~ $s:str) => do
    let e ← elabLaitExp e
    mkSurfaceDeclEntry d.raw (.DeclTestError e s.getString)
  | `(lait_decl | #check $e:lait_exp) => do
    let e ← elabLaitExp e
    mkSurfaceDeclEntry d.raw (.DeclCheck e)
  | `(lait_decl | #include $e:ident) => do
    -- `#include` is idempotent: a module that has already been spliced into the
    -- module being elaborated contributes nothing the second time.  Without this,
    -- a diamond (`#include stdlib` together with `#include M`, where `M` itself
    -- includes `stdlib`) would re-declare stdlib's types and be rejected as a
    -- duplicate definition.
    let m := e.getId
    if (<- st.get).included.contains m then
      mkSurfaceDeclEntry d.raw (.DeclList List.nil)
    else
      match (<- getModule m) with
      | some ds => do
         -- Marked as included *before* recursing, so an include cycle terminates.
         st.modify fun s => { s with included := s.included.insert m }
         let ds <- ds.toList.mapM fun sd => do
           -- The stored syntax was written in another file, so its positions are
           -- meaningless here; `sd.loc?` is the real source location of the declaration.
           let entry <- elabLaitDecl st ⟨sd.stx.raw.clearSourceInfo⟩
           if let some loc := sd.loc? then
             -- `insertIfNew`, because a nested `#include` recorded the locations of the
             -- module it spliced in during the recursive call above; those are the real
             -- definition sites, not this `#include` line.
             st.modify fun s =>
               { s with defLocs := entry.definedNames.foldl (·.insertIfNew · loc) s.defLocs }
           pure entry
         mkSurfaceDeclEntry d.raw (.DeclList ds)
      | none => throwErrorAt e.raw s!"unknown lait module `{m}`"
  | _ => throwUnsupportedSyntax

/-- Separate syntax category for `#enable_lait`.  A `lait_module` is a *single*
`lait_decl`, so each top-level declaration parses as its own command — editing
one declaration only re-elaborates that command onward (see `LaitCtx`). -/
declare_syntax_cat lait_module
syntax (name := laitModuleDecl) lait_decl : lait_module

/-- Collect `lait_decl` nodes from a `categoryParser `lait_module` result. -/
partial def collectLaitModuleDecls (stx : Syntax) : List Syntax :=
  if stx.isOfKind `laitModuleDecl || stx.isOfKind `lait_module || stx.isOfKind nullKind then
    stx.getArgs.toList.foldl (fun acc arg => acc ++ collectLaitModuleDecls arg) List.nil
  else
    [stx]

/-- Accumulated Lait elaboration context, threaded across top-level commands via
`laitCtxExt`.  Because it lives in an `EnvExtension`, it is captured per command
snapshot: editing a command rewinds subsequent commands to that command's stored
context, so each declaration can be checked/run independently and incrementally.
`n` is the de Bruijn depth; `hvars` keeps the surface-name list in sync with it. -/
structure LaitCtx where
  n : Nat
  vars : List _root_.String
  hvars : vars.length = n
  /-- The accumulated top-level bindings; see `TcEnv.vars`. -/
  vars' : Vec n VarInfo
  opMap : Std.TreeMap _root_.String OpSig
  tyMap : Std.TreeMap _root_.String TyVal
  frozen : Lean.NameSet
  freshCounter : Nat
  evalEnv : List Val
  evalState : EvalState
  /-- Lait modules already spliced in by `#include`.  Accumulates across the
  commands of a `#lait` file, so that `#include M` in a later command skips a
  module the file already pulled in (e.g. the `stdlib` that `#lait` includes). -/
  included : Lean.NameSet
  /-- Where each accumulated top-level name was defined, for "go to definition"; see
  `TcEnv.defLocs`.  Like `included`, accumulates across the commands of a `#lait` file. -/
  defLocs : Std.TreeMap _root_.String DeclarationLocation

instance : Inhabited LaitCtx where
  default :=
    { n := 0, vars := List.nil, hvars := rfl, vars' := Vec.nil
      opMap := initTcOpMap, tyMap := initTyMap, frozen := {}
      freshCounter := 0, evalEnv := List.nil, evalState := EvalState.new
      included := {}, defLocs := {} }

initialize laitCtxExt : EnvExtension LaitCtx ← registerEnvExtension (pure default)

/-- Type-check and evaluate one batch of surface declarations starting from the
accumulated `ctx`, returning the extended context. -/
def processBatch (ctx : LaitCtx) (ds : List Surface.DeclEntry) : CommandElabM LaitCtx := do
  withEnableInfoTree Bool.false do
    let ds := Surface.DeclEntry.doAllPasses ds
    let ⟨vars', decl⟩ ← Decl.fromSurface ds ctx.vars
    let decl' : Decl ctx.n vars'.length := ctx.hvars ▸ decl
    let startEnv : TcEnv ctx.n :=
      { opMap := ctx.opMap, tyMap := ctx.tyMap, curSyntax := (← getRef)
        frozen := ctx.frozen, vars := ctx.vars'
        defLocs := ctx.defLocs, tyVarScope := {}
        -- `vars` is exactly the list of top-level `def` names accumulated so
        -- far, so the type checker's uniqueness check needs no extra state
        -- beyond the language's built-in names.
        defNames := ctx.vars.foldl (fun s v => s.insert v) initDefNames }
    -- The continuation runs at the final depth, so it sees the fully-extended
    -- typing environment (all defs/types of this batch in scope).
    let capture : Check vars'.length
        (Vec vars'.length VarInfo × Std.TreeMap _root_.String OpSig ×
          Std.TreeMap _root_.String TyVal × Lean.NameSet) := do
      let e ← read
      pure (e.vars, e.opMap, e.tyMap, e.frozen)
    let ((vi, om, tm, fr), st) ← liftTermElabM <|
      ((Decl.check decl' capture).run startEnv).run { freshCounter := ctx.freshCounter }
    let (evalEnv', evalState') ← liftTermElabM <| Decl.runFrom decl ctx.evalEnv ctx.evalState
    pure { n := vars'.length, vars := vars', hvars := rfl, vars' := vi
           opMap := om, tyMap := tm, frozen := fr
           freshCounter := st.freshCounter
           evalEnv := evalEnv', evalState := evalState', included := ctx.included
           defLocs := ctx.defLocs }

/-- Package the declarations of the command being elaborated for `laitExt`, resolving each
one's source location in the file that is being elaborated now. -/
def mkStoredDecls (ds : Array (TSyntax `lait_decl)) : CommandElabM (Array LaitStoredDecl) := do
  let mod ← getMainModule
  ds.mapM fun d => do pure { stx := d, loc? := ← mkStartLocation? mod d.raw }

/-- Record a failed elaboration of module `name` as an `.error` result, so that
Lean code reading the module's outputs back (`getEvalResults`,
`getLastEvalResult`) sees the error instead of a silently missing result.  A
declaration that fails to elaborate or type-check never runs, so it produces no
`#eval` output of its own; its error takes that slot. -/
def recordModuleError (name : Name) (e : Exception) : CommandElabM _root_.Unit := do
  let ref ← match e with
    | .error ref _ => pure ref
    | _ => getRef
  let msg ← e.toMessageData.toString
  liftCoreM <| addEvalResults name #[⟨ref, .error msg⟩]

elab "{lait_decl" i:ident d:lait_decl* "}" : command => do
  -- Unlike a `#lait` file (whose declarations extend its module one command at a
  -- time), a `{lait_decl …}` block defines its module in one shot, so a name that
  -- is already taken -- here or in an import -- is a genuine duplicate definition.
  if (← liftCoreM <| getModule i.getId).isSome then
    throwErrorAt i s!"Module `{i.getId}` already exists"
  try
    -- A self-contained module also starts from an empty set of includes.
    let (ds, ist) ← liftTermElabM do
      let st ← IO.mkRef ({} : IncludeState)
      let ds ← d.mapM (elabLaitDecl st)
      return (ds, ← st.get)
    -- A `{lait_decl …}` block is a self-contained module: check/run it from a
    -- fresh context, then store its raw syntax for later `#include` and the
    -- `#eval` results it produced for later inspection from Lean.
    let ctx ← processBatch { (default : LaitCtx) with defLocs := ist.defLocs } ds.toList
    liftCoreM <| addModule i.getId (← mkStoredDecls d)
    liftCoreM <| addEvalResults i.getId ctx.evalState.evalResults
  catch e =>
    recordModuleError i.getId e
    throw e

/-- Walk a parsed Lait command and attach a (deliberately unhandled) `namespaceId`
completion info over every identifier token.

The Lean language server falls back to a *synthetic identifier completion* whenever the
cursor sits on an `ident` token and there is no better `CompletionInfo` nearby; it then
offers all of Lean's global names. Inside Lait code (e.g. while typing `def foo`) those
suggestions are meaningless. Supplying our own `CompletionInfo` over each identifier
pre-empts that fallback, and the `namespaceId` kind is not handled by the completion
collector, so it resolves to an empty list — i.e. no completions at all. -/
partial def suppressLeanCompletions (stx : Syntax) : CommandElabM _root_.Unit := do
  match stx with
  | .ident .. => pushInfoLeaf (.ofCompletionInfo (.namespaceId stx))
  | .node _ _ args => args.forM suppressLeanCompletions
  | _ => pure ⟨⟩

/-- The Lait module name of the file being elaborated: the last component of the
Lean module name, so the top-level declarations of `Lait/Examples/Tests1.lean`
form the module `Tests1` and are reachable as `#include Tests1`. -/
def currentLaitModule : CommandElabM Name := do
  match ← getMainModule with
  | .str _ s => return .mkSimple s
  | m => return m

@[command_elab laitModuleDecl]
def elabLaitModuleTop : CommandElab := fun stx => do
  -- Attach empty completions over every identifier first, so they survive even when the
  -- declaration is still being typed and elaboration below fails.
  suppressLeanCompletions stx
  try
    let decls := collectLaitModuleDecls stx
    let ctx := laitCtxExt.getState (← getEnv)
    -- Includes are tracked per file, not per command, so a module pulled in by an
    -- earlier command of this file is not spliced in again by this one.
    let (ds, ist) ← liftTermElabM do
      let st ← IO.mkRef { included := ctx.included, defLocs := ctx.defLocs : IncludeState }
      let ds ← decls.mapM fun d => elabLaitDecl st ⟨d⟩
      return (ds, ← st.get)
    let ctx' ← processBatch { ctx with included := ist.included, defLocs := ist.defLocs } ds
    modifyEnv (laitCtxExt.setState · ctx')
    -- The file's top-level declarations form a Lait module named after the file, just
    -- like the ones written with `{lait_decl …}`: record this command's syntax and the
    -- `#eval` results it produced, so both can be read back later (`#include`,
    -- `getEvalResults`).  Each command extends the module in place.
    let modName ← currentLaitModule
    liftCoreM <| addModule modName (← mkStoredDecls (decls.toArray.map (⟨·⟩)))
    liftCoreM <| addEvalResults modName
      (ctx'.evalState.evalResults.extract ctx.evalState.evalResults.size)
  catch e =>
    -- A half-typed declaration makes `elabLaitDecl` `throwUnsupportedSyntax`, which would
    -- otherwise make the command framework reset the elaboration state and discard the
    -- completion leaves we just pushed. The parser already reports the syntax error, so we
    -- swallow that case; all other exceptions are recorded as a failing result of the
    -- file's module, then propagate normally (and keep the leaves).
    match e with
    | .internal id _ => if id == unsupportedSyntaxExceptionId then pure ⟨⟩ else throw e
    | _ =>
      recordModuleError (← currentLaitModule) e
      throw e

--- Parser override

-- Borrowed from Sigil

open Lean Elab Command Parser

public meta initialize originalCommandParserExt : EnvExtension (Name → ParserFn) ←
  registerEnvExtension (pure fun _ _ s => s)

/-- Replaces the parser for a syntax category -/
public meta def replaceCategoryParser (cat : Name) (p : ParserFn) : CommandElabM _root_.Unit :=
  modifyEnv (categoryParserFnExtension.modifyState · fun st =>
    fun n => if n == cat then p else st n)

meta def laitCommandParser : ParserFn := ((categoryParser `lait_module 0).fn · ·)

/--
This command enables the Lait language.
-/
syntax (name := enableDsl) "#lait_enable" : command

@[command_elab enableDsl]
public meta def elabEnableDsl : CommandElab := fun _stx => do
  modifyEnv fun env =>
    originalCommandParserExt.setState env (categoryParserFnExtension.getState env)
  replaceCategoryParser `command laitCommandParser

elab "#lait" : command => do
  elabCommand (← `(command | delete_token ">>"))
  elabCommand (← `(command| #lait_enable))
  let stdlibId := mkIdentFrom (← getRef) `stdlib
  let includeStx ← `(lait_decl| #include $stdlibId:ident)
  elabLaitModuleTop includeStx



--- Lait completions

/- The Lait elaborator deliberately produces no Lean completions (see
`suppressLeanCompletions`). Instead we provide our own completions sourced from the
accumulated `LaitCtx`: the in-scope term names (functions/values/constructors, with their
inferred types) and the in-scope type names. We do this by *chaining* the standard
`textDocument/completion` handler — when the cursor is inside a Lait command we replace its
(empty) result with Lait completions, otherwise we pass the original result through. -/

section LaitCompletion
open Lean Server Lsp Elab

/-- Completion items for the names recorded in a `LaitCtx`. `vars`/`varMap` are both ordered
by de Bruijn index, so zipping pairs each surface name with its inferred type scheme. Names
are de-duplicated, keeping the innermost (most recent) binding of each shadowed name.

Every item carries a `data?` field (uri + request position): clients send a
`completionItem/resolve` for each selected item, and the resolve router panics on items that
lack it. We only fill in `uri`/`pos` (no `id?`), so resolution is a no-op and the
pre-computed `detail?` is shown as-is. -/
def laitCompletionItems (ctx : LaitCtx) (uri : DocumentUri) (pos : Lsp.Position) :
    Array ResolvableCompletionItem := Id.run do
  let data : ResolvableCompletionItemData := { uri, pos }
  let mut items : Array ResolvableCompletionItem := #[]
  let mut seen : List _root_.String := List.nil
  for (name, info) in ctx.vars.zip ctx.vars'.val do
    unless name == "_" || seen.contains name do
      seen := name :: seen
      items := items.push
        { label := name, detail? := some info.scheme.pretty, kind? := some .«variable»,
          data? := some data }
  for tname in ctx.tyMap.keys do
    unless seen.contains tname do
      seen := tname :: seen
      items := items.push { label := tname, kind? := some .«class», data? := some data }
  return items

/-- Chained `textDocument/completion` handler: inside a Lait command, offer completions from
the in-scope Lait names; everywhere else, defer to the original handler's result. -/
def laitCompletionHandler (_params : CompletionParams)
    (prev : RequestTask ResolvableCompletionList) :
    RequestM (RequestTask ResolvableCompletionList) := do
  let doc ← RequestM.readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos _params.position
  RequestM.bindWaitFindSnap doc (fun s => s.endPos >= pos)
    (notFoundX := pure prev)
    fun snap => do
      if snap.stx.isOfKind ``laitModuleDecl then
        let items := laitCompletionItems (laitCtxExt.getState snap.env) doc.meta.uri _params.position
        pure <| .pure { isIncomplete := false, items }
      else
        pure prev

initialize
  chainLspRequestHandler "textDocument/completion"
    CompletionParams ResolvableCompletionList laitCompletionHandler

end LaitCompletion
