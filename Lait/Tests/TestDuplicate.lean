import Lait.Elab
import Lait.Stdlib

-- Top-level names are unique: a `def` may not re-define an existing `def`, and a
-- `type` may not re-declare an existing type.  Local binders are unaffected.

/-- error: foo is already defined -/
#guard_msgs in
{lait_decl dupDef
  def foo := 1
  def foo := 2
}

/-- error: f is already defined -/
#guard_msgs in
{lait_decl dupDefMutual
  def f (x : Int) : Int := x
  and f (y : Int) : Int := y
}

-- The duplicate is reported even though the body would not type-check either.
/-- error: bad is already defined -/
#guard_msgs in
{lait_decl dupDefIllTyped
  def bad := 1
  def bad := 1 + true
}

-- A constructor's generated function counts as a top-level def.
/-- error: C is already defined -/
#guard_msgs in
{lait_decl dupCtorDef
  type T := | C (x : Int)
  def C := 3
}

/-- error: Type Tree is already defined -/
#guard_msgs in
{lait_decl dupType
  type Tree := | Leaf
  type Tree := | Branch
}

/-- error: Type Alias is already defined -/
#guard_msgs in
{lait_decl dupTypeAlias
  type Alias := Int
  type Alias := Bool
}

-- Names arriving via `#include` are just as taken as locally declared ones.
{lait_decl dupIncluded
  def dup := 1
}

/-- error: dup is already defined -/
#guard_msgs in
{lait_decl dupInclude
  #include dupIncluded
  def dup := 2
}

/-- error: List.length is already defined -/
#guard_msgs in
{lait_decl dupStdlib
  #include stdlib
  def List.length (xs : Int) : Int := xs
}

/-- error: Type Option is already defined -/
#guard_msgs in
{lait_decl dupStdlibType
  #include stdlib
  type Option := | Nothing
}

-- Still allowed: `let`/`fun`/`match` binders may shadow anything, including a
-- top-level def, and `_` is a wildcard rather than a name.
{lait_decl shadowingStillOk
  def x := 1
  #test (let x := 2 in x) === 2
  #test (fun x => x + 1) 5 === 6

  def _ := ()
  def _ := ()
}

-- The names built into the language are taken from the start.  Most of them are
-- reserved tokens, so the parser rejects them where a name is expected; the
-- boolean literals are deliberately not reserved (so `true`/`false` may be used
-- as record fields and the like), which makes `def true` parseable and this
-- check the thing that rejects it.
/-- error: true is already defined -/
#guard_msgs in
{lait_decl dupBuiltinTrue
  def true := 1
}

/-- error: false is already defined -/
#guard_msgs in
{lait_decl dupBuiltinFalse
  def false (x : Int) : Int := x
}

-- A `let` named `true` is still fine (albeit unusable, since `true` in an
-- expression parses as the literal).
{lait_decl shadowBuiltinOk
  #test (let true := 1 in 2) === 2
}
