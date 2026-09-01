import Lait.Elab
import Lait.Stdlib

/-!
# Type aliases

`type N := T` (no `|` on the right) declares an alias: a second name for an
existing type.  Aliases are transparent -- expanded before anything else, so they
never appear in a type error or a `#check`, and a value of the alias is
interchangeable with one of the underlying type.
-/

{lait_decl aliasBasics
  #include stdlib

  type Name := String
  def n : Name := "ada"
  #test n === "ada"
  -- A `Name` is a `String`.
  #test n ++ "!" === "ada!"
  def greet (s : String) : String := "hi " ++ s
  #test greet n === "hi ada"

  type IntPair := Int * Int
  def p : IntPair := (1, 2)
  #test fst p === 1

  type IntFn := Int -> Int
  def f : IntFn := fun x => x + 1
  #test f 1 === 2

  type Ints := List<Int>
  def xs : Ints := [1, 2]
  #test List.length xs === 2

  type Counter := Ref<Int>
  def c : Counter := alloc 0
  def _ := set c 1
  #test get c === 1

  type Pt := Int * Int
  def q : Pt := (1, 2)
  #test fst q === 1

  -- Aliases may refer to earlier aliases.
  type Pts := List<Pt>
  def ps : Pts := [q, q]
  #test List.length ps === 2
}

-- `#check` shows the expansion.
/--
info: String
---
info: Int * Int
---
info: List<Int>
-/
#guard_msgs in
{lait_decl aliasIsTransparentInMessages
  #include stdlib
  type Name := String
  type IntPair := Int * Int
  type Ints := List<Int>
  def n : Name := "a"
  def p : IntPair := (1, 2)
  def xs : Ints := []
  #check n
  #check p
  #check xs
}

-- ===== Parameterized aliases =====

{lait_decl aliasParameterized
  #include stdlib

  type Pair<a, b> := a * b
  def mk (x : a) (y : b) : Pair<a, b> := (x, y)
  #test fst (mk 1 "s") === 1
  #test snd (mk 1 "s") === "s"

  type Twice<a> := a * a
  def dup (x : a) : Twice<a> := (x, x)
  #test fst (dup 3) === 3
  #test snd (dup "s") === "s"

  type Table<v> := Map<String, v>
  def t : Table<Int> := Map.empty
  #test Map.lookup (Map.insert "a" 1 t) "a" === Some 1

  type Pred<a> := a -> Bool
  def isPos : Pred<Int> := fun n => n > 0
  #test isPos 1 === true
  #test List.filter [1, - 1, 2] isPos === [1, 2]
}

-- CURRENT BEHAVIOR: a type variable free in the body becomes an implicit
-- parameter, so `type Weird := a * a` silently has arity one.  The only sign is
-- the arity error when you then write `Weird` bare.  REPORT.md P12.
/--
info: Int * Int
-/
#guard_msgs in
{lait_decl aliasImplicitParameter
  type Weird := a * a
  def q : Weird<Int> := (1, 2)
  #check q
}

/-- error: Wrong number of arguments to Weird -/
#guard_msgs in
{lait_decl aliasImplicitParameterArity
  type Weird := a * a
  def q : Weird := (1, 2)
}

-- ===== An alias in a constructor's argument type =====

-- A `type ... := | ...` may spell a constructor argument with an alias.  Aliases there are
-- expanded when the constructor is *used*, not when it is declared -- which is what lets a
-- mutually recursive group name a sibling that has not been declared yet.
{lait_decl aliasInCtor
  #include stdlib
  type Ints<a> := List<a>
  type Labelled<a> := Ints<a> * a
  type Wrap<a> := | Wrap (v : Ints<a>) | Both (p : Labelled<a>)
  def unwrap (w : Wrap<a>) : List<a> :=
    match w with
    | Wrap v => v
    | Both p => fst p
    end
  -- Wrap<a> -> List<a>
  #check unwrap
  #test unwrap (Wrap [1, 2]) === [1, 2]
  #test unwrap (Both ([1], 7)) === [1]
  #test unwrap (Wrap ["a"]) === ["a"]
}

-- ===== Errors =====

/-- error: Wrong number of arguments to Pair -/
#guard_msgs in
{lait_decl aliasWrongArity
  type Pair<a, b> := a * b
  def q : Pair<Int> := (1, 2)
}

-- Arity is checked in a constructor's argument type too.
/-- error: Wrong number of arguments to Ints -/
#guard_msgs in
{lait_decl aliasArityInCtor
  #include stdlib
  type Ints<a> := List<a>
  type Bad := | Bad (v : Ints<Int, Int>)
  def f (b : Bad) : Int := 0
}

-- No recursive aliases; use `type ... := | ...` for a recursive type.
/-- error: Unknown type constructor: Cyc -/
#guard_msgs in
{lait_decl aliasNotRecursive
  type Cyc := Cyc
}

/-- error: Type Alias is already defined -/
#guard_msgs in
{lait_decl aliasDuplicate
  type Alias := Int
  type Alias := Bool
}

/-- error: Declared types must begin with an upper-case letter -/
#guard_msgs in
{lait_decl aliasLowerCase
  type name := String
}

/-- error: Type parameters must begin with a lower-case letter -/
#guard_msgs in
{lait_decl aliasUpperCaseParam
  type Bad<A> := A
}

-- The built-in type names (`Int`, `Bool`, `String`, `Unit`, `Ref`) are reserved
-- tokens, so `type Int := String` does not parse and there is no "already
-- defined" message.  A name from `#include` is reported, though.
/-- error: Type Option is already defined -/
#guard_msgs in
{lait_decl aliasShadowsIncluded
  #include stdlib
  type Option := Int
}
