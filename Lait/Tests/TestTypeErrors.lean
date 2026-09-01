import Lait.Elab
import Lait.Stdlib

/-!
# The common type errors, with exact messages

Each block pairs a mistake with the message Lait currently produces.  Two things
to notice: every mismatch is reported as `Cannot unify X with Y`, with no
expected/got framing, no offending sub-expression, and the position of the whole
enclosing expression; and which type lands on the left of `with` follows the
order constraints happen to be solved in, not what the user wrote.  REPORT.md E2
and E3.
-/

-- ===== Mixing numbers and strings =====

/-- error: Cannot unify String with Int -/
#guard_msgs in
{lait_decl teAddString
  #eval 1 + "1"
}

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teConcatNumber
  #eval "count: " ++ 1
}

-- The fix is `toString`.
{lait_decl teConcatFixed
  #include stdlib
  #test "count: " ++ toString 1 === "count: 1"
}

-- ===== Truthiness =====

/-- error: Cannot unify Int with Bool -/
#guard_msgs in
{lait_decl teIfInt
  #eval if 1 then "yes" else "no"
}

/-- error: Cannot unify String with Bool -/
#guard_msgs in
{lait_decl teIfString
  #eval if "" then 1 else 2
}

-- ===== Branches of different types =====

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teBranchTypes
  #eval if true then 1 else "one"
}

-- Same for `match` arms.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teMatchArmTypes
  type Color := | Red | Green
  #eval
    match Red with
    | Red => 1
    | Green => "green"
    end
}

-- ===== Calling a curried function as if it took a tuple =====

-- `add(1, 2)` is not a syntax error: it applies `add` to the pair `(1, 2)`, so
-- the message is about a pair where an `Int` was wanted.
/-- error: Cannot unify Int with Int * Int -/
#guard_msgs in
{lait_decl teTupleCall
  def add (x : Int) (y : Int) : Int := x + y
  #eval add(1, 2)
}

-- ===== Wrong number of arguments =====

-- Too many: the result of the last application is not a function.
/-- error: Cannot unify Int with Int -> _a -/
#guard_msgs in
{lait_decl teTooManyArgs
  def add (x : Int) (y : Int) : Int := x + y
  #eval add 1 2 3
}

-- Too few: a function where a value was wanted.
/-- error: Cannot unify Int -> Int with Int -/
#guard_msgs in
{lait_decl teTooFewArgs
  def add (x : Int) (y : Int) : Int := x + y
  #eval add 1 + 1
}

-- Applying something that is not a function.
/-- error: Cannot unify Int with Int -> _a -/
#guard_msgs in
{lait_decl teApplyNonFunction
  #eval 1 2
}

-- ===== Argument order =====

-- `List.map` takes the list first; backwards gives a `List` vs function type
-- mismatch.
/-- error: Cannot unify List<_a> with _b -> Int -/
#guard_msgs in
{lait_decl teMapArgOrder
  #include stdlib
  #eval List.map (fun x => x + 1) [1, 2, 3]
}

{lait_decl teMapArgOrderFixed
  #include stdlib
  #test List.map [1, 2, 3] (fun x => x + 1) === [2, 3, 4]
}

-- ===== Heterogeneous collections =====

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teMixedList
  #include stdlib
  #eval [1, "a"]
}

/-- error: Cannot unify Int with Bool -/
#guard_msgs in
{lait_decl teMixedCons
  #include stdlib
  #eval 1 :: [true]
}

-- ===== Comparing different types =====

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teCompareMixed
  #eval 1 == "1"
}

-- `<` and friends are `Int`-only.
/-- error: Cannot unify String with Int -/
#guard_msgs in
{lait_decl teCompareStrings
  #eval "a" < "b"
}

-- ===== Forgetting `#include stdlib` =====

-- Without it, none of `List`, `Option`, `Map`, `alloc`, `toString`, `print`,
-- `assert` are in scope, and `[]`/`::` have no `Nil`/`Cons` to refer to.  The
-- message is about a missing variable, not the missing `#include`.
/-- error: Variable Cons not found -/
#guard_msgs in
{lait_decl teNoStdlibList
  #eval [1, 2]
}

/-- error: Variable toString not found -/
#guard_msgs in
{lait_decl teNoStdlibToString
  #eval toString 1
}

/-- error: Unknown type constructor: List -/
#guard_msgs in
{lait_decl teNoStdlibListType
  def f (xs : List<Int>) : Int := 0
}

-- ===== Scope =====

-- Declarations are processed in order.
/-- error: Variable f not found -/
#guard_msgs in
{lait_decl teForwardReference
  def g := f 1
  def f (x : Int) : Int := x
}

-- A `def` without parameters is not recursive; only one with parameters (or an
-- explicit `fix`) binds its own name.
/-- error: Variable f not found -/
#guard_msgs in
{lait_decl teValueDefIsNotRecursive
  def f := f + 1
}

-- Mutual recursion needs `and`.
/-- error: Variable isOdd not found -/
#guard_msgs in
{lait_decl teMutualNeedsAnd
  def isEven (n : Int) : Bool := if n == 0 then true else isOdd (n - 1)
  def isOdd (n : Int) : Bool := if n == 0 then false else isEven (n - 1)
}

{lait_decl teMutualWithAnd
  def isEven (n : Int) : Bool := if n == 0 then true else isOdd (n - 1)
  and isOdd (n : Int) : Bool := if n == 0 then false else isEven (n - 1)
  #test isEven 4 === true
}

-- A typo is reported the same way, with no "did you mean".
/-- error: Variable List.lenght not found -/
#guard_msgs in
{lait_decl teTypo
  #include stdlib
  #eval List.lenght [1, 2]
}

-- ===== Constructors =====

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teCtorArgType
  type Box := | Box (v : Int)
  #eval Box "s"
}

-- Applied to too few arguments, a constructor is a function.
/-- error: Cannot unify Int -> Box with Box -/
#guard_msgs in
{lait_decl teCtorPartial
  type Box := | Box (v : Int)
  def b : Box := Box
}

-- ===== Annotations the body contradicts =====

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teAnnotationMismatch
  def f : String := 1
}

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teReturnTypeMismatch
  def f (x : Int) : String := x
}

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl teLetAnnotationMismatch
  #eval let x : String := 1 in x
}

-- ===== Effects =====

-- `set` returns `()`, so using its result as a value is a type error.  This is
-- what "why can't I write two statements in a row?" looks like.
/-- error: Cannot unify Unit with Int -/
#guard_msgs in
{lait_decl teSequencing
  #include stdlib
  def r := alloc 0
  def f () : Int := set r 1
}

{lait_decl teSequencingFixed
  #include stdlib
  def r := alloc 0
  def f () : Int :=
    let _ := set r 1 in
    get r
  #test f () === 1
}

-- Reading through a non-reference.
/-- error: Cannot unify Int with Ref<_a> -/
#guard_msgs in
{lait_decl teDerefNonRef
  #eval builtin_get(1)
}
