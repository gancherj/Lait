import Lait.Elab
import Lait.Stdlib

/-!
# The common type errors, with exact messages

Each block pairs a mistake with the message Lait currently produces.  Two things
to notice: every mismatch is reported as `Cannot unify X with Y`, with no
expected/got framing and no offending sub-expression, at the position of the
whole enclosing expression -- except in a `match`, where the arm that disagrees
is reported on its own body (see "Where an error lands" at the end of this
file); and the type on the left of `with` is whichever the checker reached
first, which is not always the one the user would name first.
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
/-- error: Cannot unify Int with Int -> a -/
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
/-- error: Cannot unify Int with Int -> a -/
#guard_msgs in
{lait_decl teApplyNonFunction
  #eval 1 2
}

-- ===== Argument order =====

-- `List.map` takes the list first; backwards gives a `List` vs function type
-- mismatch.
/-- error: Cannot unify List<a> with Int -> Int -/
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

/-- error: Cannot unify String with Int -/
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
/-- error: Cannot unify Int with Ref<a> -/
#guard_msgs in
{lait_decl teDerefNonRef
  #eval builtin_get(1)
}

-- ===== Where an error lands =====

/-!
`#guard_msgs` pins down what a message *says*; it never sees where the message
was reported.  `#errorRanges` below fills that half in: it elaborates a command
and logs, for each error, the source text the error covers.
-/

open Lean Elab Command in
/-- `#errorRanges <command>`: elaborate `<command>` and log one line per error it
reports, as `<the source the error covers>  ⇒  <what it says>`.  The errors
themselves are consumed, so what `#guard_msgs` asserts on is this listing. -/
elab "#errorRanges " c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := {} }
  try elabCommand c catch e => logError (← e.toMessageData.toString)
  let produced := (← get).messages
  modify fun s => { s with messages := saved }
  let fm ← getFileMap
  let mut out : Array _root_.String := #[]
  for m in produced.toList do
    if m.severity matches .error then
      let b := fm.ofPosition m.pos
      let e := fm.ofPosition (m.endPos.getD m.pos)
      let src := (Substring.Raw.mk fm.source b e).toString
      out := out.push s!"{src.replace "\n" " "}  ⇒  {← m.data.toString}"
  logInfo <| "\n".intercalate out.toList

-- A `match` arm whose body has the wrong type is reported on that body, not on
-- the `match` -- the arm is the only thing distinguishing the two types, so
-- reporting on the whole expression would leave the reader to find it.
/--
info: "green"  ⇒  Cannot unify Int with String
-/
#guard_msgs in
#errorRanges
{lait_decl teArmRangeCtor
  type Color := | Red | Green
  #eval
    match Red with
    | Red => 1
    | Green => "green"
    end
}

-- Same for the catch-all arm.
/--
info: false  ⇒  Cannot unify Int with Bool
-/
#guard_msgs in
#errorRanges
{lait_decl teArmRangeWild
  #include stdlib
  def f (xs : List<Int>) : Int :=
    match xs with
    | Nil => 0
    | _ => false
    end
}

-- A multi-line arm body is covered whole; the report still starts at the arm.
/--
info: let y := 3 in       false  ⇒  Cannot unify Int with Bool
-/
#guard_msgs in
#errorRanges
{lait_decl teArmRangeMultiline
  type Color := | Red | Green
  def f (c : Color) : Int :=
    match c with
    | Red => 0
    | Green =>
      let y := 3 in
      false
    end
}

-- When no single arm is at fault -- every arm agrees, and it is the signature
-- they disagree with -- there is no arm to blame, and the report falls back to
-- the enclosing command.  (A `def` with parameters pins its return type through
-- a synthesized `let` that carries no source span, which is why this lands on
-- the whole block rather than on the `def`.)
/--
info: {lait_decl teArmRangeAllArms   type Color := | Red | Green   def f (c : Color) : Int :=     match c with     | Red => false     | Green => false     end }  ⇒  Cannot unify Bool with Int
-/
#guard_msgs in
#errorRanges
{lait_decl teArmRangeAllArms
  type Color := | Red | Green
  def f (c : Color) : Int :=
    match c with
    | Red => false
    | Green => false
    end
}
