import Lait.Elab
import Lait.Stdlib

/-!
# Base types, literals, and the primitive operators

Integer/string/boolean/unit literals, the arithmetic and comparison operators,
and how they associate and bind.
-/

-- ===== Integer literals =====

{lait_decl basicInts
  #test 0 === 0
  #test 42 === 42

  -- A negative literal is `- 5`; the `-` is part of the literal
  -- (`syntax:67 "-" num`), not the binary minus.
  #test - 5 === - 5
  #test - 0 === 0

  -- Arbitrary precision; nothing wraps.
  #test 1000000000000 + 1 === 1000000000001
  #test 2 * 4611686018427387904 === 9223372036854775808

  -- ===== Arithmetic =====
  #test 2 + 3 === 5
  #test 2 - 3 === - 1
  #test 2 * 3 === 6
  #test 0 - 5 === - 5

  -- `+`/`-` are left-associative.
  #test 1 - 2 - 3 === - 4
  #test 1 - (2 - 3) === 2
  #test 10 - 3 + 2 === 9

  -- `*` (62) binds tighter than `+`/`-` (60).
  #test 1 + 2 * 3 === 7
  #test 2 * 3 + 1 === 7
  #test (1 + 2) * 3 === 9
  #test 2 * 3 * 4 === 24
}

-- ===== Booleans =====

{lait_decl basicBools
  #test true === true
  #test false === false

  #test true && true === true
  #test true && false === false
  #test false || true === true
  #test false || false === false

  -- `not` is prefix at 67, above every infix operator, so it grabs only its
  -- immediate argument.
  #test not true === false
  #test not false === true
  #test not true && false === false
  #test not (true && false) === true

  -- `&&` (50) binds tighter than `||` (45).
  #test true || true && false === true
  #test (true || true) && false === false

  -- Both left-associative.
  #test true && true && false === false
  #test false || false || true === true

  -- `&&`/`||` are ordinary primitives: both sides are evaluated, no
  -- short-circuiting.  See TestErrors.lean.
}

-- ===== Comparison and equality =====

{lait_decl basicCompare
  #test 3 < 4 === true
  #test 4 < 3 === false
  #test 3 < 3 === false
  #test 5 > 4 === true
  #test 4 <= 4 === true
  #test 3 <= 4 === true
  #test 5 >= 6 === false
  #test 6 >= 6 === true

  -- Comparison (55) is looser than arithmetic (60/62)...
  #test 1 + 2 == 3 === true
  #test 2 * 3 < 7 === true

  -- ...and tighter than `&&`/`||`.
  #test 0 < 1 && 1 < 2 === true

  -- Equality is `==`; a single `=` is a parse error.
  #test 3 == 3 === true
  #test 3 == 4 === false
  #test 3 != 4 === true
  #test 3 != 3 === false

  -- Polymorphic at every non-function type.
  #test "hi" == "hi" === true
  #test "hi" == "ho" === false
  #test true == true === true
  #test () == () === true
  #test (1, "a") == (1, "a") === true
  #test (1, "a") == (1, "b") === false
}

-- ===== Strings =====

{lait_decl basicStrings
  #test "" === ""
  #test "hello" === "hello"

  -- `++` is string concatenation, not list append (that is `List.append`; see
  -- TestLists.lean).
  #test "a" ++ "b" === "ab"
  #test "a" ++ "b" ++ "c" === "abc"
  #test "" ++ "x" === "x"

  -- Lean/C escapes.
  #test "a\tb" === "a\tb"
  #test "line\nline" === "line\nline"
  #test "quote\"inside" === "quote\"inside"

  -- `++` (60) is at additive precedence, tighter than `==` (55).
  #test "ab" ++ "c" == "abc" === true
}

-- ===== Unit =====

{lait_decl basicUnit
  #test () === ()

  def u : Unit := ()
  #test u === ()

  -- `()` is the result type of the effecting operations, hence the
  -- `def _ := ...` idiom.
  def _ := ()
}

-- ===== `#check` on each base type =====

/--
info: Int
---
info: Bool
---
info: String
---
info: Unit
---
info: Int -> Int
-/
#guard_msgs in
{lait_decl basicCheckTypes
  #check 1
  #check true
  #check "s"
  #check ()
  #check fun (x : Int) => x + 1
}
