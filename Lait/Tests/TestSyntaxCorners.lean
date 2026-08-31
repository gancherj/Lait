import Lait.Elab
import Lait.Stdlib

/-!
# Syntax corners

The precedence table checked by example, plus the forms that are easy to miss.
The catalogue of things that do *not* parse is at the bottom as comments, since a
parse error escapes `#guard_msgs`.

Tightest first:

    70  application                 f x
    67  fst / snd / not / -lit      fst p, not b, - 5
    62  *
    60  + - ++ ::
    55  < > <= >= == !=
    50  &&
    45  ||

Everything at 45-62 is left-associative except `::`, which is right.  The
"closing" forms (`fun`, `let ... in`, `if`, `match ... end`, `try ... end`,
`fix`) are outside the table: their bodies run as far right as they can.
-/

{lait_decl synPrecedence
  #include stdlib

  -- Application beats everything.
  def inc (n : Int) : Int := n + 1
  #test inc 1 * 2 === 4
  #test inc 1 + 1 === 3
  #test not (inc 0 == 1) === false

  -- 67 beats the infix operators...
  #test fst (1, 2) * 3 === 3
  #test not true == false === true
  -- ...but loses to application, so `fst p q` would apply `fst p` to `q`.
  def pairOf (n : Int) : Int * Int := (n, n + 1)
  #test fst (pairOf 1) === 1

  -- 62 vs 60.
  #test 1 + 2 * 3 === 7
  #test 2 * 3 - 1 === 5

  -- 60 vs 55.
  #test 1 + 1 == 2 === true
  #test "a" ++ "b" == "ab" === true

  -- 55 vs 50 vs 45.
  #test 1 < 2 && 2 < 3 === true
  #test 1 < 2 || 1 > 2 && false === true

  -- Associativity.
  #test 10 - 5 - 2 === 3
  #test 2 * 3 * 2 === 12
  #test "a" ++ "b" ++ "c" === "abc"
  #test true && true && false === false
  #test 1 :: 2 :: [] === [1, 2]

  -- A "closing" form swallows the rest of the line, so one used as an operand
  -- needs parentheses.
  #test (if true then 1 else 2) + 10 === 11
  #test (fun (n : Int) => n + 1) 1 + 10 === 12
  #test (let n := 1 in n) + 10 === 11
  #test 10 + (if true then 1 else 2) === 11
  -- ...but in trailing position it needs none.
  #test (if true then 1 + 1 else 2) === 2
}

{lait_decl synNegativeNumbers
  #include stdlib

  -- `- 5` at 67 is a negative literal, and needs the space: `-5` is not a token,
  -- and `x - 5` is the binary operator.
  #test - 5 === 0 - 5
  #test 3 - 5 === - 2
  #test 3 - - 5 === 8
  #test (- 5) * (- 1) === 5
  #test toString (- 5) === "-5"

  -- No unary minus on an expression: to negate `n`, write `0 - n`.
  def negate (n : Int) : Int := 0 - n
  #test negate 5 === - 5
  #test negate (- 5) === 5
}

-- ===== `%op { ... }` =====

{lait_decl synPercentOp
  #include stdlib

  -- `%name {e1, ..., en}` applies a primitive operator directly.  This is how
  -- the stdlib defines `toString`; there is normally no reason to write it.
  #test %toString {1} === "1"
  #test %toString {(1, 2)} === "(1, 2)"

  -- The primitives are those in `initTcOpMap`: `+ - * ++ && || not < > <= >= ==
  -- toString`.  Only `toString` is reachable this way: `%` wants an identifier,
  -- and every other primitive's name is punctuation or (for `not`) a reserved
  -- token.
}

/-- error: Unknown operator/constructor: bogus -/
#guard_msgs in
{lait_decl synPercentUnknown
  #eval %bogus {1}
}

/-- error: Operator toString expects 1 arguments but got 2 -/
#guard_msgs in
{lait_decl synPercentArity
  #eval %toString {1, 2}
}

-- ===== internal_print =====

{lait_decl synInternalPrint
  #include stdlib

  -- `internal_print : String -> Unit`.  The stdlib's `print` is a thin wrapper
  -- and is what you should use.
  def _ := internal_print "TestSyntaxCorners: internal_print works"
  def _ := print "TestSyntaxCorners: print works"
}

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl synInternalPrintNeedsString
  #eval internal_print 1
}

-- ===== `...` =====

{lait_decl synTodo
  -- `...` type-checks at any type and raises when reached.
  def half (b : Bool) : Int := if b then 1 else ...
  #test half true === 1
  #test_error half false ~ "unimplemented"

  def stubStr (b : Bool) : String := if b then "a" else ...
  #test stubStr true === "a"
}

-- ===== Things that do NOT parse =====
--
-- `#guard_msgs` never sees a parse error, so these are recorded here with the
-- message each produces.  REPORT.md P2-P4 and E4 discuss the ones worth fixing.
--
--   def f x = x + 1
--       unexpected token '='; expected ':='
--
--   def f := fun x -> x + 1
--       unexpected token '->'; expected '=>'
--
--   def f := fun x y => x + y            -- `fun` takes exactly ONE binder
--       unexpected identifier; expected '=>'
--
--   #eval 7 / 2                          -- no division or modulo
--       unexpected token '/'; expected '}'
--
--   #eval 1 + 1 :: []                    -- `::` and `+` share precedence 60
--       unexpected token '::'; expected ...
--
--   #eval (1, 2, 3)                      -- pairs only; write (1, (2, 3))
--       unexpected token ','; expected ')'
--
--   #eval ([] : List<Int>)               -- no (e : T) ascription
--       unexpected token ':'; expected ')' or ','
--
--   match p with | (x, y) => x end       -- no tuple patterns
--       unexpected token '('; expected '[]', '_', identifier or lait_ident
--
--   match n with | 0 => 1 | _ => 2 end   -- no literal patterns
--       unexpected token; expected '[]', '_', identifier or lait_ident
--
--   match xs with | x :: (y :: r) => 1   -- no nested patterns
--       unexpected token '('; expected lait_ident
--
-- A parse error inside a `match` is the worst case: the following `end` is then
-- read as Lean's own `end` keyword, giving
--
--   Invalid `end`: There is no current scope to end
--   Note: Scopes are introduced using `namespace` and `section`
--
-- followed by `unexpected token '}'; expected command`.  REPORT.md E4.
