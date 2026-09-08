import Lait.Elab
import Lait.Stdlib

/-!
# `let ... in ...` and `if ... then ... else ...`

`let` requires `in`: there is no statement-sequence `let`, only an expression
whose value is its body's.  `if` requires `else`, and both branches must have
the same type.
-/

-- ===== `let` =====

{lait_decl letBasics
  #test (let x := 1 in x) === 1
  #test (let x := 1 in x + 1) === 2

  -- Annotated.
  #test (let x : Int := 5 in x + 1) === 6
  #test (let s : String := "a" in s ++ "b") === "ab"

  -- The body runs as far right as it can, so the inner `let` needs no
  -- parentheses.
  #test (let x := 1 in let y := 2 in x + y) === 3

  -- A later `let` may refer to an earlier one.
  #test (let x := 1 in let y := x + 1 in y) === 2

  -- But not to itself: `let` is non-recursive, so the `x` on the right of `:=`
  -- is the outer one.
  #test (let x := 10 in let x := x + 1 in x) === 11

  -- Innermost binding wins; the outer one is restored after.
  #test (let x := 1 in (let x := 2 in x) + x) === 3

  -- May bind a function.
  #test (let f := fun n => n + 1 in f 1) === 2

  -- May shadow a top-level `def`.
  def y := 100
  #test (let y := 1 in y) === 1
  #test y === 100

  -- `_` is a legal binder.
  #test (let _ := 1 in 2) === 2
}

{lait_decl letInDef
  #include stdlib

  -- The usual multi-step body: a chain of `let`s ending in the result.  Note
  -- the `in` after every binding.
  def hypotenuseish (a : Int) (b : Int) : Int :=
    let a2 := a * a in
    let b2 := b * b in
    a2 + b2
  #test hypotenuseish 3 4 === 25

  -- The same chain for sequencing effects.
  def bumpTwice (r : Ref<Int>) : Int :=
    let _ := set r (get r + 1) in
    let _ := set r (get r + 1) in
    get r
  #test bumpTwice (alloc 0) === 2
}

-- ===== `if` =====

{lait_decl ifBasics
  #test (if true then 1 else 2) === 1
  #test (if false then 1 else 2) === 2

  -- The condition must be a `Bool`; there is no truthiness.
  #test (if 1 < 2 then "yes" else "no") === "yes"

  -- Both branches must have the same type.
  #test (if true then "a" else "b") === "a"

  -- No `elif`: nest in the `else` branch, which extends right.
  def classify (n : Int) : String :=
    if n < 0 then "negative"
    else if n == 0 then "zero"
    else "positive"
  #test classify (- 3) === "negative"
  #test classify 0 === "zero"
  #test classify 3 === "positive"

  -- In argument position an `if` needs parentheses, since application binds
  -- tightest.
  def inc (n : Int) : Int := n + 1
  #test inc (if true then 1 else 2) === 2

  -- ...and so does an operand.
  #test (if true then 1 else 2) + 10 === 11

  -- May return a function.
  #test (if true then (fun n => n + 1) else (fun n => n - 1)) 10 === 11
}

{lait_decl ifAndLetTogether
  -- `let` inside a branch.
  def f (n : Int) : Int :=
    if n > 0 then let d := n - 1 in d * 2
    else 0
  #test f 3 === 4
  #test f 0 === 0

  -- A branch inside a `let` right-hand side.
  def g (n : Int) : Int :=
    let sign := if n < 0 then - 1 else 1 in
    sign * n
  #test g (- 3) === 3
  #test g 3 === 3
}

-- ===== Only the taken branch runs =====

{lait_decl ifIsLazyInBranches
  -- The untaken branch may safely be an error.
  #test (if true then 1 else error "never happens") === 1
  #test_error (if false then 1 else error "boom") ~ "boom"

  -- CONTRAST: `&&`/`||` are strict, so both operands are evaluated.  For
  -- short-circuiting, use `if`.
  #test_error false && error "evaluated anyway" ~ "evaluated anyway"
  #test_error true || error "evaluated anyway" ~ "evaluated anyway"
  #test (if false then error "x" else false) === false
}
