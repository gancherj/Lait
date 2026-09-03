import Lait.Elab
import Lait.Stdlib

/-!
# Run-time errors, `try`, and the step limit

One exception mechanism: `error e` raises with the string `e`, and
`try e1 with e2 end` runs `e2` if `e1` raises.  There is no exception value and
no way to inspect the message, so `try` is "recover with this default", not
"catch and handle".

The interpreter's step limit is separate (`ExpError.TimeoutError` in `Eval.lean`)
and `try` cannot catch it.

`#test_error e ~ "substring"` asserts that `e` raises with a message containing
the substring.
-/

-- ===== `error` =====

{lait_decl errRaise
  #include stdlib

  #test_error error "boom" ~ "boom"

  -- The message is prefixed with `ERROR: `.
  #test_error error "boom" ~ "ERROR: boom"

  -- `error : String -> a`, so it stands in for a value of any type.
  def headOrDie (xs : List<a>) : a :=
    match xs with
    | [] => error "empty list"
    | h :: _ => h
    end
  #test headOrDie [1] === 1
  #test headOrDie ["s"] === "s"
  def noInts : List<Int> := []
  #test_error headOrDie noInts ~ "empty list"

  -- The argument must be a `String`.
  def checked (n : Int) : Int :=
    if n < 0 then error ("negative: " ++ toString n) else n
  #test checked 1 === 1
  #test_error checked (- 1) ~ "negative: -1"
}

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl errNeedsString
  #eval error 42
}

-- ===== `try ... with ... end` =====

{lait_decl errTry
  #include stdlib

  -- The handler runs only if the body raises.
  #test (try 1 with 2 end) === 1
  #test (try error "x" with 2 end) === 2

  -- Both sides must have the same type.
  #test (try error "x" with "fallback" end) === "fallback"

  -- The handler may itself raise.
  #test_error (try error "a" with error "b" end) ~ "b"

  -- ...and `try`s nest.
  #test (try (try error "a" with error "b" end) with 7 end) === 7

  -- No way to see the raised message: `with` takes an expression, not a binder.
  -- If you need the message, do not use `error`.
  def safeDiv (n : Int) (d : Int) : Option<Int> :=
    if d == 0 then None else Some n

  #test safeDiv 1 0 === None
  #test safeDiv 1 1 === Some 1

  -- `try` catches errors from anywhere inside the body, however deep.
  def boom (n : Int) : Int := if n == 0 then error "bottom" else boom (n - 1)
  #test (try boom 10 with - 1 end) === - 1
}

/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl errTryBranchTypes
  #eval try 1 with "s" end
}

-- ===== The step limit =====

{lait_decl errStepLimit
  #include stdlib

  -- 100000 interpreter steps per top-level `#eval`/`#test`, so a
  -- non-terminating program is reported rather than hanging.
  def loop (n : Int) : Int := loop n
  #test_error loop 1 ~ "Step limit exceeded"

  def forever := fix f. fun (_ : Unit) => f ()
  #test_error forever () ~ "Step limit exceeded"

  -- CURRENT BEHAVIOR: terminating recursion over a few thousand elements
  -- exhausts the budget too, at roughly 20 steps per call.  REPORT.md P9.
  def deep (n : Int) : Int := if n == 0 then 0 else 1 + deep (n - 1)
  #test deep 1000 === 1000
  #test_error deep 20000 ~ "Step limit exceeded"
}

-- The limit is the interpreter giving up, not a program-level exception, so it
-- propagates past a handler.
{lait_decl errTryDoesNotCatchStepLimit
  def loop (n : Int) : Int := loop n
  #test_error (try loop 1 with 0 end) ~ "Step limit exceeded"

  -- ...at any depth, and even when reached only from the handler.
  #test_error (try (try loop 1 with 0 end) with 0 end) ~ "Step limit exceeded"
  #test_error (try error "x" with loop 1 end) ~ "Step limit exceeded"

  -- Ordinary errors in the same position are still caught.
  #test (try error "x" with 0 end) === 0
}

-- ===== Errors from the primitive operators =====

{lait_decl errPrimitives
  #include stdlib

  -- `==` on functions is the one operator that is well-typed but can fail.
  #test_error (fun (x : Int) => x) == (fun (x : Int) => x) ~ "Equality not supported for functions"

  -- ...including a function buried in a pair or a constructor.
  #test_error (1, fun (x : Int) => x) == (1, fun (x : Int) => x) ~ "Equality not supported for functions"
  #test_error Some (fun (x : Int) => x) == Some (fun (x : Int) => x) ~ "Equality not supported for functions"
}

-- ===== `...` (unimplemented) =====

{lait_decl errTodo
  #include stdlib

  -- `...` type-checks at any type and raises when reached, so a partially
  -- written program still runs.
  def stub (n : Int) : Int := if n > 0 then n else ...
  #test stub 1 === 1
  #test_error stub 0 ~ "unimplemented"

  -- CURRENT BEHAVIOR: the message embeds the absolute path of the source file.
  -- REPORT.md P10.
  #test_error stub 0 ~ "TestErrors.lean, Line"
}

-- ===== What `#test`/`#test_error` report on failure =====

/-- error: Test failed: got 1 but expected 2 -/
#guard_msgs in
{lait_decl errTestFailure
  #test 1 === 2
}

/-- error: Test failed: expected an error containing "boom" but evaluation succeeded with 1 -/
#guard_msgs in
{lait_decl errTestErrorNoError
  #test 1 === 1
  #test_error 1 ~ "boom"
}

/-- error: Test failed: expected an error containing "bbb" but got error "ERROR: aaa" -/
#guard_msgs in
{lait_decl errTestErrorWrongMessage
  #test_error error "aaa" ~ "bbb"
}

-- An error inside a `#test` is reported as the error, not as a failed test.
/-- error: ERROR: boom -/
#guard_msgs in
{lait_decl errTestRaises
  #test error "boom" === 1
}

-- ===== Errors abort the rest of the block =====

-- CURRENT BEHAVIOR: a type error stops the whole `{lait_decl ...}` block, so
-- later declarations are never checked and only one error is reported.
-- REPORT.md P11.
/-- error: Cannot unify String with Int -/
#guard_msgs in
{lait_decl errStopsAtFirst
  def bad := 1 + "s"
  def alsoBad := true + 1
  #test 1 === 2
}

-- ===== A definition whose body raises =====

/-
A `def` is evaluated as soon as it is declared, so its body can raise before
anything uses it.  That failure is *local*: it is reported once at the
declaration, the declaration group carries on, and the binding stays in the
environment as a recorded failure (`Val.VFailed`).

Both halves matter.  Aborting the group instead would mean one bad definition
hid every later result; and dropping the binding would leave the environment
shorter than the list of names the type checker indexed against, silently
rebinding every *earlier* definition to the wrong value -- `before` below would
have evaluated to `after`'s value, with no error anywhere.
-/
/-- error: ERROR: boom -/
#guard_msgs in
{lait_decl defBodyRaises
  #include stdlib

  def before : Int := 111
  def raises : Int := error "boom"
  def after : Int := 222

  -- Neighbours are untouched, and keep their own values.
  #test before === 111
  #test after === 222

  -- Using the failed definition raises at the point of use, naming it.
  #test_error raises + 1 ~ "`raises` cannot be used here"
  #test_error raises + 1 ~ "boom"
}

-- The failure propagates: a definition built from a failed one fails in turn,
-- and says which definition was the root cause.
/--
error: ERROR: root cause
---
error: `broken` cannot be used here because its own definition failed: ERROR: root cause
-/
#guard_msgs in
{lait_decl defBodyRaisesChain
  #include stdlib

  def broken : Int := error "root cause"
  def derived : Int := broken + 1
  def fine : Int := 7

  #test fine === 7
  #test_error derived ~ "`derived` cannot be used here"
  #test_error broken ~ "root cause"
}
