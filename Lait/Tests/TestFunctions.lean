import Lait.Elab
import Lait.Stdlib

/-!
# Functions: `fun`, application, currying, `def`, and `fix`

`f x y` is two applications of a curried function, not one call with two
arguments.  Most of this file is about that.
-/

-- ===== Lambdas and application =====

{lait_decl fnLambda
  -- Un-annotated: the argument type is inferred.
  #test (fun x => x + 1) 5 === 6

  -- Annotated.  The parentheses are part of `fun (x : T) => e`.
  #test (fun (x : Int) => x + 1) 5 === 6

  -- `_` is a legal binder.
  #test (fun _ => 7) "ignored" === 7

  -- The body extends as far right as it can, so the parentheses matter: without
  -- them this parses as `fun x => x + (1 5)`.
  #test (fun x => x + 1) 5 === 6

  -- Application (70) binds tighter than every infix operator.
  def inc (n : Int) : Int := n + 1
  #test inc 1 + 1 === 3
  #test inc (1 + 1) === 3

  -- ...and is left-associative: `f x y` is `(f x) y`.
  def const2 (x : Int) (y : Int) : Int := x
  #test const2 1 2 === 1

  -- An argument that is itself an application needs parentheses.
  #test inc (inc 1) === 3
}

-- ===== Currying =====

{lait_decl fnCurry
  def add (x : Int) (y : Int) : Int := x + y

  -- `->` is right-associative, so `add : Int -> (Int -> Int)`.
  #test add 2 3 === 5

  -- Hence partial application.
  def add2 := add 2
  #test add2 3 === 5
  #test add2 40 === 42

  -- The nested-lambda spelling.
  def addL := fun x => fun y => x + y
  #test addL 2 3 === 5
  #test (addL 2) 3 === 5

  def addA : Int -> Int -> Int := fun x => fun y => x + y
  #test addA 2 3 === 5

  -- The one-tuple-argument style is a different type; calling it with two
  -- arguments does not type-check (see TestTypeErrors.lean).
  def addP (p : Int * Int) : Int := fst p + snd p
  #test addP (2, 3) === 5
}

/--
info: Int -> Int -> Int
-/
#guard_msgs in
{lait_decl fnCurryCheck
  def add (x : Int) (y : Int) : Int := x + y
  #check add
}

-- ===== Closures =====

{lait_decl fnClosures
  -- Lexical scope: a lambda captures where it was written, not where it is
  -- called.
  def makeAdder (n : Int) : Int -> Int := fun x => x + n
  def add10 := makeAdder 10
  #test add10 5 === 15

  def x := 100
  def usesOuterX (y : Int) : Int := x + y
  #test usesOuterX 1 === 101

  -- Shadowing `x` in a body leaves the top-level binding alone.
  def shadowsX (x : Int) : Int := x + 1
  #test shadowsX 1 === 2
  #test x === 100

  -- Two closures from the same function share nothing.
  def a1 := makeAdder 1
  def a2 := makeAdder 2
  #test a1 0 === 1
  #test a2 0 === 2
}

-- ===== Higher-order functions =====

{lait_decl fnHigherOrder
  def twice (f : Int -> Int) (x : Int) : Int := f (f x)
  def inc (n : Int) : Int := n + 1
  #test twice inc 0 === 2
  #test twice (fun n => n * 2) 3 === 12

  -- A partially applied function as an argument.
  def add (x : Int) (y : Int) : Int := x + y
  #test twice (add 5) 0 === 10

  def compose (f : b -> c) (g : a -> b) (x : a) : c := f (g x)
  #test compose inc inc 0 === 2
  #test compose (fun (s : String) => s ++ "!") (fun (n : Int) => "n") 1 === "n!"

  def apply (f : a -> b) (x : a) : b := f x
  #test apply inc 1 === 2
  #test apply (apply add 1) 2 === 3
}

-- ===== The `def` spellings =====

{lait_decl fnDefForms
  -- Everything annotated.
  def f1 (x : Int) (y : Int) : Int := x + y
  #test f1 1 2 === 3

  -- No return type.
  def f2 (x : Int) (y : Int) := x + y
  #test f2 1 2 === 3

  -- Argument types inferred.
  def f3 x y := x + y
  #test f3 1 2 === 3

  -- Mixed.
  def f4 (x : Int) y : Int := x + y
  #test f4 1 2 === 3

  -- No parameters: a value binding.
  def f5 := 3
  #test f5 === 3

  def f6 : Int := 3
  #test f6 === 3

  -- `()` as a parameter is sugar for `(_ : Unit)`, i.e. a thunk.
  def f7 () := 3
  #test f7 () === 3

  -- Un-annotated parameters generalize when the body allows it.
  def f8 x := x
  #test f8 1 === 1
  #test f8 "s" === "s"
}

-- ===== Recursion =====

{lait_decl fnRecursion
  -- A `def` with parameters may call itself; no extra keyword.
  def fact (n : Int) : Int := if n <= 1 then 1 else n * fact (n - 1)
  #test fact 0 === 1
  #test fact 1 === 1
  #test fact 5 === 120
  #test fact 10 === 3628800

  def fib (n : Int) : Int := if n < 2 then n else fib (n - 1) + fib (n - 2)
  #test fib 0 === 0
  #test fib 1 === 1
  #test fib 10 === 55

  -- Accumulator style.
  def sumTo (n : Int) (acc : Int) : Int :=
    if n == 0 then acc else sumTo (n - 1) (acc + n)
  #test sumTo 10 0 === 55

  -- Mutual recursion with `and`.
  def isEven (n : Int) : Bool := if n == 0 then true else isOdd (n - 1)
  and isOdd (n : Int) : Bool := if n == 0 then false else isEven (n - 1)
  #test isEven 10 === true
  #test isOdd 10 === false
  #test isEven 7 === false
  #test isOdd 7 === true
}

-- ===== `fix` =====

{lait_decl fnFix
  #include stdlib

  -- `fix f. e` binds `f` to the whole expression inside `e`.  A `def` with
  -- parameters is sugar for this.
  def fact := fix f. fun (n : Int) => if n <= 1 then 1 else n * f (n - 1)
  #test fact 5 === 120

  -- It is an expression, so it goes anywhere one is expected.
  #test (fix f. fun (n : Int) => if n == 0 then 0 else 1 + f (n - 1)) 5 === 5

  def countdown := fix go. fun (n : Int) => if n <= 0 then [] else n :: go (n - 1)
  #test countdown 3 === [3, 2, 1]

  -- `fix` is monomorphically recursive: `f` has one fixed type in the body.
  -- (`def` likewise; there is no polymorphic recursion.)
}

/--
info: Int -> Int
-/
#guard_msgs in
{lait_decl fnFixCheck
  #check fix f. fun (n : Int) => n
}

-- ===== Functions are values, but not comparable =====

{lait_decl fnValues
  def inc (n : Int) : Int := n + 1

  -- Stored, passed, returned...
  def fs := (inc, inc)
  #test (fst fs) 1 === 2

  -- ...but `==` on functions is a run-time error, not a type error.
  #test_error inc == inc ~ "Equality not supported for functions"
}
