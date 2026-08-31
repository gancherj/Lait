import Lait.Elab
import Lait.Stdlib

/-!
# Polymorphism: what generalizes and what does not

`def` and `let` both generalize -- each is a declaration, and a declaration closes
the type of what it binds over the type variables the enclosing context does not fix
(the Definition of Standard ML, rule 15).  A `fun` parameter does not: it has one
monomorphic type, so a function cannot use its own argument at two types.

The value restriction has its own file: TestValueRestriction.lean; let-polymorphism
and the scope of explicit type variables have TestLetPolymorphism.lean.
-/

-- ===== Top-level defs generalize =====

{lait_decl polyTopLevel
  #include stdlib

  def id x := x
  #test id 1 === 1
  #test id "s" === "s"
  #test id true === true
  #test id (1, "s") === (1, "s")
  #test id id 1 === 1

  def const x y := x
  #test const 1 "ignored" === 1
  #test const "kept" 0 === "kept"

  def compose f g x := f (g x)
  #test compose (fun n => n + 1) (fun n => n * 2) 5 === 11
  #test compose (fun (s : String) => s ++ "!") (fun (n : Int) => "n") 1 === "n!"

  -- Several instantiations in one expression.
  #test fst (id (id 1, id "s")) === 1
  #test snd (id (id 1, id "s")) === "s"

  -- Explicit type variables mean the same thing.
  def swap (p : a * b) : b * a := (snd p, fst p)
  #test swap (1, "s") === ("s", 1)
  #test swap (true, ()) === ((), true)

  -- Over a type constructor's parameter.
  def firstOr (xs : List<a>) (d : a) : a :=
    match xs with
    | [] => d
    | h :: _ => h
    end
  #test firstOr [1] 0 === 1
  #test firstOr ["a"] "d" === "a"
}

/--
info: a -> a
---
info: b -> a -> b
---
info: (c -> a) -> (b -> c) -> b -> a
-/
#guard_msgs in
{lait_decl polySchemes
  def id x := x
  def const x y := x
  def compose f g x := f (g x)
  #check id
  #check const
  #check compose
}

-- ===== `let` generalizes too =====

-- The textbook let-polymorphism example.  `id` is generalized where it is bound, so
-- the two uses instantiate it independently.  REPORT.md P1.
{lait_decl polyLetIsPolymorphic
  def f := let id := fun x => x in (id 1, id "s")
  #test fst f === 1
  #test snd f === "s"
}

-- At a single type it is fine.
{lait_decl polyLetOneType
  #test (let id := fun x => x in (id 1, id 2)) === (1, 2)
}

-- Lifting the helper to the top level does the same thing.
{lait_decl polyLetWorkaround
  def id x := x
  def f := (id 1, id "s")
  #test fst f === 1
  #test snd f === "s"
}

-- ===== `fun` parameters do NOT generalize =====

-- No rank-2 polymorphism: a parameter cannot be used at two types.
/-- error: Cannot unify String with Int -/
#guard_msgs in
{lait_decl polyLambdaIsMonomorphic
  def useTwice := fun f => (f 1, f "s")
}

-- ===== Occurs check =====

-- CURRENT BEHAVIOR: the message names an internal unification variable
-- (`_tcFresh.NN`), whose number shifts whenever anything earlier in the file
-- changes.  REPORT.md E1.
/-- error: Occurs check failed: _tcFresh.0 occurs in _tcFresh.0 -> _tcFresh.1 -/
#guard_msgs in
{lait_decl polyOccursCheck
  def selfApply := fun x => x x
}

-- ===== Instantiation is per-occurrence =====

{lait_decl polyInstantiation
  #include stdlib

  -- Each occurrence gets fresh type variables.
  def pair x y := (x, y)
  def nested := pair (pair 1 "a") (pair true ())
  #test fst (fst nested) === 1
  #test snd (fst nested) === "a"
  #test fst (snd nested) === true

  -- A polymorphic function stored in a data structure is instantiated at the
  -- point it goes in: the list has a single element type.
  def ids := [fun (n : Int) => n, fun (n : Int) => n + 0]
  #test List.length ids === 2

  -- Through user types.
  type Box<a> := | Box (v : a)
  def unbox (b : Box<a>) : a := match b with | Box v => v end
  #test unbox (Box 1) === 1
  #test unbox (Box "s") === "s"
  #test unbox (Box (Box 1)) === Box 1
}

-- ===== Type variables in annotations are universally quantified =====

{lait_decl polyAnnotations
  #include stdlib

  -- A lower-case name in a type position is a type variable, bound implicitly at
  -- the enclosing `def`.  Not a wildcard: the caller chooses it, so the body may
  -- not assume anything about it.
  def idA (x : a) : a := x
  #test idA 1 === 1
  #test idA "s" === "s"

  -- The same variable twice means the two positions must agree.
  def eq2 (x : a) (y : a) : Bool := x == y
  #test eq2 1 1 === true
  #test eq2 "a" "b" === false

  -- An upper-case name is a type constructor, and must have been declared.
  type Box<a> := | Box (v : a)
  def boxInt (n : Int) : Box<Int> := Box n
  #test boxInt 1 === Box 1
}

-- Calling a `(x : a) (y : a)` function at two types is an error, as the shared
-- variable demands.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl polySharedVariable
  def eq2 (x : a) (y : a) : Bool := x == y
  #eval eq2 1 "s"
}

-- ===== An annotated type variable is a promise, not a hint =====

-- A user-written type variable stands for a type the *user* of the definition picks,
-- so the body may not narrow it: the variables a declaration scopes are rigid while
-- its body is checked (`TcEnv.tyVarScope`), and the error lands on the definition
-- rather than on some later call site.  A type variable in SML is a semantic object of
-- its own, never an unknown to be solved for, so the Definition rejects this program
-- for the same reason.  REPORT.md B4.
/--
error: Cannot make the type variable a equal to Int: a is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl polyAnnotationIsAPromise
  -- `a` is chosen by the caller, so `x + 1` is unsound.
  def notReallyPoly (x : a) : a := x + 1
}
