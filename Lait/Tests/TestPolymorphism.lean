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
info: a -> b -> a
---
info: (a -> b) -> (c -> a) -> c -> b
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

-- The letters run `a`, `b`, `c`, ... in the order the reader meets them, however many a
-- declaration needs.
/-- info: a -> b -> c -> d -> e -> f -> g -> h -> a * b * c * d * e * f * g * h -/
#guard_msgs in
{lait_decl polyManyVariables
  def oct p q r s t u v w := (p, (q, (r, (s, (t, (u, (v, w)))))))
  #check oct
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
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl polyLambdaIsMonomorphic
  def useTwice := fun f => (f 1, f "s")
}

-- ===== Occurs check =====

-- The unknowns are named `a`, `b`, ... within the message, so it says the same thing
-- however many constraints were generated before it.  The two occurrences of `a` are one
-- variable -- that is what the occurs check is complaining about.
/-- error: Occurs check failed: a occurs in a -> b -/
#guard_msgs in
{lait_decl polyOccursCheck
  def selfApply := fun x => x x
}

-- The naming is per-message, not per-elaboration, so the same mistake reads the same
-- however many constraints came before it.  This block generates plenty and still says
-- `a`; with the raw internal names it said `_tcFresh.<N>` for a large, drifting `N`.
/-- error: Occurs check failed: a occurs in a -> b -/
#guard_msgs in
{lait_decl polyOccursCheckStableName
  #include stdlib
  def pad1 x := (x, x)
  def pad2 y := [y, y]
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

-- The same holds for a variable written *only* in the return type.  Every `def` with
-- parameters is desugared by `elabDefMutual`, which pins the declared return type with a
-- synthetic `$mutual$ret` let; that let scopes nothing of its own, so its annotation has
-- to fall to the enclosing `def` (`ExpX.unguardedTyVars`).  Until it did, `a` here was an
-- ordinary unification variable and this was accepted as `Int -> Int`.  REPORT.md B4.
/--
error: Cannot make the type variable a equal to Int: a is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl polyReturnOnlyIsAPromise
  def retOnly (x : Int) : a := x
}

-- ...and inside an `and` group, where the pin is the only place the return type appears.
/--
error: Cannot make the type variable a equal to Int: a is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl polyReturnOnlyMutual
  def f (x : Int) : a := g x
  and g (y : Int) : a := y
}

-- A return-only variable the body never constrains is still genuinely polymorphic: the
-- rigidity check must not reject one, only refuse to narrow it.
/-- info: Int -> a -/
#guard_msgs in
{lait_decl polyReturnOnlyStaysPolymorphic
  def alwaysFails (x : Int) : a := error "nope"
  #check alwaysFails
}

-- Rigidity has to hold at the solve that *discharges* a constraint, not just while it is
-- generated.  A `def` with parameters gets an inner solve for free -- `elabDefMutual`'s
-- return-type pin is a `let`, and every `let` solves -- but a `def` with none has only
-- the declaration's final solve.  While that ran outside the scope, a no-parameter `def`
-- never had its declared variables checked at all.  REPORT.md B4.
/--
error: Cannot make the type variable c equal to Int: c is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl polyNoParamSignatureIsAPromise
  def noArgs3 : c -> Int := fun y => y + 1
}

-- The same when the variable is written on an inner `fun` rather than in a signature.
/--
error: Cannot make the type variable c equal to Int: c is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl polyNoParamInnerAnnotation
  def noArgs2 := fun (y : c) => y + 1
}

-- `#eval` is a `val it = e` declaration, so it scopes its type variables the same way.
/--
error: Cannot make the type variable c equal to Int: c is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl polyEvalScopesTyVars
  #eval (fun (y : c) => y + 1) 2
}

-- Still no over-rejection: a no-parameter `def` whose body leaves its declared variable
-- alone stays polymorphic.
/-- info: a -> Int -/
#guard_msgs in
{lait_decl polyNoParamStaysPolymorphic
  def constly : c -> Int := fun _ => 1
  #check constly
}
