import Lait.Elab
import Lait.Stdlib

/-!
# `let` generalization, and the scope of explicit type variables

A `let` is a declaration, so -- exactly like a top-level `def` -- the type of what it
binds is *closed* over the type variables the enclosing context does not fix.  This is
rule 15 of the Definition of Standard ML together with the closure operation
`Clos_{C,valbind}` of section 4.8, and the value restriction is part of it: only a
non-expansive bound expression is generalized.

Type variables the user writes are handled the same way as in the Definition: each is
scoped at the innermost declaration in which it occurs unguarded (section 4.6), is rigid
while that declaration's body is checked, and is quantified by that declaration's
closure.
-/

-- ===== Let-polymorphism =====

{lait_decl lpBasics
  #include stdlib

  -- The textbook example.
  def f := let id := fun x => x in (id 1, id "s")
  -- Int * String
  #check f
  #test fst f === 1
  #test snd f === "s"

  -- Nested, and used at three types.
  def g := let k := fun x => fun y => x in ((k 1 "a", k "b" 2), k true ())
  -- (Int * String) * Bool
  #check g
  #test snd g === true

  -- A `let` inside a function body: generalized once, per call.
  def h u := let e := [] in ((List.length (1 :: e), List.length ("s" :: e)), u)
  -- a -> (Int * Int) * a
  #check h
  #test h 0 === ((1, 1), 0)

  -- A local recursive helper is a value (`fix` of a `fun`), so it generalizes too --
  -- though, as in SML, only after the recursion is done: `len` has one fixed type
  -- inside its own body.
  def usesLocal :=
    let len := fix len. fun xs =>
      match xs with
      | [] => 0
      | h :: t => 1 + len t
      end
    in
    (len [1, 2, 3], len ["a"])
  #test usesLocal === (3, 1)

  -- Two helpers, the second used at both of the first's instantiations.
  def m :=
    let dup := fun x => (x, x) in
    let pairUp := fun xs => List.map xs dup in
    (pairUp [1, 2], pairUp ["a"])
  #test fst m === [(1, 1), (2, 2)]
  #test snd m === [("a", "a")]
}

-- What the context fixes is not generalized: `g` is `x`, whose type the parameter
-- already pinned down.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl lpContextFixed
  def f x := let g := x in (g 1, g "s")
}

-- Same when the connection runs through a constraint rather than the type itself.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl lpContextFixedIndirect
  def f x := let g := fun y => x y in (g 1, g "s")
}

-- ===== The value restriction applies to `let` too =====

-- A `let` whose body allocates is monomorphic, but -- unlike a top-level `def` -- the
-- leftover variable is not an error: the rest of the declaration determines it.
{lait_decl lpValueRestriction
  #include stdlib
  def usesRef :=
    let r := builtin_alloc([]) in
    let _ := builtin_set(r, [1, 2, 3]) in
    List.length (builtin_get(r))
  -- Int
  #check usesRef
  #test usesRef === 3
}

-- ... so the cell cannot be used at two element types.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl lpRefNotPolymorphic
  #include stdlib
  def bad :=
    let r := builtin_alloc([]) in
    let f := fun x => (builtin_set(r, x), builtin_get(r)) in
    (f [1], f ["s"])
}

-- A call is expansive, even when it returns a fresh cell.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl lpCallIsExpansive
  #include stdlib
  def mk () := builtin_alloc([])
  def bad :=
    let r := mk () in
    let _ := builtin_set(r, [1]) in
    List.member (builtin_get(r)) "s"
}

-- Each *call* of it, on the other hand, allocates its own cell and may pick its own
-- element type.
{lait_decl lpFreshPerCall
  #include stdlib
  def mk () := builtin_alloc([])
  -- Unit -> Ref<List<a>>
  #check mk
  def ok :=
    let r := mk () in
    let s := mk () in
    let _ := builtin_set(r, [1]) in
    let _ := builtin_set(s, ["a"]) in
    (List.length (builtin_get(r)), List.member (builtin_get(s)) "a")
  #test ok === (1, true)
}

-- A constructor applied to an allocation is expansive as well.
/-- error: Cannot unify Int with String -/
#guard_msgs in
{lait_decl lpCtorOfAlloc
  #include stdlib
  def bad :=
    let o := Some (builtin_alloc([])) in
    match o with
    | None => 0
    | Some r =>
      let _ := builtin_set(r, [1]) in
      if List.member (builtin_get(r)) "s" then 1 else 0
    end
}

-- ===== The scope of an explicit type variable =====

-- The Definition's own example (section 4.6), first form: `a` occurs only inside the
-- inner declaration, so it is scoped there and `id` is generalized over it.
{lait_decl lpTyVarScopedAtLet
  def x := let id : a -> a := fun z => z in (id 1, id "s")
  -- Int * String
  #check x
  #test fst x === 1
}

-- Second form: `a` also occurs unguarded in the outer declaration, so it is scoped
-- there instead -- one variable for the whole `def`, leaving `id` monomorphic.  The
-- Definition rejects this program too: `a` is the caller's to choose, so the body may
-- not pin it to `Int` and then to `String`.
/--
error: Cannot make the type variable a equal to Int: a is chosen by whoever uses this definition, so its body cannot require it to be Int
-/
#guard_msgs in
{lait_decl lpTyVarScopedAtDef
  def x := (let id : a -> a := fun z => z in (id 1, id "s"), fun (z : a) => z)
}

-- A variable the value restriction cannot quantify may not escape the declaration that
-- scopes it (rule 15's side condition `U ∩ tyvars(VE') = ∅`).
/--
error: The type variable(s) a written in the type of x cannot be generalized here: the body of x is not a value, so the value restriction cannot quantify it.  Give x a type that does not mention a, or make its body a value (for instance by turning it into a function).
-/
#guard_msgs in
{lait_decl lpTyVarEscapes
  def f () := let x : a := error "no" in x
}

-- And one the context fixes, rather than the value restriction: `q`'s type is what the
-- annotation names, so `a` is not the caller's to choose after all.
/--
error: The type variable(s) a written in the type of g cannot be generalized here: the surrounding context already fixes it.  Give g a type that does not mention a.
-/
#guard_msgs in
{lait_decl lpTyVarFixedByContext
  def f q := let g : a -> a := q in g
}

-- Two variables of one declaration are chosen separately, so the body may not force
-- them together.
/--
error: Cannot make the type variables b and a equal: each is chosen separately by whoever uses this definition
-/
#guard_msgs in
{lait_decl lpTwoRigidTyVars
  def bad (x : a) (y : b) : Bool := x == y
}

-- An annotated `let` fixes the type, and then it really is fixed.
/-- error: Cannot unify String with Int -/
#guard_msgs in
{lait_decl lpAnnotatedLet
  #include stdlib
  def bad := let xs : List<Int> := [] in "a" :: xs
}
