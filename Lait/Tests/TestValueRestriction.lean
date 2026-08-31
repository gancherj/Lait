import Lait.Elab
import Lait.Stdlib

-- The value restriction.  With `Ref` in the language, generalizing a definition
-- whose body allocates is unsound: `def r := builtin_alloc([])` at
-- `∀ a. Ref<List<a>>` would let one use store `Int`s into the single cell and
-- another read them back as `String`s.  So only a *value* -- a body whose
-- evaluation allocates nothing and has no effects -- is generalized.

-- ===== Values still generalize =====

{lait_decl vrValues
  #include stdlib

  -- Functions are values.
  -- a -> a
  #check fun x => x
  def idf x := x
  -- a -> a
  #check idf

  -- Variables, constants, nullary constructors.
  def myId := idf
  -- a -> a
  #check myId
  -- List<a>
  #check []
  -- Option<a>
  #check None

  -- A constructor applied to values is a value, even though it reaches the type
  -- checker as an application of its generated `def`.
  def oneEmpty := Some []
  -- Option<List<a>>
  #check oneEmpty
  -- Map<b,a>
  #check Map.empty

  -- Pairs, constructor applications, and `let` of values.
  def twoIds := (idf, idf)
  -- (b -> b) * (a -> a)
  #check twoIds
  def boxed := ([], None)
  -- List<b> * Option<a>
  #check boxed
  def viaLet := let e := [] in (e, e)
  -- List<b> * List<a>
  #check viaLet

  -- Each function of an `and` group is a projection out of one recursive bundle
  -- (`elabDefMutual`); projections out of a value are values, so the group
  -- generalizes.
  def firstOf xs :=
    match xs with
    | [] => None
    | h :: t => Some h
    end
  and lastOf xs :=
    match xs with
    | [] => None
    | h :: t => if List.length t == 0 then Some h else lastOf t
    end
  -- List<a> -> Option<a>
  #check firstOf
  -- List<a> -> Option<a>
  #check lastOf
  #test firstOf [1, 2, 3] === Some 1
  #test lastOf [1, 2, 3] === Some 3

  -- The real test: each used at two element types, which only type-checks if the
  -- scheme is polymorphic.
  def emptyList := []
  #test List.length (1 :: emptyList) === 1
  #test List.length ("one" :: emptyList) === 1
  #test fst viaLet === emptyList
  #test List.length (true :: fst viaLet) === 1
  #test (fst twoIds) 1 === 1
  #test (snd twoIds) "one" === "one"
  #test Map.lookup (Map.insert 1 "one" Map.empty) 1 === Some "one"
  #test Map.lookup (Map.insert "one" 1 Map.empty) "one" === Some 1
  #test firstOf [1] === Some 1
  #test firstOf ["one"] === Some "one"
  #test myId 1 === 1
  #test myId "one" === "one"
  #test List.length (1 :: fst boxed) === 1
  #test List.length ("one" :: fst boxed) === 1
  def atInts (o : Option<List<Int> >) : Int := 0
  def atStrs (o : Option<List<String> >) : Int := 0
  #test atInts oneEmpty === 0
  #test atStrs oneEmpty === 0
}

-- ===== Non-values with no type variables left =====

{lait_decl vrMonomorphic
  #include stdlib

  -- Allocation is expansive, but `Ref<Int>` has nothing to generalize.
  def counter := builtin_alloc(0)
  def _ := builtin_set(counter, builtin_get(counter) + 1)
  #test builtin_get(counter) === 1

  -- Likewise any application whose result type is fully determined.
  def three := List.length [1, 2, 3]
  #test three === 3
}

-- ===== Non-values with leftover type variables are rejected =====

/--
error: Value restriction: the body of r is not a value, so its type Ref<List<_a>> cannot be generalized.  Give r a type annotation that fixes the remaining type variable(s), or make its body a value (for instance by turning it into a function).
-/
#guard_msgs in
{lait_decl vrAlloc
  #include stdlib
  -- Without the restriction all three declarations type-check, and the `#eval`
  -- prints `Cons 1 (Cons 2 (Cons 3 Nil))` at type `List<String>` while
  -- `List.member` compares an `Int` against a `String`.
  def r := builtin_alloc([])
  def _ := builtin_set(r, [1, 2, 3])
  def leaked : List<String> := builtin_get(r)
  #eval List.member leaked "one"
}

-- Same for an ordinary application: only constructors are exempt.
/--
error: Value restriction: the body of xs is not a value, so its type List<_a> cannot be generalized.  Give xs a type annotation that fixes the remaining type variable(s), or make its body a value (for instance by turning it into a function).
-/
#guard_msgs in
{lait_decl vrApp
  #include stdlib
  def idf x := x
  def xs := idf []
}

-- A binder shadowing a constructor is an ordinary variable, so applying it is
-- expansive like any other call.
/--
error: Value restriction: the body of shadowed is not a value, so its type Ref<List<_a>> cannot be generalized.  Give shadowed a type annotation that fixes the remaining type variable(s), or make its body a value (for instance by turning it into a function).
-/
#guard_msgs in
{lait_decl vrShadowedCtor
  #include stdlib
  def shadowed := let Cons := alloc in Cons []
}

-- Writing the type variable out does not buy generalization back: the body still
-- allocates, so `a` would still be shared by every use.
/--
error: Value restriction: the body of r is not a value, so its type Ref<List<_a>> cannot be generalized.  Give r a type annotation that fixes the remaining type variable(s), or make its body a value (for instance by turning it into a function).
-/
#guard_msgs in
{lait_decl vrAnnotatedPoly
  #include stdlib
  def r : Ref<List<a> > := builtin_alloc([])
}

-- ===== The two ways out =====

{lait_decl vrWorkarounds
  #include stdlib

  -- Pin the type, giving up polymorphism.
  def ints : Ref<List<Int> > := builtin_alloc([])
  def _ := builtin_set(ints, [1, 2])
  #test List.length (builtin_get(ints)) === 2

  -- Or make the body a value by turning it into a function, so each call
  -- allocates its own cell.  `freshRef` is then a value and generalizes, and
  -- every call may pick a different element type.
  def freshRef () := builtin_alloc([])
  -- Unit -> Ref<List<a>>
  #check freshRef
  def useTwice () : Int :=
    let ints := freshRef () in
    let strs := freshRef () in
    let _ := builtin_set(ints, [1]) in
    let _ := builtin_set(strs, ["one"]) in
    List.length (builtin_get(ints)) + List.length (builtin_get(strs))
  #test useTwice () === 2
}

-- ===== `#check` reports what it cannot generalize =====

-- `#check` binds nothing, so an un-generalizable type is not an error there.
-- Weak variables print as `_a`, `_b`, ... rather than as `a`, `b`, ...
/--
info: Ref<List<_a>>
---
info: List<a>
-/
#guard_msgs in
{lait_decl vrCheck
  #include stdlib
  #check builtin_alloc([])
  #check []
}
