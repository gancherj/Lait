import Lait.Elab
import Lait.Stdlib

/-!
# The standard library

Everything reachable after `#include stdlib` other than the list functions
(TestLists.lean): `Option`, `Map`, the reference wrappers, and `toString`,
`print`, `assert`.
-/

-- ===== Option =====

{lait_decl stdOption
  #include stdlib

  def noInt : Option<Int> := None

  #test Some 1 === Some 1
  #test noInt === None
  #test Some 1 == None === false

  def orElse (o : Option<a>) (d : a) : a :=
    match o with
    | None => d
    | Some v => v
    end
  #test orElse (Some 1) 0 === 1
  #test orElse noInt 99 === 99

  -- `Option.andThen` is the only Option combinator the library ships.
  def half (n : Int) : Option<Int> := if n == 0 then None else Some (n - 1)
  #test Option.andThen (Some 2) half === Some 1
  #test Option.andThen (Some 0) half === None
  #test Option.andThen noInt half === None

  -- Chaining: the failure propagates.
  #test Option.andThen (Option.andThen (Some 3) half) half === Some 1
  #test Option.andThen (Option.andThen (Some 1) half) half === None

  -- `None` is polymorphic.
  def noStr : Option<String> := None
  #test noStr === None
  #test noInt === None

  -- `Some` is an ordinary curried function.
  #test List.map [1, 2] Some === [Some 1, Some 2]
}

/--
info: Option<a>
---
info: a -> Option<a>
---
info: Option<a> -> (a -> Option<b>) -> Option<b>
-/
#guard_msgs in
{lait_decl stdOptionCheck
  #include stdlib
  #check None
  #check Some
  #check Option.andThen
}

-- ===== Map =====

{lait_decl stdMap
  #include stdlib

  -- An association list; `Map.empty` is polymorphic in key and value type.
  def m0 : Map<String, Int> := Map.empty
  def m1 := Map.insert "a" 1 m0
  def m2 := Map.insert "b" 2 m1

  #test Map.lookup m2 "a" === Some 1
  #test Map.lookup m2 "b" === Some 2
  #test Map.lookup m2 "c" === None
  #test Map.lookup m0 "a" === None

  -- Re-inserting replaces rather than shadows.
  def m3 := Map.insert "a" 99 m2
  #test Map.lookup m3 "a" === Some 99
  #test Map.lookup m3 "b" === Some 2

  def m4 := Map.delete m3 "a"
  #test Map.lookup m4 "a" === None
  #test Map.lookup m4 "b" === Some 2
  -- Deleting an absent key is a no-op.
  #test Map.lookup (Map.delete m4 "zz") "b" === Some 2

  -- NOTE the inconsistent argument orders (REPORT.md P7):
  --   Map.insert key value m   -- map last
  --   Map.lookup m key         -- map first
  --   Map.delete m key         -- map first

  -- Any equality-comparable key type works.
  def n0 : Map<Int, String> := Map.empty
  #test Map.lookup (Map.insert 1 "one" n0) 1 === Some "one"
  #test Map.lookup (Map.insert 1 "one" n0) 2 === None

  -- Including compound keys.
  def p0 : Map<Int * Int, Int> := Map.empty
  #test Map.lookup (Map.insert (1, 2) 3 p0) (1, 2) === Some 3
  #test Map.lookup (Map.insert (1, 2) 3 p0) (2, 1) === None
}

-- ===== References =====

{lait_decl stdRefs
  #include stdlib

  -- `alloc`/`get`/`set` are ordinary functions wrapping the three primitives.
  def r := alloc 0
  #test get r === 0
  def _ := set r 5
  #test get r === 5

  -- `set` returns `()`, so sequencing is `let _ := ... in`.
  def bump (c : Ref<Int>) : Int :=
    let _ := set c (get c + 1) in
    get c
  #test bump r === 6
  #test get r === 6

  -- Compared by identity, not contents.
  def a := alloc 1
  def b := alloc 1
  #test a == a === true
  #test a == b === false

  -- Aliasing: two names for one cell see each other's writes.
  def alias := a
  def _ := set alias 42
  #test get a === 42

  -- Any type, including functions, lists and other references.
  def rs := alloc [1, 2]
  def _ := set rs (0 :: get rs)
  #test List.length (get rs) === 3

  def rr := alloc (alloc 7)
  #test get (get rr) === 7

  def rf := alloc (fun (n : Int) => n + 1)
  #test (get rf) 1 === 2

  -- A counter.
  def counter := alloc 0
  def tick () : Int :=
    let _ := set counter (get counter + 1) in
    get counter
  #test tick () === 1
  #test tick () === 2
  #test tick () === 3
}

/--
info: a -> Ref<a>
---
info: Ref<a> -> a
---
info: Ref<a> -> a -> Unit
-/
#guard_msgs in
{lait_decl stdRefsCheck
  #include stdlib
  #check alloc
  #check get
  #check set
}

-- ===== toString =====

{lait_decl stdToString
  #include stdlib

  #test toString 1 === "1"
  #test toString (- 1) === "-1"
  #test toString true === "true"
  #test toString () === "()"
  #test toString (1, 2) === "(1, 2)"
  #test toString [1, 2] === "Cons 1 (Cons 2 Nil)"
  #test toString (Some 1) === "Some 1"
  #test toString None === "None"

  -- CURRENT BEHAVIOR: `toString` of a `String` keeps the quotes, so it is not
  -- the identity on strings and `"a" ++ toString "b"` is `"a\"b\""`.
  -- REPORT.md P8.
  #test toString "b" === "\"b\""

  -- Functions and references stringify to placeholders.
  #test toString (fun x => x) === "<function>"
  #test toString (alloc 1) === "<location>"

  -- Building a message.
  def describe (n : Int) : String := "n = " ++ toString n
  #test describe 5 === "n = 5"
}

-- ===== print and assert =====

{lait_decl stdPrintAssert
  #include stdlib

  -- `print : String -> Unit`.
  def _ := print "a message from the test suite"

  -- `assert` returns `()` when true, and raises otherwise.
  def _ := assert true
  #test assert true === ()
  #test_error assert false ~ "Assertion failed"

  -- A plain function, so its argument is evaluated first: it cannot guard
  -- something that would itself fail.
  #test_error assert (1 == (error "evaluated first")) ~ "evaluated first"
}
