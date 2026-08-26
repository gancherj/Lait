import Lait.Stdlib
import Lait.Elab

{lait_decl refsTest
  #include stdlib

  -- ===== The primitives =====
  -- `builtin_alloc(e)`, `builtin_get(r)` and `builtin_set(r, e)` are the three
  -- built-in operations on mutable references.
  def p := builtin_alloc(100)
  #test builtin_get(p) === 100
  def _ := builtin_set(p, 200)
  #test builtin_get(p) === 200

  -- ===== The stdlib wrappers =====
  -- ∀ a. (a -> Ref<a>)
  #check alloc
  -- ∀ a. (Ref<a> -> a)
  #check get
  -- ∀ a. (Ref<a> -> (a -> Unit))
  #check set

  def r := alloc 100
  #test get r === 100

  def _ := set r 300
  #test get r === 300

  -- Being ordinary functions, they can be partially applied and passed around.
  def setR := set r
  def _ := setR 400
  #test get r === 400

  def bump (c : Ref<Int>) : Unit := set c (get c + 1)
  def _ := bump r
  #test get r === 401

  -- `alloc`/`get`/`set` compose like any other functions.
  def _ := set (alloc 0) 1
  #test get (alloc "fresh") === "fresh"

  -- All three are polymorphic in the referenced type.
  def s := alloc "hello"
  def _ := set s "world"
  #test get s === "world"

  def nested := alloc (alloc 7)
  #test get (get nested) === 7

  -- References hold any value, including lists.
  def xs := alloc [1, 2, 3]
  def _ := set xs (0 :: get xs)
  #test List.length (get xs) === 4

  -- ===== Sequencing writes =====
  def counter := alloc 0
  def incr () : Unit := set counter (get counter + 1)
  def _ := incr ()
  def _ := incr ()
  def _ := incr ()
  #test get counter === 3
}
