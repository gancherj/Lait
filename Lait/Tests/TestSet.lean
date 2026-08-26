import Lait.Stdlib
import Lait.Elab

{lait_decl setTest
  #include stdlib

  -- The primitive: `builtin_set(r, e)` writes `e` into the reference `r`.
  def r := alloc 100
  #test !r === 100
  def _ := builtin_set(r, 200)
  #test !r === 200

  -- The stdlib wrapper is an ordinary curried function over the primitive.
  def _ := set r 300
  #test !r === 300

  -- ...so it can be partially applied and passed around like any function.
  def setR := set r
  def _ := setR 400
  #test !r === 400

  def bump (c : Ref<Int>) : Unit := set c ((!c) + 1)
  def _ := bump r
  #test !r === 401

  -- `set` is polymorphic in the referenced type.
  def s := alloc "hello"
  def _ := set s "world"
  #test !s === "world"

  -- ∀ a. (Ref<a> -> (a -> Unit))
  #check set

  -- Writing through a non-reference is a type error, as is writing a value of
  -- the wrong type; both are checked statically, so we can only test the
  -- runtime behaviour of well-typed programs here.
  def counter := alloc 0
  def incr () : Unit := set counter ((!counter) + 1)
  def _ := incr ()
  def _ := incr ()
  def _ := incr ()
  #test !counter === 3
}
