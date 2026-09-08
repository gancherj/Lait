import Lait.Eval
import Lait.Elab

{lait_decl genDefTest

  -- Return type omitted.
  def addOne (x : Int) := x + 1
  #test addOne 4 === 5

  -- Parameter types inferred.
  def twice f x := f (f x)
  #test twice addOne 0 === 2

  -- Mixed, with a return type.
  def pickFirst (x : Int) y : Int := x
  #test pickFirst 3 99 === 3

  -- `()` as sugar for `(_ : Unit)`.
  def constFive () := 5
  #test constFive () === 5

  -- Carries over to `and` groups.
  def isEven n := if n == 0 then true else isOdd (n + (- 1))
  and isOdd n := if n == 0 then false else isEven (n + (- 1))
  #test isEven 4 === true
  #test isOdd 3 === true
}
