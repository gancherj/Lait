import Lait
#lait


-- The following are rejected because the type variable is out of scope.
-- Each is expected to be red: this file is the demonstration.

-- Type aliases: `a` is not a parameter of `Bad1`, so it is not in scope in the body.
-- (Previously it silently became one, giving `Bad1` an arity nobody wrote.)
type Bad1 := a * a

-- Datatypes: `a` is not a parameter of `Bad2`, so `Bad`'s field has no type to be.
-- (Previously it was existential -- `Bad 3` and `Bad true` both had type `Bad2`, and
-- reading the field back at `Int` was a well-typed program that crashed.)
type Bad2 := | Bad (val : a)


-- Declaring the parameter is what both of them meant:
type Good1<a> := a * a
type Good2<a> := | Good (val : a)

def foo : Good1<Int> := (3, 5)
def bar : Good2<Int> := Good 3
