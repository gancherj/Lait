import Lait
#lait

type Foo := | A | B | C

def f (v : Foo) : Int :=
  match v with
  | A => "hi"
  | B => 32
  | C => 32
  end
