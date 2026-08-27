import Lait
#lait

def foo := 1234
def id  := fun x => x

type Tree :=
  | Leaf (v : Int)
  | Node (t1 : Tree) (t2 : Tree)

def test := Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

def testList := Cons 1 (Cons 2 [])

#eval testList

#eval "hi"

#eval
  let true := 42 in
  true


#eval 111
