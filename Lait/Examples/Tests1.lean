import Lait
#lait

def foo := 1234
def id  := fun x => x

type Tree :=
  | Leaf (v : Int)
  | Node (t1 : Tree) (t2 : Tree)

def test := Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

def test := Cons 1 (Cons 2 [])

#eval test

#eval "hi"

#eval
  let _ := print "hi2" in
  let _ := print "there2" in
  ()


#eval 111
