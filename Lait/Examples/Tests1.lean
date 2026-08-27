import Lait
#lait

def foo := 1234
def id  := fun x => x

type IntPair := Int * Int

type MyPair<a> := List<List<a>>

type NatTree :=
  | NTLeaf (v : Int)
  | NTNode (l : NatTree) (r : NatTree)

type BinTree<a> :=
  | BTLeaf (v : a)
  | BTNode (l : BinTree<a>) (r : BinTree<a>)

type Tree :=
  | Leaf (v : Int)
  | Node (t1 : Tree) (t2 : Tree)

def test := Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

def testList := Cons 1 (Cons 2 [])

#eval testList

#eval "hi"

#eval 111
