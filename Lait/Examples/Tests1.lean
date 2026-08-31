import Lait
#lait

def foo := 1234
def id  := fun x => x

type IntPair := Int * Int

#check alloc []

def churchBool (x : a) (y : a) : a := x

type MyPair<a> := List<List<a>>

type NatTree :=
  | NTLeaf (v : Int)
  | NTNode (l : NatTree) (r : NatTree)

def test (t : NatTree) :=
  match t with
  | NTNode x y => 3
  | NTLeaf _ => 2
  end

type BinTree<a> :=
  | BTLeaf (v : a)
  | BTNode (l : BinTree<a>) (r : BinTree<a>)

type Tree :=
  | Leaf (v : Int)
  | Node (t1 : Tree) (t2 : Tree)

def fib? := fix f. fun n => if n < 2 then 1 else f (n - 1) + f (n - 2)
#eval fib? 17


def test := Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

def testList := Cons 1 (Cons 2 [])

#eval testList

#eval "hi"

#eval 111
