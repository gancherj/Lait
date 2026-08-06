import Lait.Eval
import Lait.Elab

{lait_decl mutualTest

  -- Mutually recursive types
  type Tree<a> = | Leaf (v : a) | Node (c : Forest<a>)
  and Forest<a> = | FNil | FCons (t : Tree<a>) (f : Forest<a>)

  -- Mutually recursive functions
  def isEven (n : Int) : Bool =
    if n == 0 then true else isOdd (n + (- 1))
  and isOdd (n : Int) : Bool =
    if n == 0 then false else isEven (n + (- 1))

  -- true
  #eval isEven 10
  -- false
  #eval isEven 7
  -- true
  #eval isOdd 3

  #test isEven 4 === true
  #test isOdd 4 === false

  -- size over the mutually recursive trees/forests
  def treeSize (t : Tree<a>) : Int =
    match t with
    | Leaf v => 1
    | Node c => forestSize c
     end
  and forestSize (f : Forest<a>) : Int =
    match f with
    | FNil => 0
    | FCons t f' => treeSize t + forestSize f'
    end

  def myTree : Tree<Int> = Node (FCons (Leaf 1) (FCons (Leaf 2) (FCons (Node (FCons (Leaf 3) FNil)) FNil)))

  -- 3
  #eval treeSize myTree
  #test treeSize myTree === 3

  #check isEven
  #check treeSize
}
