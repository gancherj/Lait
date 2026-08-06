# Intro to Lait

Lait is a simple programming language embedded in the Lean proof assistant, intended 
to be used for teaching programming languages courses. 
It has an [ML-like](https://en.wikipedia.org/wiki/ML_(programming_language)) syntax and type system; 
if you don't know what that is, that's OK; we will explain it as we go along.

### Getting Started


TODO: Installation instructions, once we have open-sourced it 

Once we have a Lean project up and running with Lait added as a dependency, we can start writing Lait programs.
To get started, create a new Lean file with the following contents:
```
import Lait
#lait
```

The first line imports the Lait library into Lean, while the second line enables Lait. 

Now, type the following code into the file:
```
#eval 1 + 1
```

This should highlight and evaluate to `2`.
Hovering over `1 + 1`

In this tutorial, we will mostly be using `#eval` to evaluate expressions.

### Simple Data   

Lait supports integers, which we call `Int`.



Lait programs live inside a Lean file. A file starts with `import Lait` and then
`#lait`, which switches the rest of the file over to Lait syntax.

```lean
import Lait
#lait

def my_max (a : Int) (b : Int) : Int =
  if a < b then b else a

#eval my_max 10 4
```

Each code block continues the same file, so `my_max` is still in scope further
down the page. `#test e1 === e2` checks that both sides evaluate to the same
value:

```lean
#test (my_max 4 10) === 10
#test (my_max (-1) 0) === 0

#test 1 === 2
```

Lists, `Option`, and a handful of functions over them come from the standard
library, which `#lait` includes. `match` scrutinises a value one constructor at a
time and is closed by `end`:

```lean
def all_greater? (l : List<Int>) (k : Int) : Bool =
  match l with
  | [] => true
  | h :: t => if h > k then all_greater? t k else false
  end

#test (all_greater? [1, 2, 3] 0) === true
#test (all_greater? [1, 2, 3] 1) === false
```

New datatypes are introduced with `type`, listing one constructor per `|`:

```lean
type Tree = | Leaf (value : Int) | Node (left : Tree) (right : Tree)

def sum_tree (t : Tree) : Int =
  match t with
  | Leaf x => x
  | Node l r => sum_tree l + sum_tree r
  end

#eval sum_tree (Node (Leaf 10) (Node (Leaf 20) (Leaf 30)))
```
