import Lait

/-!
# `#lait` file mode

`#lait` switches the rest of the `.lean` file into Lait: every following command
is a single `lait_decl`, elaborated into one module named after the file (here
`TestLaitMode`), with `stdlib` already included.  This is the mode homework is
written in; `{lait_decl NAME ... }` blocks are the test suite's mode, since they
let one file hold many independent modules.

Everything below the `#lait` line must be Lait, so no `#guard_msgs`: this file
checks only the happy path.
-/

#lait

-- The stdlib is in scope without an explicit `#include`.
#test List.length [1, 2, 3] === 3
#test Some 1 === Some 1
#test Map.lookup (Map.insert "a" 1 Map.empty) "a" === Some 1

-- Ordinary declarations, in the file's own module.
def double (n : Int) : Int := n * 2
#test double 21 === 42

type Fruit := | Apple | Pear
def name (f : Fruit) : String :=
  match f with
  | Apple => "apple"
  | Pear => "pear"
  end
#test name Pear === "pear"

type Tree<a> := | Leaf (v : a) | Node (l : Tree<a>) (r : Tree<a>)
def size (t : Tree<a>) : Int :=
  match t with
  | Leaf _ => 1
  | Node l r => size l + size r
  end
#test size (Node (Leaf 1) (Leaf 2)) === 2

def isEven (n : Int) : Bool := if n == 0 then true else isOdd (n - 1)
and isOdd (n : Int) : Bool := if n == 0 then false else isEven (n - 1)
#test isEven 10 === true

def counter := alloc 0
def _ := set counter (get counter + 1)
#test get counter === 1

#test_error error "boom" ~ "boom"
#test (try error "boom" with 0 end) === 0

-- `#lait` runs `delete_token ">>"`, so no space is needed before the closing
-- bracket here; inside `{lait_decl}` the same type is a parse error.
-- REPORT.md P2.
def firstOr (xs : Option<List<Int>>) (d : Int) : Int :=
  match xs with
  | None => d
  | Some ys =>
    match ys with
    | [] => d
    | h :: _ => h
    end
  end
#test firstOr (Some [1, 2]) 0 === 1
#test firstOr None 9 === 9
