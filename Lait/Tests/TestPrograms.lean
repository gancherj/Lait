import Lait.Elab
import Lait.Stdlib

/-!
# End-to-end programs

Homework-sized programs exercising the features together: an expression
interpreter, a binary search tree, sorting, a stack on a `Ref`, a state machine,
and folds.
-/

-- ===== A small expression language =====

{lait_decl progInterpreter
  #include stdlib

  -- `Int`, `Bool`, `String`, `Unit` and `Ref` are reserved tokens, so they
  -- cannot be constructor names -- hence `BLit`.
  type Expr :=
    | Num (n : Int)
    | BLit (b : Bool)
    | Add (l : Expr) (r : Expr)
    | Mul (l : Expr) (r : Expr)
    | Leq (l : Expr) (r : Expr)
    | If (c : Expr) (t : Expr) (e : Expr)
    | Var (x : String)
    | Let (x : String) (v : Expr) (b : Expr)

  type Value := | VNum (n : Int) | VBool (b : Bool)
  type Env := Map<String, Value>

  def asNum (v : Value) : Int :=
    match v with
    | VNum n => n
    | VBool _ => error "expected a number"
    end

  def asBool (v : Value) : Bool :=
    match v with
    | VBool b => b
    | VNum _ => error "expected a boolean"
    end

  def eval (env : Env) (e : Expr) : Value :=
    match e with
    | Num n => VNum n
    | BLit b => VBool b
    | Add l r => VNum (asNum (eval env l) + asNum (eval env r))
    | Mul l r => VNum (asNum (eval env l) * asNum (eval env r))
    | Leq l r => VBool (asNum (eval env l) <= asNum (eval env r))
    | If c t e' => if asBool (eval env c) then eval env t else eval env e'
    | Var x =>
      match Map.lookup env x with
      | Some v => v
      | None => error ("unbound variable: " ++ x)
      end
    | Let x v b => eval (Map.insert x (eval env v) env) b
    end

  def empty : Env := Map.empty
  def run (e : Expr) : Value := eval empty e

  #test run (Num 1) === VNum 1
  #test run (Add (Num 1) (Num 2)) === VNum 3
  #test run (Mul (Add (Num 1) (Num 2)) (Num 4)) === VNum 12
  #test run (Leq (Num 1) (Num 2)) === VBool true
  #test run (If (Leq (Num 2) (Num 1)) (Num 10) (Num 20)) === VNum 20
  #test run (Let "x" (Num 5) (Add (Var "x") (Var "x"))) === VNum 10

  -- Shadowing in the object language.
  #test run (Let "x" (Num 1) (Let "x" (Num 2) (Var "x"))) === VNum 2
  -- The outer binding survives, since `Map.insert` returns a new map.
  #test run (Let "x" (Num 1) (Add (Let "x" (Num 2) (Var "x")) (Var "x"))) === VNum 3

  #test_error run (Var "nope") ~ "unbound variable: nope"
  #test_error run (Add (Num 1) (BLit true)) ~ "expected a number"
  #test_error run (If (Num 1) (Num 2) (Num 3)) ~ "expected a boolean"

  -- `try` gives a safe front end.
  def runOr (e : Expr) (d : Value) : Value := try run e with d end
  #test runOr (Var "nope") (VNum 0) === VNum 0
  #test runOr (Num 1) (VNum 0) === VNum 1
}

-- ===== A binary search tree =====

{lait_decl progBST
  #include stdlib

  type Tree<a> := | Tip | Bin (l : Tree<a>) (v : a) (r : Tree<a>)

  def insert (t : Tree<Int>) (x : Int) : Tree<Int> :=
    match t with
    | Tip => Bin Tip x Tip
    | Bin l v r =>
      if x < v then Bin (insert l x) v r
      else if x > v then Bin l v (insert r x)
      else t
    end

  def member (t : Tree<Int>) (x : Int) : Bool :=
    match t with
    | Tip => false
    | Bin l v r => if x < v then member l x else if x > v then member r x else true
    end

  def toList (t : Tree<a>) : List<a> :=
    match t with
    | Tip => []
    | Bin l v r => List.append (toList l) (v :: toList r)
    end

  def size (t : Tree<a>) : Int :=
    match t with
    | Tip => 0
    | Bin l _ r => 1 + size l + size r
    end

  def fromList (xs : List<Int>) (t : Tree<Int>) : Tree<Int> :=
    match xs with
    | [] => t
    | h :: rest => fromList rest (insert t h)
    end

  def empty : Tree<Int> := Tip
  def t := fromList [5, 3, 8, 1, 4, 7, 9] empty

  #test size t === 7
  #test toList t === [1, 3, 4, 5, 7, 8, 9]
  #test member t 4 === true
  #test member t 6 === false
  #test member empty 1 === false
  #test toList empty === []

  -- A duplicate insert changes nothing.
  #test size (insert t 5) === 7
  #test toList (insert t 5) === toList t

  -- The tree is polymorphic even though `insert` is not.
  def strs : Tree<String> := Bin Tip "a" Tip
  #test toList strs === ["a"]
  #test size strs === 1
}

-- ===== Sorting =====

{lait_decl progSorting
  #include stdlib
  def none : List<Int> := []

  def insertSorted (x : Int) (xs : List<Int>) : List<Int> :=
    match xs with
    | [] => [x]
    | h :: t => if x <= h then x :: xs else h :: insertSorted x t
    end

  def insertionSort (xs : List<Int>) : List<Int> :=
    match xs with
    | [] => []
    | h :: t => insertSorted h (insertionSort t)
    end

  #test insertionSort none === none
  #test insertionSort [1] === [1]
  #test insertionSort [3, 1, 2] === [1, 2, 3]
  #test insertionSort [1, 2, 3] === [1, 2, 3]
  #test insertionSort [3, 3, 1] === [1, 3, 3]
  #test insertionSort [5, 4, 3, 2, 1] === [1, 2, 3, 4, 5]

  -- Merge sort, whose `split` returns a pair.
  def split (xs : List<Int>) : List<Int> * List<Int> :=
    match xs with
    | [] => (none, none)
    | h :: t =>
      match t with
      | [] => ([h], none)
      | h2 :: rest =>
        let halves := split rest in
        (h :: fst halves, h2 :: snd halves)
      end
    end

  def merge (xs : List<Int>) (ys : List<Int>) : List<Int> :=
    match xs with
    | [] => ys
    | xh :: xt =>
      match ys with
      | [] => xs
      | yh :: yt => if xh <= yh then xh :: merge xt ys else yh :: merge xs yt
      end
    end

  def mergeSort (xs : List<Int>) : List<Int> :=
    match xs with
    | [] => none
    | h :: t =>
      match t with
      | [] => [h]
      | _ =>
        let halves := split xs in
        merge (mergeSort (fst halves)) (mergeSort (snd halves))
      end
    end

  #test mergeSort none === none
  #test mergeSort [1] === [1]
  #test mergeSort [2, 1] === [1, 2]
  #test mergeSort [5, 3, 8, 1, 4, 7, 9] === [1, 3, 4, 5, 7, 8, 9]
  #test mergeSort [3, 3, 3] === [3, 3, 3]
  #test mergeSort [9, 8, 7, 6, 5, 4, 3, 2, 1] === [1, 2, 3, 4, 5, 6, 7, 8, 9]

  -- The two sorts agree.
  def sample := [4, 1, 9, 2, 8, 3, 7]
  #test mergeSort sample === insertionSort sample
}

-- ===== A mutable stack =====

{lait_decl progStack
  #include stdlib

  -- NOTE the space before the final `>`: inside `{lait_decl}`, `Ref<List<a>>`
  -- lexes `>>` as one token and fails to parse.  `#lait` whole-file mode runs
  -- `delete_token ">>"` and is fine.  REPORT.md P2.
  type Stack<a> := Ref<List<a> >

  -- `newStack` has to be a function: the value restriction rejects a `def` whose
  -- body allocates and whose type still has a variable in it.  See
  -- TestValueRestriction.lean.
  def newStack () : Stack<a> := alloc []

  def push (s : Stack<a>) (x : a) : Unit := set s (x :: get s)

  def pop (s : Stack<a>) : Option<a> :=
    match get s with
    | [] => None
    | h :: t =>
      let _ := set s t in
      Some h
    end

  def depth (s : Stack<a>) : Int := List.length (get s)

  -- The annotation is required: `newStack ()` is an application, hence not a
  -- value.
  def s : Stack<Int> := newStack ()
  def _ := push s 1
  def _ := push s 2
  def _ := push s 3

  #test depth s === 3
  #test pop s === Some 3
  #test pop s === Some 2
  #test depth s === 1
  #test pop s === Some 1
  #test pop s === None
  #test depth s === 0

  -- A second stack is independent, and may hold a different type.
  def s2 : Stack<String> := newStack ()
  def _ := push s2 "a"
  #test pop s2 === Some "a"
  #test depth s === 0
}

-- ===== A state machine =====

{lait_decl progStateMachine
  #include stdlib

  type State := | Idle | Running | Done
  type Event := | Start | Finish | Reset

  def step (st : State) (e : Event) : State :=
    match st with
    | Idle => (match e with | Start => Running | _ => Idle end)
    | Running => (match e with | Finish => Done | Reset => Idle | _ => Running end)
    | Done => (match e with | Reset => Idle | _ => Done end)
    end

  def runAll (st : State) (es : List<Event>) : State :=
    match es with
    | [] => st
    | h :: t => runAll (step st h) t
    end

  #test step Idle Start === Running
  #test step Idle Finish === Idle
  #test runAll Idle [Start, Finish] === Done
  #test runAll Idle [Start, Finish, Reset] === Idle
  #test runAll Idle [Finish, Finish] === Idle
  #test runAll Done [Reset, Start] === Running

  -- Counting transitions with a reference.
  def transitions := alloc 0
  def stepCounted (st : State) (e : Event) : State :=
    let _ := set transitions (get transitions + 1) in
    step st e
  def runCounted (st : State) (es : List<Event>) : State :=
    match es with
    | [] => st
    | h :: t => runCounted (stepCounted st h) t
    end
  #test runCounted Idle [Start, Finish, Reset] === Idle
  #test get transitions === 3
}

-- ===== Folds =====

{lait_decl progFolds
  #include stdlib
  def none : List<Int> := []

  def foldl (f : b -> a -> b) (z : b) (xs : List<a>) : b :=
    match xs with
    | [] => z
    | h :: t => foldl f (f z h) t
    end

  def foldr (f : a -> b -> b) (z : b) (xs : List<a>) : b :=
    match xs with
    | [] => z
    | h :: t => f h (foldr f z t)
    end

  def add := fun (x : Int) => fun (y : Int) => x + y
  def consR := fun (x : Int) => fun (acc : List<Int>) => x :: acc
  def snocL := fun (acc : List<Int>) => fun (x : Int) => x :: acc

  #test foldl add 0 [1, 2, 3] === 6
  #test foldr add 0 [1, 2, 3] === 6
  #test foldl add 0 none === 0

  -- `foldl` with cons reverses; `foldr` with cons is the identity.
  #test foldl snocL none [1, 2, 3] === [3, 2, 1]
  #test foldr consR none [1, 2, 3] === [1, 2, 3]

  -- Everything else as a fold.
  def lengthF (xs : List<a>) : Int := foldr (fun _ => fun (n : Int) => n + 1) 0 xs
  #test lengthF [1, 2, 3] === 3
  #test lengthF ["a"] === 1

  def allF (p : a -> Bool) (xs : List<a>) : Bool :=
    foldr (fun x => fun (acc : Bool) => p x && acc) true xs
  #test allF (fun n => n > 0) [1, 2] === true
  #test allF (fun n => n > 1) [1, 2] === false
  #test allF (fun n => n > 0) none === true
}
