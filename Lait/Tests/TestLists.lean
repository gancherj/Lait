import Lait.Elab
import Lait.Stdlib

/-!
# Lists

`List` is not built in; it is an ordinary stdlib declaration:

    type List<a> := | Nil | Cons (h : a) (t : List<a>)

The notation is: `[]`, `[a, b, c]` and `::` are sugar for `Nil`/`Cons`, as are
the arms `| [] =>` and `| h :: t =>`.  The sugar is hard-wired to those two
*names*, so it works for any type declaring constructors called `Nil` and
`Cons`, and nothing else -- see `listSugarIsNameBased` at the bottom.
-/

-- ===== Building lists =====

{lait_decl listLiterals
  #include stdlib

  #test [] === Nil
  #test [1] === Cons 1 Nil
  #test [1, 2, 3] === Cons 1 (Cons 2 (Cons 3 Nil))

  -- `::` is right-associative.
  #test 1 :: 2 :: [] === [1, 2]
  #test 1 :: (2 :: []) === [1, 2]
  #test 1 :: [2, 3] === [1, 2, 3]

  -- `::` sits at additive precedence (60), like `+`, `-` and `++`, so an
  -- arithmetic element has to be parenthesised: `1 + 1 :: []` is a parse error
  -- rather than `[2]`.  REPORT.md P4.
  #test (1 + 1) :: [] === [2]
  #test 0 :: (1 + 1) :: [] === [0, 2]

  -- Lists of anything, including lists and pairs.
  #test List.length ["a", "b"] === 2
  #test List.length [[1], [2, 3]] === 2
  #test List.length [(1, "a")] === 1
  #test List.length [true, false] === 2

  -- ...but homogeneous: `[1, "a"]` does not type-check.  See TestTypeErrors.lean.

  -- The empty list at a chosen element type needs an annotated `def`, since
  -- there is no `(e : T)` ascription.
  def noInts : List<Int> := []
  #test List.length noInts === 0
}

-- ===== Matching =====

{lait_decl listMatching
  #include stdlib
  def noInts : List<Int> := []

  def isEmpty (xs : List<a>) : Bool :=
    match xs with
    | [] => true
    | h :: t => false
    end
  #test isEmpty noInts === true
  #test isEmpty [1] === false

  -- The de-sugared spelling of the same function.
  def isEmpty2 (xs : List<a>) : Bool :=
    match xs with
    | Nil => true
    | Cons h t => false
    end
  #test isEmpty2 noInts === true
  #test isEmpty2 [1] === false

  -- Mixing the two spellings in one `match` names the same two constructors, so
  -- it is a "duplicate constructor" error, not two arms.
  def headOr (xs : List<a>) (d : a) : a :=
    match xs with
    | [] => d
    | h :: _ => h
    end
  #test headOr [1, 2] 0 === 1
  #test headOr noInts 99 === 99

  -- `_` works as either binder of a `::` arm.
  def tailOr (xs : List<a>) (d : List<a>) : List<a> :=
    match xs with
    | [] => d
    | _ :: t => t
    end
  #test tailOr [1, 2, 3] noInts === [2, 3]

  -- A wildcard arm covers both cases.
  def anyAt (xs : List<a>) : Int :=
    match xs with
    | [] => 0
    | _ => 1
    end
  #test anyAt noInts === 0
  #test anyAt [1] === 1
}

-- ===== The usual list functions, from scratch =====

{lait_decl listRecursion
  #include stdlib
  def noInts : List<Int> := []

  def len (xs : List<a>) : Int :=
    match xs with
    | [] => 0
    | _ :: t => 1 + len t
    end
  #test len noInts === 0
  #test len [1, 2, 3] === 3

  def sum (xs : List<Int>) : Int :=
    match xs with
    | [] => 0
    | h :: t => h + sum t
    end
  #test sum [1, 2, 3] === 6
  #test sum noInts === 0

  def rev (xs : List<a>) (acc : List<a>) : List<a> :=
    match xs with
    | [] => acc
    | h :: t => rev t (h :: acc)
    end
  #test rev [1, 2, 3] noInts === [3, 2, 1]

  -- NOTE: `++` is string concatenation, not list append.  `xs ++ [n]` is a type
  -- error ("Cannot unify List<Int> with String").  REPORT.md P5.
  def range (n : Int) : List<Int> :=
    if n <= 0 then [] else List.append (range (n - 1)) [n]
  #test range 0 === noInts
  #test range 3 === [1, 2, 3]

  def map (f : a -> b) (xs : List<a>) : List<b> :=
    match xs with
    | [] => []
    | h :: t => f h :: map f t
    end
  #test map (fun n => n + 1) [1, 2, 3] === [2, 3, 4]
  #test map (fun (n : Int) => "x") [1] === ["x"]

  def filter (p : a -> Bool) (xs : List<a>) : List<a> :=
    match xs with
    | [] => []
    | h :: t => if p h then h :: filter p t else filter p t
    end
  #test filter (fun n => n > 1) [1, 2, 3] === [2, 3]

  def foldr (f : a -> b -> b) (z : b) (xs : List<a>) : b :=
    match xs with
    | [] => z
    | h :: t => f h (foldr f z t)
    end
  -- NOTE: `fun` takes exactly one binder, so a two-argument literal is nested
  -- `fun`s.  REPORT.md P3.
  #test foldr (fun (x : Int) => fun (acc : Int) => x + acc) 0 [1, 2, 3] === 6
  #test foldr (fun (x : Int) => fun (acc : List<Int>) => x :: acc) noInts [1, 2] === [1, 2]
}

-- ===== The stdlib's list functions =====

{lait_decl listStdlib
  #include stdlib
  def noInts : List<Int> := []
  def noStrs : List<String> := []

  -- NOTE the argument order: the list comes first in every `List.*` function,
  -- the opposite of the usual `map f xs`.
  #test List.length noInts === 0
  #test List.length [1, 2, 3] === 3

  #test List.append [1, 2] [3] === [1, 2, 3]
  #test List.append noInts [1] === [1]
  #test List.append [1] noInts === [1]

  #test List.member [1, 2, 3] 2 === true
  #test List.member [1, 2, 3] 9 === false
  #test List.member noInts 1 === false
  #test List.member ["a"] "a" === true

  #test List.map [1, 2, 3] (fun n => n + 1) === [2, 3, 4]
  #test List.map noInts (fun n => n + 1) === noInts
  #test List.map [1] (fun (n : Int) => "x") === ["x"]

  #test List.filter [1, 2, 3] (fun n => n > 1) === [2, 3]
  #test List.filter [1, 2, 3] (fun n => n > 9) === noInts

  #test List.find [1, 2, 3] (fun n => n > 1) === Some 2
  #test List.find [1, 2, 3] (fun n => n > 9) === None
  #test List.find noInts (fun n => true) === None
}

-- ===== Printing and equality =====

{lait_decl listPrinting
  #include stdlib
  def noInts : List<Int> := []

  -- CURRENT BEHAVIOR: lists print in constructor form, so `#eval` output cannot
  -- be pasted back into a program.  REPORT.md P6.
  #test toString noInts === "Nil"
  #test toString [1] === "Cons 1 Nil"
  #test toString [1, 2] === "Cons 1 (Cons 2 Nil)"

  -- Equality is structural, and reaches through nesting.
  #test [1, 2] == [1, 2] === true
  #test [1, 2] == [2, 1] === false
  #test [1] == [1, 2] === false
  #test noInts == noInts === true
  #test [[1], [2]] == [[1], [2]] === true
  #test [(1, "a")] == [(1, "a")] === true
}

-- ===== The sugar is tied to the names `Nil` and `Cons` =====

-- `[]`/`::` elaborate to the variables `Nil` and `Cons`, so with no declaration
-- providing them you get a scope error rather than anything about lists.  This
-- is what a missing `#include stdlib` looks like.
/-- error: Variable Nil not found -/
#guard_msgs in
{lait_decl listSugarNeedsStdlib
  #eval []
}

-- Conversely, any type with constructors named `Nil` and `Cons` picks up the
-- notation.
{lait_decl listSugarIsNameBased
  type Weird := | Nil | Cons (h : String) (t : Weird)

  def stringy : Weird := ["a", "b"]
  def count (w : Weird) : Int :=
    match w with
    | [] => 0
    | _ :: t => 1 + count t
    end
  #test count stringy === 2
  #test count ("c" :: stringy) === 3
}

-- ...and a list type under other names does not.
/-- error: Variable Nil not found -/
#guard_msgs in
{lait_decl listSugarOtherNames
  type MyList<a> := | MyNil | MyCons (h : a) (t : MyList<a>)
  def xs : MyList<Int> := []
}
