import Lait.Elab
import Lait.Stdlib

/-!
# Pairs, `fst`, `snd`, and the product type `*`

Pairs, not n-tuples: a "triple" is a pair whose second component is a pair, and
`(1, 2, 3)` is a parse error.  `Int * Int * Int` likewise means
`Int * (Int * Int)`.
-/

{lait_decl pairBasics
  #test fst (1, 2) === 1
  #test snd (1, 2) === 2

  -- Components may differ in type.
  def p := (1, "two")
  #test fst p === 1
  #test snd p === "two"

  -- `fst`/`snd` are prefix at 67: tighter than every infix operator, looser
  -- than application, so they take exactly one argument.
  #test fst (1, 2) + 10 === 11
  #test fst (1, 2) == 1 === true

  -- An application inside `fst` needs parentheses.
  def mk (x : Int) : Int * Int := (x, x + 1)
  #test fst (mk 1) === 1
  #test snd (mk 1) === 2
}

{lait_decl pairNesting
  -- A "triple" is a nested pair; `(1, 2, 3)` will not parse.
  def triple := (1, (2, 3))
  #test fst triple === 1
  #test fst (snd triple) === 2
  #test snd (snd triple) === 3

  -- Nesting the other way is a different type.
  def other := ((1, 2), 3)
  #test fst (fst other) === 1
  #test snd (fst other) === 2
  #test snd other === 3

  -- `*` associates right, matching `(1, (2, 3))`.
  def t : Int * Int * Int := (1, (2, 3))
  #test snd (snd t) === 3

  def u : (Int * Int) * Int := ((1, 2), 3)
  #test snd u === 3
}

{lait_decl pairPolymorphic
  def mkPair (x : a) (y : b) : a * b := (x, y)
  def swap (q : a * b) : b * a := (snd q, fst q)
  def dup (x : a) : a * a := (x, x)

  #test fst (swap (mkPair 1 2)) === 2
  #test snd (swap (mkPair 7 "kept")) === 7
  #test fst (dup 3) === 3
  #test snd (dup "s") === "s"

  -- Curry/uncurry.  The parentheses in `(a * b) -> c` are optional: `*` binds
  -- tighter than `->`, as in ML.  See below.
  def curry (f : (a * b) -> c) (x : a) (y : b) : c := f (x, y)
  def uncurry (f : a -> b -> c) (p : a * b) : c := f (fst p) (snd p)

  def addP (p : Int * Int) : Int := fst p + snd p
  def addC (x : Int) (y : Int) : Int := x + y

  #test curry addP 1 2 === 3
  #test uncurry addC (1, 2) === 3
}

-- A scheme is printed with the names its declaration wrote: `swap`, declared
-- `(q : a * b) : b * a`, reports exactly that.  `mkPair` is reported through a fresh
-- instantiation, which keeps no names -- but the generated ones are handed out in order
-- of first appearance, so they line up with the declaration anyway.  REPORT.md.
/--
info: a -> b -> a * b
---
info: a * b -> b * a
---
info: Int * String
-/
#guard_msgs in
{lait_decl pairCheck
  def mkPair (x : a) (y : b) : a * b := (x, y)
  def swap (q : a * b) : b * a := (snd q, fst q)
  #check mkPair
  #check swap
  #check (1, "s")
}

-- ===== Type-level `*` and `->` =====

-- `*` binds tighter than `->`, as in ML, so `Int * Int -> Int` is a function on
-- pairs and the parentheses in `(Int * Int) -> Int` are redundant -- the two
-- declarations below have the same type, and both print without them.  REPORT.md P15.
/--
info: (Int * Int -> Int) -> Int
---
info: (Int * Int -> Int) -> Int
---
info: Int -> Int * Int
---
info: Int * (Int -> Int) -> Int
-/
#guard_msgs in
{lait_decl pairTyPrecedence
  -- Takes a function from a pair of `Int`s.
  def pairArg (f : Int * Int -> Int) : Int := 0
  #check pairArg
  -- The same type, written with the grouping spelled out.
  def pairArgParens (f : (Int * Int) -> Int) : Int := 0
  #check pairArgParens
  -- `->` reaches to the right, so a product in result position needs nothing.
  def res : Int -> Int * Int := fun x => (x, x)
  #check res
  -- A function *inside* a pair is where the parentheses are needed, and they are
  -- printed back.
  def fnInPair (p : Int * (Int -> Int)) : Int := 0
  #check fnInPair
}

{lait_decl pairEquality
  -- Componentwise.
  #test (1, 2) == (1, 2) === true
  #test (1, 2) == (1, 3) === false
  #test ((1, 2), 3) == ((1, 2), 3) === true
  #test ("a", true) == ("a", true) === true

  -- ...unless a component is a function, which is a run-time error.
  #test_error (1, fun x => x) == (1, fun x => x) ~ "Equality not supported for functions"
}

{lait_decl pairInData
  #include stdlib

  -- Pairs go inside lists, refs, and constructors.
  def ps := [(1, "a"), (2, "b")]
  #test List.length ps === 2
  #test fst (List.length ps, "n") === 2

  def r := alloc (1, 2)
  def _ := set r (3, 4)
  #test fst (get r) === 3

  -- The stdlib `Map` is exactly this: a list of key/value pairs.
  #test Map.lookup (Map.insert 1 "one" Map.empty) 1 === Some "one"
}

-- ===== No pattern matching on pairs =====

{lait_decl pairNoPatterns
  -- `match p with | (x, y) => ...` does not parse: `match` takes only
  -- constructor patterns.  Use `fst`/`snd`, or `let`.
  def addP (p : Int * Int) : Int :=
    let x := fst p in
    let y := snd p in
    x + y
  #test addP (1, 2) === 3
}
