import Lait.Elab
import Lait.Stdlib

/-!
# `type` declarations, constructors, and `match`

Three rules worth stating up front: type and constructor names are upper-case
(a lower-case name in a type position is a type variable); constructors are
ordinary curried functions, so `Cons 1 rest`, never `Cons(1, rest)`; and
patterns are one level deep and bind plain names, with no nested patterns,
literal patterns, `as`-patterns or guards.
-/

-- ===== Enumerations =====

{lait_decl dtEnum
  type Color := | Red | Green | Blue

  def toNum (c : Color) : Int :=
    match c with
    | Red => 1
    | Green => 2
    | Blue => 3
    end

  #test toNum Red === 1
  #test toNum Green === 2
  #test toNum Blue === 3

  -- Arm order does not matter.
  def toNum2 (c : Color) : Int :=
    match c with
    | Blue => 3
    | Red => 1
    | Green => 2
    end
  #test toNum2 Green === 2

  -- Nullary constructors are values, and compare structurally.
  #test Red == Red === true
  #test Red == Green === false

  -- A wildcard arm makes the match exhaustive.
  def isRed (c : Color) : Bool :=
    match c with
    | Red => true
    | _ => false
    end
  #test isRed Red === true
  #test isRed Blue === false
}

-- ===== Constructors carrying data =====

{lait_decl dtPayload
  type Shape :=
    | Circle (r : Int)
    | Rect (w : Int) (h : Int)

  def area (s : Shape) : Int :=
    match s with
    | Circle r => 3 * r * r
    | Rect w h => w * h
    end

  #test area (Circle 2) === 12
  #test area (Rect 3 4) === 12

  -- A constructor is a curried function, so it may be partially applied.
  def squareOfSide := Rect 5
  #test area (squareOfSide 5) === 25

  def mkCircle := Circle
  #test area (mkCircle 1) === 3

  -- Declared field names are documentation; patterns bind positionally and may
  -- use any names.
  def widthOr (s : Shape) (d : Int) : Int :=
    match s with
    | Circle _ => d
    | Rect a b => a
    end
  #test widthOr (Rect 7 8) 0 === 7
  #test widthOr (Circle 1) 99 === 99
}

/--
info: Int -> Shape
---
info: Int -> Int -> Shape
-/
#guard_msgs in
{lait_decl dtCtorTypes
  type Shape := | Circle (r : Int) | Rect (w : Int) (h : Int)
  #check Circle
  #check Rect
}

-- ===== Recursive types =====

{lait_decl dtRecursive
  type Nat := | Z | S (n : Nat)

  def toInt (n : Nat) : Int :=
    match n with
    | Z => 0
    | S m => 1 + toInt m
    end
  #test toInt Z === 0
  #test toInt (S (S (S Z))) === 3

  def add (n : Nat) (m : Nat) : Nat :=
    match n with
    | Z => m
    | S k => S (add k m)
    end
  #test toInt (add (S Z) (S (S Z))) === 3

  type Tree :=
    | Leaf (v : Int)
    | Node (l : Tree) (r : Tree)

  def sum (t : Tree) : Int :=
    match t with
    | Leaf v => v
    | Node l r => sum l + sum r
    end
  def depth (t : Tree) : Int :=
    match t with
    | Leaf _ => 1
    | Node l r => 1 + (if depth l > depth r then depth l else depth r)
    end

  def t := Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)
  #test sum t === 6
  #test depth t === 3
  #test sum (Leaf 5) === 5
  #test depth (Leaf 5) === 1
}

-- ===== Polymorphic types =====

{lait_decl dtPolymorphic
  type Opt<a> := | Nothing | Just (v : a)

  def orElse (o : Opt<a>) (d : a) : a :=
    match o with
    | Nothing => d
    | Just v => v
    end
  #test orElse (Just 1) 0 === 1
  #test orElse Nothing 99 === 99
  #test orElse (Just "s") "d" === "s"

  def mapOpt (f : a -> b) (o : Opt<a>) : Opt<b> :=
    match o with
    | Nothing => Nothing
    | Just v => Just (f v)
    end
  #test orElse (mapOpt (fun n => n + 1) (Just 1)) 0 === 2
  #test orElse (mapOpt (fun n => n + 1) Nothing) 0 === 0

  -- Several parameters.
  type Either<a, b> := | Left (l : a) | Right (r : b)

  def isLeft (e : Either<a, b>) : Bool :=
    match e with
    | Left _ => true
    | Right _ => false
    end
  #test isLeft (Left 1) === true
  #test isLeft (Right "s") === false

  type BinTree<a> := | BLeaf (v : a) | BNode (l : BinTree<a>) (r : BinTree<a>)

  def size (t : BinTree<a>) : Int :=
    match t with
    | BLeaf _ => 1
    | BNode l r => size l + size r
    end
  #test size (BNode (BLeaf 1) (BLeaf 2)) === 2
  #test size (BNode (BLeaf "a") (BLeaf "b")) === 2
}

-- ===== Mutually recursive types =====

{lait_decl dtMutualTypes
  type Expr :=
    | Lit (n : Int)
    | Neg (e : Expr)
    | Sum (es : ExprList)
  and ExprList :=
    | ENil
    | ECons (e : Expr) (es : ExprList)

  def evalE (e : Expr) : Int :=
    match e with
    | Lit n => n
    | Neg e' => 0 - evalE e'
    | Sum es => evalL es
    end
  and evalL (es : ExprList) : Int :=
    match es with
    | ENil => 0
    | ECons e rest => evalE e + evalL rest
    end

  #test evalE (Lit 3) === 3
  #test evalE (Neg (Lit 3)) === - 3
  #test evalE (Sum (ECons (Lit 1) (ECons (Neg (Lit 2)) ENil))) === - 1
  #test evalL ENil === 0
}

-- ===== Nested matches =====

{lait_decl dtNestedMatch
  #include stdlib

  -- No nested patterns, so "match the head, then match again" is a `match`
  -- inside an arm.  Each one needs its own `end`.
  def secondOf (xs : List<a>) : Option<a> :=
    match xs with
    | [] => None
    | h :: t =>
      match t with
      | [] => None
      | h2 :: _ => Some h2
      end
    end

  #test secondOf [1, 2, 3] === Some 2
  #test secondOf [1] === None

  -- No `(e : T)` ascription, so an empty list at a chosen element type goes
  -- through an annotated `def`.
  def noInts : List<Int> := []
  #test secondOf noInts === None
}

-- ===== Printing =====

{lait_decl dtPrinting
  #include stdlib
  type Shape := | Circle (r : Int) | Rect (w : Int) (h : Int)

  -- `toString` prints a constructor applied to its arguments, parenthesising
  -- nested applications.
  #test toString Circle === "<function>"
  #test toString (Circle 1) === "Circle 1"
  #test toString (Rect 1 2) === "Rect 1 2"

  type Wrap := | W (s : Shape)
  #test toString (W (Circle 1)) === "W (Circle 1)"

  -- Equality reaches inside constructors.
  #test Circle 1 == Circle 1 === true
  #test Circle 1 == Circle 2 === false
  #test Circle 1 == Rect 1 1 === false
}

-- ===== Errors =====

/-- error: Non-exhaustive match on Color: missing constructor(s) Blue -/
#guard_msgs in
{lait_decl dtNonExhaustive
  type Color := | Red | Green | Blue
  def f (c : Color) : Int :=
    match c with
    | Red => 1
    | Green => 2
    end
}

-- CURRENT BEHAVIOR: only the first missing-constructor list is reported, and the
-- message points at the whole `match`.
/-- error: Non-exhaustive match on Color: missing constructor(s) Green, Blue -/
#guard_msgs in
{lait_decl dtNonExhaustiveTwo
  type Color := | Red | Green | Blue
  def f (c : Color) : Int :=
    match c with
    | Red => 1
    end
}

/-- error: Unknown constructor in match: Purple -/
#guard_msgs in
{lait_decl dtUnknownCtor
  type Color := | Red | Green | Blue
  def f (c : Color) : Int :=
    match c with
    | Red => 1
    | Purple => 2
    end
}

/-- error: Duplicate constructor in match: Red -/
#guard_msgs in
{lait_decl dtDuplicateArm
  type Color := | Red | Green
  def f (c : Color) : Int :=
    match c with
    | Red => 1
    | Red => 2
    | Green => 3
    end
}

/-- error: Constructor Just expects 1 arguments but pattern has 0 -/
#guard_msgs in
{lait_decl dtPatternArity
  type Opt := | Nothing | Just (v : Int)
  def f (o : Opt) : Int :=
    match o with
    | Nothing => 0
    | Just => 1
    end
}

/-- error: Constructor Just expects 1 arguments but pattern has 2 -/
#guard_msgs in
{lait_decl dtPatternArity2
  type Opt := | Nothing | Just (v : Int)
  def f (o : Opt) : Int :=
    match o with
    | Nothing => 0
    | Just a b => 1
    end
}

/-- error: Empty match: cannot determine the type being matched -/
#guard_msgs in
{lait_decl dtEmptyMatch
  type Color := | Red
  def f (c : Color) : Int := match c with end
}

/-- error: Wildcard pattern must be the last arm of a match -/
#guard_msgs in
{lait_decl dtWildcardNotLast
  type Color := | Red | Green
  def f (c : Color) : Int :=
    match c with
    | _ => 0
    | Red => 1
    end
}

/-- error: Declared types must begin with an upper-case letter -/
#guard_msgs in
{lait_decl dtLowerCaseType
  type color := | Red
}

/-- error: Error when defining T2: Constructor C is already defined -/
#guard_msgs in
{lait_decl dtCtorClash
  type T1 := | C (x : Int)
  type T2 := | C (x : String)
}

/-- error: Error when defining T: Constructor C is defined twice in type T -/
#guard_msgs in
{lait_decl dtCtorTwice
  type T := | C (x : Int) | C (y : Int)
}

/-- error: Unknown type constructor: Missing -/
#guard_msgs in
{lait_decl dtUnknownType
  def f (x : Missing) : Int := 0
}

-- CURRENT BEHAVIOR: the arity message says neither how many arguments the type
-- takes nor how many were supplied.
/-- error: Wrong number of arguments to Box -/
#guard_msgs in
{lait_decl dtTypeArity
  type Box<a> := | B (v : a)
  def f (b : Box) : Int := 0
}
