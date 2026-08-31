import Lait.Eval
import Lait.Elab

{lait_decl tst1

  type List<a> := | Nil | Cons (h : a) (t : List<a>)

  def length (xs : List<a>) : Int :=
    match xs with
    | Nil => 0
    | Cons h t => 1 + length t
    end


  -- List<a> -> Int
  #check length

  -- Val.VConst (Const.Nat 2)
  #eval (length (Cons 1 (Cons 2 Nil)))

}

{lait_decl tst3

  type Pair<a, b> := a * b

  def mkPair (x : a) (y : b) : Pair<a, b> := (x, y)

  def p := mkPair 1 "two"

  #check p
  #eval fst p                                          -- 1
  #eval snd p                                          -- "two"

  type Twice<a> := a * a

  def dup (x : a) : Twice<a> := (x, x)

  #eval fst (dup 3)                                    -- 3

}


{lait_decl tst4

  -- ===== Constants =====
  def kNum := 42
  def kStr := "hello"
  def kUnit := ()
  #eval kNum
  #eval kStr
  #eval kUnit


  -- ===== + =====
  #eval 3 + 4
  def add := fun x => fun y => x + y
  #eval add 5 6

  -- ===== Boolean and comparison operators =====
  #eval true && false                                    -- false
  #eval true || false                                    -- true
  #eval 3 < 4                                            -- true
  #eval 5 > 4                                            -- true
  #eval 4 <= 4                                           -- true
  #eval 5 >= 6                                           -- false
  #eval 3 == 3                                           -- true
  #eval 3 == 4                                           -- false
  #eval "hi" == "hi"                                     -- true


  def r := builtin_alloc(32)

  def _ := builtin_set(r, builtin_get(r) + 1)

  #eval builtin_get(r)

  -- ===== Let bindings =====
  def usingLet := let x := 10 in x + 1
  #eval usingLet                                       -- 11

  def letAnn := let x : Int := 5 in x + 1
  #eval letAnn                                         -- 6


  -- ===== Top-level polymorphism: `id` at two types =====
  def id := fun x => x
  #eval id 7
  #eval id "polymorphism!"


  -- const : forall a b. a -> b -> a, at two instantiations
  def const := fun x => fun y => x
  #eval const 100 "ignored"
  #eval const "kept" 0


  -- compose : forall a b c. (b -> c) -> (a -> b) -> a -> c
  def compose := fun f => fun g => fun x => f (g x)
  def plusOne := fun n => n + 1
  def plusTwo := fun n => n + 2
  #eval compose plusOne plusTwo 10                     -- 13


  -- ===== Pairs, fst, snd =====
  def mkPair := fun x => fun y => (x, y)
  def p := mkPair 1 "two"
  #eval fst p                                          -- 1
  #eval snd p                                          -- "two"

  -- swap : forall a b. a * b -> b * a
  def swap := fun q => (snd q, fst q)
  #eval fst (swap (mkPair 1 2))                        -- 2
  #eval snd (swap (mkPair 7 "kept"))                   -- 7


  -- ===== References =====
  def r2 := builtin_alloc(100)
  #eval builtin_get(r2)
  def doAssign := builtin_set(r2, 200)
  #eval builtin_get(r2)                                -- 200
  #eval builtin_get(r2) + 1                            -- 201

  -- forall a. a -> Ref a
  def cell := fun x => builtin_alloc(x)
  def rNum := cell 5
  def rStr := cell "stored"
  #eval builtin_get(rNum)                              -- 5
  #eval builtin_get(rStr)                              -- "stored"


  -- ===== Annotated defs =====
  def annN : Int := 7
  #eval annN

  def addOne : Int -> Int := fun x => x + 1
  #eval addOne 41                                      -- 42

  -- Annotated lambda parameter.
  def explicitArg := fun (x : Int) => x + 1
  #eval explicitArg 9                                  -- 10


  -- ===== Nullary constructors =====
  type Color := | Red | Green | Blue
  def myColor := Green
  def colorNum :=
    match myColor with
    | Red => 1
    | Green => 2
    | Blue => 3
    end
  #eval colorNum                                       -- 2


  -- ===== Constructor with a field =====
  type OptN := | NoneN | SomeN (x : Int)
  def unwrap := fun o => fun d =>
    match o with
    | NoneN => d
    | SomeN x => x
    end
  #eval unwrap (SomeN 42) 0                            -- 42
  #eval unwrap NoneN 99                                -- 99

  type Foo := optN

  type NatList := | Nil | Cons (h : Int) (t : NatList)

  def sum := fix f.
    fun (xs : NatList) =>
      match xs with
      | Nil => 0
      | Cons h t => h + f t
      end

  type List<a> := | LNil | LCons (h : a) (t : List<a>)

  def length := fix f.
   fun (xs : List<a>) =>
    match xs with
    | LNil => 0
    | LCons h t => 1 + f t
    end

  def length2 (xs : List<a>) : Int :=
    match xs with
    | LNil => 0
    | LCons h t => 1 + length2 t
    end

  #eval length2 (LCons 1 (LCons 2 LNil))                -- 2


  #eval sum (Cons 1 (Cons 2 Nil))

  def test : foo := SomeN 1

  type Opt<a> := | None | Some (x : a)

  #check None
  #check Some





  -- ===== Recursive inductive type (`NatList`, declared above) =====
  def headOr := fun xs => fun d =>
    match xs with
    | Nil => d
    | Cons h t => h
    end
  def threeOnes := Cons 1 (Cons 1 (Cons 1 Nil))
  #eval headOr threeOnes 0                             -- 1
  #eval headOr Nil 99                                  -- 99
  #check threeOnes


  -- ===== `id` at three types in one expression =====
  def usePolyTwice := id (mkPair (id 1) (id "hi"))
  #eval fst usePolyTwice                               -- 1
  #eval snd usePolyTwice                               -- "hi"

}
