import Lait.Elab

{lait_decl tst2
  def blah := 32

  def forever := fix f. fun (_ : Unit) => f ()

  #test_error forever () ~ "Step limit exceeded"

}

{lait_decl tst3_include
  #include tst2
  #eval blah

  def blah2 := true

  def foo := blah2
  -- A no-op: spliced in twice, `blah` would be a duplicate definition.
  #include tst2

  #eval foo


}

{lait_decl tst3
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
