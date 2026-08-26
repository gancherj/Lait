import Lait.Elab


{lait_decl stdlib

  type List<a> := | Nil | Cons (h : a) (t : List<a>)

  type Option<a> := | None | Some (x : a)

  def List.append (xs : List<a>) (ys : List<a>) : List<a> :=
    match xs with
    | [] => ys
    | h :: t => h :: List.append t ys
    end

  def List.length (xs : List<a>) : Int :=
    match xs with
    | [] => 0
    | h :: t => 1 + List.length t
    end

  def List.member (xs : List<a>) (x : a) : Bool :=
    match xs with
    | [] => false
    | h :: t => if x == h then true else List.member t x
    end

  def List.filter (xs : List<a>) (f : a -> Bool) : List<a> :=
    match xs with
    | [] => []
    | h :: t => if f h then h :: List.filter t f else List.filter t f
    end

  def List.find (xs : List<a>) (f : a -> Bool) : Option<a> :=
    match xs with
    | [] => None
    | h :: t => if f h then Some h else List.find t f
    end

  def List.map (xs : List<a>) (f : a -> b) : List<b> :=
    match xs with
    | [] => []
    | h :: t => f h :: List.map t f
    end


  def Option.andThen (x : Option<a>) (f : a -> Option<b>) : Option<b> :=
    match x with
    | None => None
    | Some x => f x
    end

  type Map<k, v> := | Map (entries : List<k * v>)

  def Map.empty : Map<k, v> := Map []

  def Map.delete_inner (entries : List<k * v>) (key : k) : List<k * v> :=
    List.filter entries (fun kv => fst kv != key)

  def Map.delete (m : Map<k, v>) (key : k) : Map<k, v> :=
    match m with
    | Map entries => Map (Map.delete_inner entries key)
    end

  def Map.insert (key : k) (value : v) (m : Map<k, v>) : Map<k, v> :=
    match m with
    | Map entries => Map ((key, value) :: (Map.delete_inner entries key))
    end

  def Map.lookup (m : Map<k, v>) (key : k) : Option<v> :=
    match m with
    | Map entries =>
      match List.find entries (fun kv => fst kv == key) with
      | Some kv => Some (snd kv)
      | None => None
      end
    end

  -- Write `x` into the mutable reference `r`, wrapping the primitive
  -- `builtin_set` as an ordinary (curried) function.
  def set (r : Ref<a>) (x : a) : Unit := builtin_set(r, x)

  def toString (n : a) : String := %toString {n}

  def print x := internal_print x

  def assert (b : Bool) : Unit :=
    if not b then error "Assertion failed" else ()


}
