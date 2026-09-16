import Lait
#lait

def test (xs : List<Int>) : Int :=
  match xs with
  | Nil => 0
  | _ => false
  end
