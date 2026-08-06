import Lait
#lait


#check Some 1


def List.head (xs : List<a>) : Option<a> =
  match xs with 
  | [] => None
  | x :: _ => Some x
  end

def List.headIsPositive (xs : List<Int>) : Bool =
  match List.head xs with 
  | None => false -- List is empty, so head is not positive
  | Some x => x > 0
  end

/- -/ 