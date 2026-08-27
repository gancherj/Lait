import Lait
#lait

def foo := 1234
def id  := fun x => x

#eval
  let _ := print "hi" in
  let _ := print "there" in
  ()

#eval
  let _ := print "hi2" in
  let _ := print "there2" in
  ()


#eval 111
