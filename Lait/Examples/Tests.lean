import Lait
import Lait.Examples.Tests1


{lait_decl my_decls
  #include stdlib
  #include Tests1
  -- def bar := baz
  #eval 42
}


-- #lait
--
--
-- #check Some 1
--
--
-- def List.head (xs : List<a>) : Option<a> :=
--   match xs with
--   | [] => None
--   | x :: _ => Some x
--   end
--
-- def List.headIsPositive (xs : List<Int>) : Bool :=
--   match List.head xs with
--   | None => false -- List is empty, so head is not positive
--   | Some x => x > 0
--   end
--
-- type Status := | Ok | Err
-- type Visibility := | Public | Hidden
--
-- type Result := {
--   label : String,
--   value : Int,
--   threshold : Option<Int>,
--   status : Status,
--   message : Option<String>,
--   visibility : Visibility
-- }
--
-- def exampleResult : Result := {
--   label := "Example",
--   value := 10,
--   threshold := Some 10,
--   status := Ok,
--   message := Some "Example output",
--   visibility := Public
-- }
--
-- /- -/
--
