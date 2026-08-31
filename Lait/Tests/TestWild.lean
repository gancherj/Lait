import Lait.Eval
import Lait.Elab

{lait_decl wildTest

  type Color := | Red | Green | Blue

  -- A wildcard last arm makes the match exhaustive.
  def isRed (c : Color) : Bool :=
    match c with
    | Red => true
    | _ => false
    end

  #eval isRed Red                                        -- true
  #eval isRed Green                                      -- false
  #eval isRed Blue                                       -- false

  -- Wildcard-only: binds nothing, always succeeds.
  def always (c : Color) : Int :=
    match c with
    | _ => 42
    end

  #eval always Blue                                      -- 42

}
