import Lait.Eval
import Lait.Elab

{lait_decl wildTest

  type Color := | Red | Green | Blue

  -- Wildcard as the last arm makes the match exhaustive even though Green and
  -- Blue are not listed explicitly.
  def isRed (c : Color) : Bool :=
    match c with
    | Red => true
    | _ => false
    end

  #eval isRed Red                                        -- true
  #eval isRed Green                                      -- false
  #eval isRed Blue                                       -- false

  -- A wildcard-only match: binds nothing, always succeeds.
  def always (c : Color) : Int :=
    match c with
    | _ => 42
    end

  #eval always Blue                                      -- 42

}
