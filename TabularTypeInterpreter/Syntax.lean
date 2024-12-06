import Lott
import TabularTypeInterpreter.«F⊗⊕ω»

namespace TabularTypeInterpreter

nonterminal Kind, κ :=
  | "*"         : star
  | κ₀ " ↦ " κ₁ : arr
  | "L"         : label
  | "U"         : comm
  | "R" κ       : row
  | "C"         : constr

end TabularTypeInterpreter
