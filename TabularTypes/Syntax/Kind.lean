import Lott

namespace TabularTypes

nonterminal Kind, κ :=
  | "*"         : star (tex := "\\lottsym{\\star}")
  | κ₀ " ↦ " κ₁ : arr
  | "R" κ       : row (tex := s!"\\lottkw\{R}^\{{κ}}")
  | "C"         : constr
  | "L"         : label
  | "U"         : comm

end TabularTypes
