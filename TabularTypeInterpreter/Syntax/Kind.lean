import Lott

namespace TabularTypeInterpreter

nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") Kind, κ :=
  | "*"         : star (tex := "\\star")
  | κ₀ " ↦ " κ₁ : arr
  | "L"         : label
  | "U"         : comm
  | "R" κ       : row (tex := s!"\\lottkw\{R}^\{{κ}}")
  | "C"         : constr

end TabularTypeInterpreter
