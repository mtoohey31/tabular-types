import Lott

namespace TabularTypeInterpreter

nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") Kind, κ :=
  | "*"         : star (tex := "\\star")
  | "L"         : label
  | "R" κ       : row (tex := s!"\\lottkw\{R}^\{{κ}}")
  | "U"         : comm
  | "C"         : constr
  | κ₀ " ↦ " κ₁ : arr

end TabularTypeInterpreter
