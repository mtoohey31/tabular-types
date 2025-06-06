import Lott

namespace TabularTypeInterpreter

nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") Kind, κ :=
  | "*"         : star (tex := "\\star")
  | κ₀ " ↦ " κ₁ : arr
  | "R" κ       : row (tex := s!"\\lottkw\{R}^\{{κ}}")
  | "C"         : constr
  | "L"         : label
  | "U"         : comm

end TabularTypeInterpreter
