import Lott

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal (tex pre := "\\targetpre", post := "\\targetpost") Kind, K :=
  | "*"         : star (tex := "\\star")
  | K₁ " ↦ " K₂ : arr
  | "L " K      : list (tex := s!"\\lottkw\{L}^\{{K}}")
  | "(" K ")"   : paren notex (expand := return K)

end TabularTypeInterpreter.«F⊗⊕ω»
