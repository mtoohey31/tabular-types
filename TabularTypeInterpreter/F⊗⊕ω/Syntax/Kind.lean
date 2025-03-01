import Lott

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal Kind, K :=
  | "*"         : star
  | K₁ " ↦ " K₂ : arr
  | "L " K      : list
  | "(" K ")"   : paren (expand := return K)

end TabularTypeInterpreter.«F⊗⊕ω»
