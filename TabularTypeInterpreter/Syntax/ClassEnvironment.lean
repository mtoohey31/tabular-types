import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal ClassEnvironmentEntry, γc :=
  | "(" sepBy(TCₛ a " ⇝ " «F⊗⊕ω».Aₛ, ", ") " ⇒ " TC a " : " κ ")" " ↦ " m " : " σ " ⇝ " «F⊗⊕ω».A : mk (bind a)

nosubst
nonterminal ClassEnvironment, Γc :=
  | "ε"        : empty
  | Γc ", " γc : ext

end TabularTypeInterpreter
