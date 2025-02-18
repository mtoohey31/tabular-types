import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

metavar Member, m

nosubst
nonterminal ClassEnvironmentEntry, γc :=
  | "(" sepBy(TCₛ a " ⇝ " «F⊗⊕ω».Aₛ, ", ") " ⇒ " TC a " : " κ ")" " ↦ " m " : " σ " ⇝ " «F⊗⊕ω».A : mk (bind a)

nosubst
nonterminal ClassEnvironment, Γc :=
  | "ε"         : empty
  | Γc ", " γc  : ext
  | "(" Γc ")"  : paren (desugar := return Γc)
  | Γc ", " Γc' : append (elab := return Lean.mkApp2 (.const `TabularTypeInterpreter.ClassEnvironment.append []) Γc Γc')

end TabularTypeInterpreter
