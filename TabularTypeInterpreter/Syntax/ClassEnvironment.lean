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
  | "(" Γc ")"  : paren (expand := return Γc)
  | Γc ", " Γc' : append (expand := return .mkCApp `TabularTypeInterpreter.ClassEnvironment.append #[Γc, Γc'])

end TabularTypeInterpreter
