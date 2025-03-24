import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

metavar (tex pre := "\\sourcepre", post := "\\sourcepost") Member, m

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") ClassEnvironmentEntry, γc :=
  | "(" sepBy(TCₛ a " ⇝ " «F⊗⊕ω».Aₛ, ", ") " ⇒ " TC a " : " κ ")" " ↦ " m " : " σ " ⇝ " «F⊗⊕ω».A : mk (bind a)

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") ClassEnvironment, Γc (tex := "Γ_{C}") :=
  | "ε"         : empty
  | Γc ", " γc  : ext
  | "(" Γc ")"  : paren notex (expand := return Γc)
  | Γc ", " Γc' : append notex (expand := return .mkCApp `TabularTypeInterpreter.ClassEnvironment.append #[Γc, Γc'])

end TabularTypeInterpreter
