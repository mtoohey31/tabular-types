import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

metavar Member, m

nosubst
nonterminal ClassEnvironmentEntrySuper, γcₛ :=
  | TCₛ a " ⇝ " «F⊗⊕ω».Aₛ : mk (bind a) (tex noelab := s!"{TCₛ} \\, {a}")

nosubst
nonterminal ClassEnvironmentEntry, γc :=
  | "(" TCₛaAₛ:sepBy(γcₛ, ", ") " ⇒ " TC a " : " κ ")" " ↦ " m " : " σ " ⇝ " «F⊗⊕ω».A : mk (bind a) (tex noelab := s!"\\lottsym\{(} {TCₛaAₛ} \\, \\lottsym\{⇒} \\, {TC} \\, {a} \\, \\lottsym\{:} \\, {κ} \\lottsym\{)} \\, \\lottsym\{↦} \\, {m} \\, \\lottsym\{:} \\, {σ}")

nosubst
nonterminal ClassEnvironment, Γc (tex := "Γ_{C}") :=
  | "ε"         : empty (tex := "\\lottsym{\\epsilon}")
  | Γc ", " γc  : ext
  | "(" Γc ")"  : paren notex (expand := return Γc)
  | Γc ", " Γc' : append notex (expand := return .mkCApp `TabularTypeInterpreter.ClassEnvironment.append #[Γc, Γc'])

end TabularTypeInterpreter
