import TabularTypes.Syntax.Type

namespace TabularTypes

metavar Method, m

nosubst
nonterminal ClassEnvironmentEntrySuper, γc' :=
  | TC' a " ⇝ " «F⊗⊕ω».A' : mk (bind a) (tex noelab := s!"{TC'} \\, {a}")

nosubst
nonterminal ClassEnvironmentEntry, γc :=
  | "(" TC'aA':sepBy(γc', ", ") " ⇒ " TC a " : " κ ")" " ↦ " m " : " σ " ⇝ " «F⊗⊕ω».A : mk (bind a) (tex noelab := s!"\\lottsym\{(} {TC'aA'} \\, \\lottsym\{⇒} \\, {TC} \\, {a} \\, \\lottsym\{:} \\, {κ} \\lottsym\{)} \\, \\lottsym\{↦} \\, {m} \\, \\lottsym\{:} \\, {σ}")

nosubst
nonterminal ClassEnvironment, Γc (tex := "Γ_{C}") :=
  | "ε"         : empty (tex := "\\lottsym{\\epsilon}")
  | Γc ", " γc  : ext
  | "(" Γc ")"  : paren notex (expand := return Γc)
  | Γc ", " Γc' : append notex (expand := return .mkCApp `TabularTypes.ClassEnvironment.append #[Γc, Γc'])

end TabularTypes
