import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal InstanceEnvironmentEntryTypeVars, γᵢas :=
  | sepBy(a " : " κ, ", ") : mk (bind a)

nosubst
nonterminal InstanceEnvironmentEntryConstr, γᵢψ :=
  | ψ " ⇝ " «F⊗⊕ω».x : mk (bind x) (tex noelab := ψ)

nosubst
nonterminal InstanceEnvironmentEntryConstrs, γᵢψs :=
  | sepBy(γᵢψ, ", ") : mk

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") InstanceEnvironmentEntry, γᵢ :=
  | "(" "∀ " γᵢas ". " γᵢψs " ⇒ " TC τ ")" " ⇝ " «F⊗⊕ω».E "; " sepBy(«F⊗⊕ω».Eₛ, ", ") : mk (tex noelab := s!"\\lottsym\{(} \\lottsym\{∀} \\, {γᵢas} \\lottsym\{.} \\, {γᵢψs} \\, \\lottsym\{⇒} \\, {TC} \\, {τ} \\lottsym\{)}")

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") InstanceEnvironment, Γᵢ (tex := "Γ_{I}") :=
  | "ε"        : empty (tex := "\\epsilon")
  | Γᵢ ", " γᵢ : ext

end TabularTypeInterpreter
