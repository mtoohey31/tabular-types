import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal InstanceEnvironmentEntryTypeVars, γᵢas :=
  | sepBy(a " : " κ, ", ") : mk (bind a)

nosubst
nonterminal InstanceEnvironmentEntryConstrs, γᵢψs :=
  | sepBy(ψ " ⇝ " «F⊗⊕ω».x, ", ") : mk (bind x)

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") InstanceEnvironmentEntry, γᵢ :=
  | "(" "∀ " γᵢas ". " γᵢψs " ⇒ " TC τ ")" " ↦ " «F⊗⊕ω».E "; " sepBy(«F⊗⊕ω».Eₛ, ", ") : mk

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") InstanceEnvironment, Γᵢ (tex := "Γ_{I}") :=
  | "ε"        : empty (tex := "\\epsilon")
  | Γᵢ ", " γᵢ : ext

end TabularTypeInterpreter
