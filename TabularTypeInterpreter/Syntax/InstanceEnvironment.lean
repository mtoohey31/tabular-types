import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") InstanceEnvironmentEntry, γᵢ :=
  | "(" "∀ " sepBy(a " : " κ, ", ") ". " sepBy(ψ, ", ") " ⇒ " TC τ ")" " ↦ " «F⊗⊕ω».E "; " sepBy(«F⊗⊕ω».Eₛ, ", ") : mk (bind a)

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") InstanceEnvironment, Γᵢ (tex := "Γ_{I}") :=
  | "ε"        : empty (tex := "\\epsilon")
  | Γᵢ ", " γᵢ : ext

end TabularTypeInterpreter
