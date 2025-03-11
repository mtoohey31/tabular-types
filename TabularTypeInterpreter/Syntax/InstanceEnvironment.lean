import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal InstanceEnvironmentEntry, γᵢ :=
  | "(" "∀ " sepBy(a " : " κ, ", ") ". " sepBy(ψ, ", ") " ⇒ " TC τ ")" " ↦ " «F⊗⊕ω».E "; " sepBy(«F⊗⊕ω».E, ", ") : mk (bind a)

nosubst
nonterminal InstanceEnvironment, Γᵢ :=
  | "ε"        : empty
  | Γᵢ ", " γᵢ : ext

end TabularTypeInterpreter
