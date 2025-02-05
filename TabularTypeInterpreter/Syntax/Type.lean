import Lott.Tactic.Termination
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.Syntax.Kind

namespace TabularTypeInterpreter

nonterminal Commutativity, u :=
  | "C" : comm
  | "N" : non

locally_nameless
metavar TypeVar, a

metavar Label, ℓ

nonterminal ProdOrSum, Ξ :=
  | "Π" : prod
  | "Σ" : sum

metavar TypeClass, TC

variable (TC : Unit) -- To silence warning about TC deprecation.

mutual

nonterminal TypeLambda, «λτ» :=
  | "(" "λ " a " : " κ ". " τ ")" : mk (bind a in τ)

nonterminal Monotype, τ, ξ, μ, ρ, ψ, φ :=
  | a                                                : var
  | φ τ                                              : app
  | τ₀ " → " τ₁                                      : arr
  | ℓ                                                : label
  | "⌊" ξ "⌋"                                        : floor
  | u                                                : comm
  | "⟨" sepBy(ξ " ▹ " τ, ", ") optional(" : " κ) "⟩" : row
  | Ξ "(" μ ") " ρ                                   : prodOrSum
  | "Lift " «λτ» ρ                                   : lift
  | ρ₀ " ≲" "(" μ ") " ρ₁                            : contain
  | ρ₀ " ⊙" "(" μ ") " ρ₁ " ~ " ρ₂                   : concat
  | TC τ                                             : typeClass
  | "All " «λτ» ρ                                    : all
  | "Ind " ρ                                         : ind
  | "Split " «λτ» ρ₀ " ⊙' " ρ₁ " ~ " ρ₂              : split
  | "(" τ ")"                                        : paren (desugar := return τ)

end

nonterminal QualifiedType, γ :=
  | τ         : mono
  | ψ " ⇒ " γ : qual

nonterminal TypeScheme, σ :=
  | γ                     : qual
  | "∀ " a " : " κ ". " σ : quant (bind a)

end TabularTypeInterpreter
