import Lott
import Lott.Tactic.Termination
import TabularTypeInterpreter.«F⊗⊕ω»

namespace TabularTypeInterpreter

nonterminal Kind, κ :=
  | "*"         : star
  | κ₀ " ↦ " κ₁ : arr
  | "L"         : label
  | "U"         : comm
  | "R" κ       : row
  | "C"         : constr

nonterminal Commutativity, u :=
  | "C" : comm
  | "N" : non

locally_nameless
metavar TypeVar, a

metavar Label, ℓ

metavar TypeClass, TC

metavar Member, m

mutual

nonterminal TypeLambda, «λτ» :=
  | "(" "λ " a " : " κ ". " τ ")" : mk (bind a in τ)

nonterminal Monotype, τ, ξ, μ, ρ, ψ, φ :=
  | a                                   : var
  | φ τ                                 : app
  | τ₀ " → " τ₁                         : arr
  | ℓ                                   : label
  | "⌊" ξ "⌋"                           : floor
  | u                                   : comm
  | "⟨" sepBy(ξ " ▹ " τ, ", ") "⟩"      : row
  | "Π" "(" μ ") " ρ                    : prod
  | "Σ" "(" μ ") " ρ                    : sum
  | "Lift " «λτ» ρ                      : lift
  | ρ₀ " ≲" "(" μ ") " ρ₁               : contain
  | ρ₀ " ⊙" "(" μ ") " ρ₁ " ~ " ρ₂      : concat
  | TC τ                                : typeClass
  | "All " «λτ» ρ                       : all
  | "Ind " ρ                            : ind
  | "Split " «λτ» ρ₀ " ⊙' " ρ₁ " ~ " ρ₂ : split
  | "(" τ ")"                           : paren (desugar := return τ)

end

nonterminal QualifiedType, γ :=
  | τ         : mono
  | ψ " ⇒ " γ : qual

nonterminal TypeScheme, σ :=
  | γ                     : qual
  | "∀ " a " : " κ ". " σ : quant (bind a)

locally_nameless
metavar TermVar, x

nosubst
nonterminal TypeEnvironment, Γ :=
  | "ε"                     : empty
  | Γ ", " a " : " κ        : typeExt (id a)
  | Γ ", " x " : " σ        : termExt (id x)
  | Γ ", " ψ " ⇝ " «F⊗⊕ω».x : constrExt (id x)

nosubst
nonterminal ClassEnvironmentEntry, γc :=
  | "(" sepBy(TCₛ a " ⇝ " «F⊗⊕ω».Aₛ, ", ") " ⇒ " TC a " : " κ ")" " ↦ " m " : " σ " ⇝ " «F⊗⊕ω».A : mk (bind a)

nosubst
nonterminal ClassEnvironment, Γc :=
  | "ε"        : empty
  | Γc ", " γc : ext

end TabularTypeInterpreter
