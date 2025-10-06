import Lott.Tactic.Termination
import TabularTypes.«F⊗⊕ω».Syntax.Type
import TabularTypes.Syntax.Kind

namespace TabularTypes

nonterminal Commutativity, u :=
  | "C" : comm (tex := "\\mathfrak{c}")
  | "N" : non (tex := "\\mathfrak{n}")

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

nonterminal Monotype, τ, ϕ, ρ, ψ, ξ, μ :=
  | a                                                  : var
  | ϕ τ                                                : app
  | τ₀ " → " τ₁                                        : arr
  | ℓ                                                  : label nosubst
  | "⌊" ξ "⌋"                                          : floor
  | u                                                  : comm
  | "⟨" f:sepBy(ξ " ▹ " τ, ", ") optional(" : " κ) "⟩" : row (tex := s!"\\lottsym\{⟨} {f} \\lottsym\{⟩}")
  | Ξ "(" μ ") " ρ                                     : prodOrSum (tex := s!"\{{Ξ}}_\{{μ}} \\, {ρ}")
  | "Lift " «λτ» ρ                                     : lift
  | ρ₀ " ≲" "(" μ ") " ρ₁                              : contain (tex := s!"{ρ₀} \\, \\lottsym\{≲}_\{{μ}} \\, {ρ₁}")
  | ρ₀ " ⊙" "(" μ ") " ρ₁ " ~ " ρ₂                     : concat (tex := s!"{ρ₀} \\, \\lottsym\{⊙}_\{{μ}} \\, {ρ₁} \\, \\lottsym\{\\sim} \\, {ρ₂}")
  | TC τ                                               : typeClass
  | "All " «λτ» ρ                                      : all
  | "Ind " ρ                                           : ind
  | "Split " «λτ» ρ₀ " ⊙' " ρ₁ " ~ " ρ₂                : split (tex := s!"\\lottkw\{Split} \\, {«λτ»} \\, {ρ₀} \\, {ρ₁} \\, {ρ₂}")
  | τ "^^^" a "#" n                                    : TypeVar_multi_open notex (id a) (expand := return .mkCApp `TabularTypes.Monotype.TypeVar_multi_open #[τ, .mk <| Lean.mkNode ``coeFunNotation #[Lean.mkAtom "⇑", a], n]) (tex := τ)
  | τ₀ "^^^^" τ₁ "@@" i "#" n "/" a                    : Monotype_multi_open notex (expand := return .mkCApp `TabularTypes.Monotype.Monotype_multi_open #[τ₀, τ₁, n]) (tex := s!"{τ₀}\\lottsepbycomprehension\{\\left[\{{τ₁}}_\{{i}}/\{{a}}_\{{i}}\\right]}")
  | "(" τ ")"                                          : paren notex (expand := return τ)
  | "⦅" τ "⦆"                                          : invisible_paren notex (expand := return τ) (tex := τ)

end

nonterminal QualifiedType, γ :=
  | ψ " ⇒ " γ : qual
  | τ         : mono

nonterminal TypeScheme, σ :=
  | "∀ " a " : " κ ". " σ : quant (bind a)
  | γ                     : qual

end TabularTypes
