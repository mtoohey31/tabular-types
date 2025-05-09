import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nonterminal TypeEnvironmentDoubleComma, «,,» :=
  | ",, " : mk (tex := "\\lottsym{,} \\,")

nonterminal TypeEnvironmentTripleComma, «,,,» :=
  | ",,, " : mk (tex := "\\lottsym{,} \\,")

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") TypeEnvironment, Γ :=
  | "ε"                                       : empty (tex := "\\epsilon")
  | Γ ", " a " : " κ                          : typeExt (id a)
  | Γ «,,» aκ:sepBy(a " : " κ, ",, ")         : multiTypeExt notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.multiTypeExt #[Γ, aκ])
  | Γ ", " x " : " σ                          : termExt (id x)
  | Γ ", " ψ " ⇝ " «F⊗⊕ω».x                   : constrExt (id x)
  | Γ «,,,» ψx:sepBy(ψ " ⇝ " «F⊗⊕ω».x, ",, ") : multiConstrExt notex (id x) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.multiConstrExt #[Γ, ψx])
  | Γ ", " Γ'                                 : append notex (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.append #[Γ, Γ'])
  | Γ " [" τ " / " a "]"                      : subst notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.TypeVar_subst #[Γ, a, τ])
  | "(" Γ ")"                                 : paren notex (expand := return Γ)

end TabularTypeInterpreter
