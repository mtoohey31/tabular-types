import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") TypeEnvironment, Γ :=
  | "ε"                                : empty
  | Γ ", " a " : " κ                   : typeExt (id a)
  | Γ ",, " aκ:sepBy(a " : " κ, ",, ") : multiTypeExt notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.multiTypeExt #[Γ, aκ])
  | Γ ", " x " : " σ                   : termExt (id x)
  | Γ ", " ψ " ⇝ " «F⊗⊕ω».x            : constrExt (id x)
  | Γ ", " Γ'                          : append notex (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.append #[Γ, Γ'])
  | Γ " [" τ " / " a "]"               : subst notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.TypeVar_subst #[Γ, a, τ])
  | "(" Γ ")"                          : paren notex (expand := return Γ)

end TabularTypeInterpreter
