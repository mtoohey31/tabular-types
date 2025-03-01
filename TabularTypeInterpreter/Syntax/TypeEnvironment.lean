import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal TypeEnvironment, Γ :=
  | "ε"                                : empty
  | Γ ", " a " : " κ                   : typeExt (id a)
  | Γ ",, " aκ:sepBy(a " : " κ, ",, ") : multiTypeExt (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.multiTypeExt #[Γ, aκ])
  | Γ ", " x " : " σ                   : termExt (id x)
  | Γ ", " ψ " ⇝ " «F⊗⊕ω».x            : constrExt (id x)
  | Γ ", " Γ'                          : append (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.append #[Γ, Γ'])
  | Γ " [" τ " / " a "]"               : subst (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.TypeVar_subst #[Γ, a, τ])
  | "(" Γ ")"                          : paren (expand := return Γ)

end TabularTypeInterpreter
