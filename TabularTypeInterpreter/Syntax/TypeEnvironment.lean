import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nonterminal TypeEnvironmentDoubleComma, «,,» :=
  | ",, " : mk (tex := "\\lottsym{,} \\,")

nonterminal TypeEnvironmentTripleComma, «,,,» :=
  | ",,, " : mk (tex := "\\lottsym{,} \\,")

nonterminal TypeEnvironmentConstrEntry, ψx :=
  | ψ " ⇝ " «F⊗⊕ω».x : mk (id x) (tex noelab := ψ)

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") TypeEnvironment, Γ :=
  | "ε"                               : empty (tex := "\\epsilon")
  | Γ ", " a " : " κ                  : typeExt (id a)
  | Γ «,,» aκ:sepBy(a " : " κ, ",, ") : multiTypeExt notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.multiTypeExt #[Γ, aκ])
  | Γ ", " x " : " σ                  : termExt (id x)
  | Γ ", " ψx                         : constrExt (id x)
  | Γ «,,,» ψx:sepBy(ψx, ",,, ")      : multiConstrExt notex (id x) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.multiConstrExt #[Γ, ψx])
  | Γ ", " Γ'                         : append notex (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.append #[Γ, Γ'])
  | Γ " [" τ " / " a "]"              : subst notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.TypeEnvironment.TypeVar_subst #[Γ, a, τ])
  | "(" Γ ")"                         : paren notex (expand := return Γ)

end TabularTypeInterpreter
