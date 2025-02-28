import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal TypeEnvironment, Γ :=
  | "ε"                     : empty
  | Γ ", " a " : " κ        : typeExt (id a)
  | Γ ", " x " : " σ        : termExt (id x)
  | Γ ", " ψ " ⇝ " «F⊗⊕ω».x : constrExt (id x)
  | "(" Γ ")"               : paren (desugar := return Γ)
  | Γ ", " Γ'               : append (elab := return Lean.mkApp2 (.const `TabularTypeInterpreter.TypeEnvironment.append []) Γ Γ')
  | Γ " [" τ " / " a "]"    : subst (id a) (elab := return Lean.mkApp3 (.const `TabularTypeInterpreter.TypeEnvironment.TypeVar_subst []) Γ a τ)

end TabularTypeInterpreter
