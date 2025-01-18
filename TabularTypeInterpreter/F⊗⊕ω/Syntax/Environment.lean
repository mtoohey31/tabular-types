import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

private
def Environment.appendExpr : Lean.Expr :=
  .const `TabularTypeInterpreter.«F⊗⊕ω».Environment.append []

private
def Environment.TypeVar_substExpr : Lean.Expr :=
  .const `TabularTypeInterpreter.«F⊗⊕ω».Environment.TypeVar_subst []

nosubst
nonterminal Environment, Δ :=
  | "ε"                  : empty
  | Δ ", " a " : " K     : typeExt (id a)
  | Δ ", " x " : " A     : termExt (id x)
  | "(" Δ ")"            : paren (desugar := return Δ)
  | Δ ", " Δ'            : append (elab := return Lean.mkApp2 Environment.appendExpr Δ Δ')
  | Δ " [" A " / " a "]" : subst (id a) (elab := return Lean.mkApp3 Environment.TypeVar_substExpr Δ a A)

end TabularTypeInterpreter.«F⊗⊕ω»
