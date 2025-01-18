import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

nosubst
nonterminal TypeEnvironment, Γ :=
  | "ε"                     : empty
  | Γ ", " a " : " κ        : typeExt (id a)
  | Γ ", " x " : " σ        : termExt (id x)
  | Γ ", " ψ " ⇝ " «F⊗⊕ω».x : constrExt (id x)

end TabularTypeInterpreter
