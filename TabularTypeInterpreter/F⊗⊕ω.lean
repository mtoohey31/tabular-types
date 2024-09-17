import Lott

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal Kind, K :=
  | "*"         : star
  | K₁ " ↦ " K₂ : arr
  | "L " K      : list

metavar TypeVar, a

nonterminal Type', A, B :=
  | a                      : var
  | "λ " a " : " K ". " A  : lam
  | A B                    : app
  | "∀ " a " : " K ". " A  : forall'
  | A " → " B              : arr
  | "{" sepBy(A, ", ") "}" : list
  | A " ⟦" B "⟧"           : listApp
  | "⊕ " A                 : sum
  | "⊗ " A                 : prod
  | "(" A ")"              : paren (desugar := return A)

end TabularTypeInterpreter.«F⊗⊕ω»
