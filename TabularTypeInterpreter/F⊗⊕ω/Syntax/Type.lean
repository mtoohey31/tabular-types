import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Kind

namespace TabularTypeInterpreter.«F⊗⊕ω»

locally_nameless
metavar TypeVar, a

nonterminal «Type», A, B :=
  | a                      : var
  | "λ " a " : " K ". " A  : lam (bind a in A)
  | A B                    : app
  | "∀ " a " : " K ". " A  : «forall» (bind a in A)
  | A " → " B              : arr
  | "{" sepBy(A, ", ") "}" : list
  | A " ⟦" B "⟧"           : listApp
  | "⊗ " A                 : prod
  | "⊕ " A                 : sum
  | "(" A ")"              : paren (desugar := return A)

end TabularTypeInterpreter.«F⊗⊕ω»
