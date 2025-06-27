import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal (parent := «Type») TypeValue, W :=
  | a                      : var
  | "λ " a " : " K ". " W  : lam (bind a in W)
  | "∀ " a " : " K ". " W  : «forall» (bind a in W)
  | W₀ " → " W₁            : arr
  | "{" sepBy(W, ", ") "}" : list
  | "⊗ " W                 : prod
  | "⊕ " W                 : sum

end TabularTypeInterpreter.«F⊗⊕ω»
