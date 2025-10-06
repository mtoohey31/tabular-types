import TabularTypes.Syntax.Term

namespace TabularTypes

nosubst
nonterminal Program, pgm :=
  | "class " sepBy(TC' a, ", ") " ⇒ " TC a " : " κ " where " "{" m " : " σ "}" "; " pgm : cls (bind a)
  | "instance " sepBy(ψ, ", ") " ⇒ " TC τ " where " "{" m " = " M "}" "; " pgm          : inst
  | M                                                                                   : term

end TabularTypes
