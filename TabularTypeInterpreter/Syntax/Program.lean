import TabularTypeInterpreter.Syntax.Term

namespace TabularTypeInterpreter

nosubst
nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") Program, pgm :=
  | "class " sepBy(TCₛ a, ", ") " ⇒ " TC a " : " κ " where " "{" m " : " σ "}" "; " pgm : cls (bind a)
  | "instance " sepBy(ψ, ", ") " ⇒ " TC τ " where " "{" m " = " M "}" "; " pgm          : inst
  | M                                                                                   : term

end TabularTypeInterpreter
