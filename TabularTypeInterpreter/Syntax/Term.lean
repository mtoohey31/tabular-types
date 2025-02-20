import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.ClassEnvironment

namespace TabularTypeInterpreter

nonterminal Term, M, «N» :=
  | x                                   : var
  | m                                   : member nosubst
  | "λ " x ". " M                       : lam (bind x in M)
  | M «N»                               : app
  | "let " x " : " σ " = " M " in " «N» : «let» (bind x in «N»)
  | M " :' " σ                          : annot
  | ℓ                                   : label nosubst
  | "{" sepBy(M " ▹ " «N», ", ") "}"    : prod
  | "[" M " ▹ " «N» "]"                 : sum
  | M "/" «N»                           : unlabel
  | "prj " M                            : prj
  | M " ++ " «N»                        : concat
  | "inj " M                            : inj
  | M " ▿ " «N»                         : elim
  | "order " ρ M                        : order
  | "ind " «λτ» ρ "; " M "; " «N»       : ind
  | "splitₚ " «λτ» M                    : splitₚ
  | "splitₛ " «λτ» M "; " «N»           : splitₛ
  | "(" M ")"                           : paren (desugar := return M)

end TabularTypeInterpreter
