import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.ClassEnvironment

namespace TabularTypeInterpreter

nonterminal (tex pre := "\\sourcepre", post := "\\sourcepost") Term, M, «N» :=
  | x                                   : var
  | m                                   : member nosubst
  | "λ " x ". " M                       : lam (bind x in M)
  | M «N»                               : app
  | "let " x " : " σ " = " M " in " «N» : «let» (bind x in «N»)
  | M " :' " σ                          : annot (tex := s!"{M} \\, \\lottsym\{:} \\, {σ}")
  | ℓ                                   : label nosubst
  | "{" sepBy(M " ▹ " «N», ", ") "}"    : prod
  | "[" M " ▹ " «N» "]"                 : sum
  | M "/" «N»                           : unlabel
  | "prj " M                            : prj
  | M " ++ " «N»                        : concat (tex := s!"{M} \\doubleplus {«N»}")
  | "inj " M                            : inj
  | M " ▿ " «N»                         : elim
  | "order " ρ M                        : order
  | "ind " «λτ» ρ "; " M "; " «N»       : ind (tex := s!"\\lottkw\{ind} \\, {«λτ»} {ρ} \\, {M} \\, {«N»}")
  | "splitₚ " «λτ» M                    : splitₚ
  | "splitₛ " «λτ» M "; " «N»           : splitₛ (tex := s!"\\lottkw\{splitₛ} \\, {«λτ»} {M} \\, {«N»}")
  | "(" M ")"                           : paren notex (expand := return M)

end TabularTypeInterpreter
