import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.ClassEnvironment

namespace TabularTypeInterpreter

nonterminal Term, M, «N» :=
  | x                                   : var
  | m                                   : method nosubst
  | "λ " x ". " M                       : lam (bind x in M)
  | M «N»                               : app
  | "let " x " : " σ " = " M " in " «N» : «let» (bind x in «N»)
  | M " :' " σ                          : annot (tex := s!"{M} \\, \\lottsym\{:} \\, {σ}")
  | ℓ                                   : label nosubst
  | "{" M " ▹ " «N» "}"                 : prod
  | "[" M " ▹ " «N» "]"                 : sum
  | M "/" «N»                           : unlabel
  | "prj " M                            : prj
  | M " ++ " «N»                        : concat (tex := s!"{M} \\lottsym\{\\doubleplus} {«N»}")
  | "inj " M                            : inj
  | M " ▿ " «N»                         : elim
  | "ind " «λτ» ρ "; " M "; " «N»       : ind (tex := s!"\\lottkw\{ind} \\, {«λτ»} \\, {ρ} \\, {M} \\, {«N»}")
  | M "^^^" a "#" n                     : TypeVar_multi_open notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.Term.TypeVar_multi_open #[M, a, n]) (tex := M)
  | M "^^^" x "#" n                     : TermVar_multi_open notex (id x) (expand := return .mkCApp `TabularTypeInterpreter.Term.TermVar_multi_open #[M, x, n]) (tex := M)
  | "(" M ")"                           : paren notex (expand := return M)

end TabularTypeInterpreter
