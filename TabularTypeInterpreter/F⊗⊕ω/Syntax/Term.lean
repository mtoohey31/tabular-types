import Lott.DSL.Elab.Nat
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

locally_nameless
metavar TermVar, x

nonterminal Term, E, F :=
  | x                                : var
  | "λ " x " : " A ". " E            : lam (bind x in E)
  | E F                              : app
  | "Λ " a " : " K ". " E            : typeLam (bind a in E)
  | E " [" A "]"                     : typeApp
  | "(" sepBy(E, ", ") ")"           : prodIntro
  | "π " n E                         : prodElim
  | "ι " n E                         : sumIntro
  | "case " E "{" sepBy(F, ", ") "}" : sumElim
  | "⦅" E "⦆"                        : paren (desugar := return E)

end TabularTypeInterpreter.«F⊗⊕ω»
