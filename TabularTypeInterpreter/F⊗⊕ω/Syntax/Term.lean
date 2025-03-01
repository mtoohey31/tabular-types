import Lott.Elab.Nat
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
  | "⦅" E "⦆"                        : paren (expand := return E)

namespace Term
attribute [app_unexpander TypeVar_open] Type.delabTVOpen
attribute [app_unexpander Type_open] Type.delabTOpen
attribute [app_unexpander TypeVar_subst] Type.delabTVSubst
attribute [app_unexpander TermVar_open] Type.delabTVOpen
attribute [app_unexpander Term_open] Type.delabTOpen
attribute [app_unexpander TermVar_subst] Type.delabTVSubst
end Term

end TabularTypeInterpreter.«F⊗⊕ω»
