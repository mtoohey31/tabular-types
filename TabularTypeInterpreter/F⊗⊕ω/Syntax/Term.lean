import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

locally_nameless
metavar (tex pre := "\\targetpre", post := "\\targetpost") TermVar, x

nonterminal (tex pre := "\\targetpre", post := "\\targetpost") Term, E, F :=
  | x                                 : var
  | "λ " x " : " A ". " E             : lam (bind x in E)
  | E F                               : app
  | "Λ " a " : " K ". " E             : typeLam (bind a in E)
  | E " [" A "]"                      : typeApp
  | "(" sepBy(E, ", ") ")"            : prodIntro
  | "π " n E                          : prodElim (tex := s!"\\lottsym\{π}_\{{n}} \\, {E}")
  | "ι " n E                          : sumIntro (tex := s!"\\lottsym\{ι}_\{{n}} \\, {E}")
  | "case " E " {" sepBy(F, ", ") "}" : sumElim
  | "⦅" E "⦆"                         : paren notex (expand := return E) (tex := s!"\\lottsym\{(} {E} \\lottsym\{)}")

namespace Term

termonly
attribute [app_unexpander TypeVar_open] Type.delabTVOpen

termonly
attribute [app_unexpander Type_open] Type.delabTOpen

termonly
attribute [app_unexpander TypeVar_subst] Type.delabTVSubst

termonly
attribute [app_unexpander TermVar_open] Type.delabTVOpen

termonly
attribute [app_unexpander Term_open] Type.delabTOpen

termonly
attribute [app_unexpander TermVar_subst] Type.delabTVSubst

end Term

end TabularTypeInterpreter.«F⊗⊕ω»
