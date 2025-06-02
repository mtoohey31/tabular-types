import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

locally_nameless
metavar (tex pre := "\\targetpre", post := "\\targetpost") TermVar, x

nonterminal (tex pre := "\\targetpre", post := "\\targetpost") Term, E, F :=
  | x                                 : var
  | "λ " x " : " A ". " E             : lam (bind x in E)
  | E F                               : app
  | "! " Es:sepBy(E, ", ") F          : multiApp notex (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Term.multi_app #[Es, F]) (tex := s!"{Es} \\, {F}")
  | "Λ " a " : " K ". " E             : typeLam (bind a in E)
  | E " [" A "]"                      : typeApp
  | "(" sepBy(E, ", ") ")"            : prodIntro
  | "π " n E                          : prodElim (tex := s!"\\lottsym\{π}_\{{n}} \\, {E}")
  | "ι " n E                          : sumIntro (tex := s!"\\lottsym\{ι}_\{{n}} \\, {E}")
  | "case " E " {" sepBy(F, ", ") "}" : sumElim
  | E "^^^" a "#" n                   : TypeVar_multi_open notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Term.TypeVar_multi_open #[E, a, n]) (tex := E)
  | E "^^^" x "#" n                   : TermVar_multi_open notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Term.TermVar_multi_open #[E, x, n]) (tex := E)
  | E "^^^^" A "@@" i "#" n "/" a     : Type_multi_open notex (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Term.Type_multi_open #[E, A, n]) (tex := s!"{E}\\lottsepbycomprehension\{\\left[\{{A}}_\{{i}}/\{{a}}_\{{i}}\\right]}")
  | E "^^^^" F "@@" i "#" n "/" x     : Term_multi_open notex (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Term.Term_multi_open #[E, F, n]) (tex := s!"{E}\\lottsepbycomprehension\{\\left[\{{F}}_\{{i}}/\{{x}}_\{{i}}\\right]}")
  | "⦅" E "⦆"                         : paren notex (expand := return E) (tex := s!"\\lottsym\{(} {E} \\lottsym\{)}")

namespace Term

termonly
attribute [app_unexpander TypeVar_open] Type.delabTVOpen

termonly
attribute [app_unexpander TypeVar_close] Type.delabTVClose

termonly
attribute [app_unexpander Type_open] Type.delabTOpen

termonly
attribute [app_unexpander TypeVar_subst] Type.delabTVSubst

termonly
attribute [app_unexpander TermVar_open] Type.delabTVOpen

termonly
attribute [app_unexpander TermVar_close] Type.delabTVClose

termonly
attribute [app_unexpander Term_open] Type.delabTOpen

termonly
attribute [app_unexpander TermVar_subst] Type.delabTVSubst

end Term

end TabularTypeInterpreter.«F⊗⊕ω»
