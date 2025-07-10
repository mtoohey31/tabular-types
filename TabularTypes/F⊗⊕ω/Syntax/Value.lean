import TabularTypes.«F⊗⊕ω».Syntax.Term

namespace TabularTypes.«F⊗⊕ω»

nonterminal (parent := Term) (tex pre := "\\targetpre", post := "\\targetpost") Value, V :=
  | "λ " x " : " A ". " E  : lam (bind x in E)
  | "Λ " a " : " K ". " E  : typeLam (bind a in E)
  | "(" sepBy(V, ", ") ")" : prodIntro
  | "ι " n V               : sumIntro (tex := s!"\\lottsym\{ι}_\{{n}} {V}")

end TabularTypes.«F⊗⊕ω»
