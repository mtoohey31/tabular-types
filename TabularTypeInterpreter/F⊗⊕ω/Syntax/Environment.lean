import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

nosubst
nonterminal (tex pre := "\\targetpre", post := "\\targetpost") Environment, Δ :=
  | "ε"                  : empty (tex := "\\epsilon")
  | Δ ", " a " : " K     : typeExt (id a)
  | Δ ", " x " : " A     : termExt (id x)
  | "(" Δ ")"            : paren notex (expand := return Δ)
  | Δ ", " Δ'            : append notex (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.append #[Δ, Δ'])
  | Δ " [" A " / " a "]" : subst notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.TypeVar_subst #[Δ, a, A])

namespace Environment

termonly
@[app_unexpander empty]
def delabEempty : Lean.PrettyPrinter.Unexpander
  | `($(_)) =>
    let info := Lean.SourceInfo.none
    let eps := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "ε") }
    `( $eps )

termonly
@[app_unexpander typeExt, app_unexpander termExt]
def delabETypeExt : Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $a $K) =>
    let info := Lean.SourceInfo.none
    let comma := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ",") }
    let colon := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ":") }
    `( $Δ $comma $a $colon $K )
  | _ => throw ()

end Environment

end TabularTypeInterpreter.«F⊗⊕ω»
