import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal EnvironmentDoubleComma, «,,» :=
  | ",, " : mk (tex := "\\lottsym{,} \\,")

nonterminal EnvironmentTripleComma, «,,,» :=
  | ",,, " : mk (tex := "\\lottsym{,} \\,")

nosubst
nonterminal (tex pre := "\\targetpre", post := "\\targetpost") Environment, Δ :=
  | "ε"                                      : empty (tex := "\\epsilon")
  | Δ ", " a " : " K                         : typeExt (id a)
  | Δ «,,» aK:sepBy(a " : " K, ",, ")        : multiTypeExt notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.multiTypeExt #[Δ, aK])
  | Δ ", " x " : " A                         : termExt (id x)
  | Δ «,,,» xA:sepBy(x " : " A, ",,, ")      : multiTermExt notex (id x) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.multiTermExt #[Δ, xA])
  | "(" Δ ")"                                : paren notex (expand := return Δ)
  | Δ ", " Δ'                                : append notex (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.append #[Δ, Δ'])
  | Δ " [" A " / " a "]"                     : subst notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.TypeVar_subst #[Δ, a, A])
  | Δ " ! " Aa:sepBy("[" A " / " a "]", "!") : multi_subst notex (id a) (expand := return .mkCApp `TabularTypeInterpreter.«F⊗⊕ω».Environment.TypeVar_multi_subst #[Δ, Aa]) (tex := s!"{Δ} \\, {Aa}")

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
