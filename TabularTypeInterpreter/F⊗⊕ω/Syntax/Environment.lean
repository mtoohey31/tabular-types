import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

private
def Environment.appendExpr : Lean.Expr :=
  .const `TabularTypeInterpreter.«F⊗⊕ω».Environment.append []

private
def Environment.TypeVar_substExpr : Lean.Expr :=
  .const `TabularTypeInterpreter.«F⊗⊕ω».Environment.TypeVar_subst []

nosubst
nonterminal Environment, Δ :=
  | "ε"                  : empty
  | Δ ", " a " : " K     : typeExt (id a)
  | Δ ", " x " : " A     : termExt (id x)
  | "(" Δ ")"            : paren (desugar := return Δ)
  | Δ ", " Δ'            : append (elab := return Lean.mkApp2 Environment.appendExpr Δ Δ')
  | Δ " [" A " / " a "]" : subst (id a) (elab := return Lean.mkApp3 Environment.TypeVar_substExpr Δ a A)

namespace Environment
@[app_unexpander empty]
def delabEempty : Lean.PrettyPrinter.Unexpander
  | `($(_)) =>
    let info := Lean.SourceInfo.none
    let eps := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "ε") }
    `( $eps )

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
