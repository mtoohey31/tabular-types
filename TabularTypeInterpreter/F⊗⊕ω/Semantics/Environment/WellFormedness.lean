import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax "⊢ " Δ : EnvironmentWellFormedness

judgement EnvironmentWellFormedness :=

─── empty
⊢ ε

⊢ Δ
a ∉ dom(Δ)
────────── typeVarExt
⊢ Δ, a : K

⊢ Δ
x ∉ dom(Δ)
Δ ⊢ A : *
────────── termVarExt
⊢ Δ, x : A

@[app_unexpander EnvironmentWellFormedness]
def EnvironmentWellFormedness.delabEnvWF: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    `([ $vdash $Δ ])
  | _ => throw ()

end TabularTypeInterpreter.«F⊗⊕ω»
