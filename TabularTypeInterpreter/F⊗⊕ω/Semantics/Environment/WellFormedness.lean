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
def EnvironmentWellFormedness.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    `([ $vdash $Δ ])
  | _ => throw ()

judgement_syntax "⊢τ" Δ : EnvironmentTypeWellFormedness

judgement EnvironmentTypeWellFormedness :=

─── empty
⊢τ ε

⊢τ Δ
a ∉ dom(Δ)
────────── typeVarExt
⊢τ Δ, a : K

⊢τ Δ
────────── termVarExt
⊢τ Δ, x : A

@[app_unexpander EnvironmentTypeWellFormedness]
def EnvironmentTypeWellFormedness.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢τ") }
    `([ $vdash $Δ ])
  | _ => throw ()

end TabularTypeInterpreter.«F⊗⊕ω»
