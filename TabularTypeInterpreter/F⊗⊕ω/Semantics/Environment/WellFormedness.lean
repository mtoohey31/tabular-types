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

end TabularTypeInterpreter.«F⊗⊕ω»
