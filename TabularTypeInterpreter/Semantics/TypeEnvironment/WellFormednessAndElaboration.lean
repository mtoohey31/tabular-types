import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax Γc " ⊢ " Γ " ⇝ " Δ : TypeEnvironment.WellFormednessAndElaboration

judgement TypeEnvironment.WellFormednessAndElaboration where

────────── empty
Γc ⊢ ε ⇝ ε

Γc ⊢ Γ ⇝ Δ
a ∉ dom(Γ)
⊢ κ ⇝ K
──────────────────────── typeExt
Γc ⊢ Γ, a : κ ⇝ Δ, a : K

Γc ⊢ Γ ⇝ Δ
x ∉ dom'(Γ)
Γc; Γ ⊢ σ : * ⇝ A
──────────────────────── termExt
Γc ⊢ Γ, x : σ ⇝ Δ, x : A

Γc ⊢ Γ ⇝ Δ
x ∉ dom'(Γ)
Γc; Γ ⊢ ψ : C ⇝ A
──────────────────────── constrExt
Γc ⊢ Γ, ψ ⇝ x ⇝ Δ, x : A

end TabularTypeInterpreter
