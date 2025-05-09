import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Semantics.ClassEnvironment.Basic
import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration
import TabularTypeInterpreter.Syntax.InstanceEnvironment

namespace TabularTypeInterpreter

judgement_syntax γᵢ " ∈ " Γᵢ : InstanceEnvironment.In

judgement InstanceEnvironment.In where

─────────── head
γᵢ ∈ Γᵢ, γᵢ

γᵢ ∈ Γᵢ
──────────── ext
γᵢ ∈ Γᵢ, γᵢ'

judgement_syntax Γc " ⊢ " Γᵢ : InstanceEnvironment.WellFormedness

judgement InstanceEnvironment.WellFormedness where

────── empty
Γc ⊢ ε

Γc ⊢ Γᵢ
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ₀) ↦ m : σ ⇝ A ∈ Γc
</ ∀ a : { a : Nat → TypeVarId // a.Injective' }, Γc; ε,, </ a@k : κ₁@k // k in [:o] notex /> ⊢ ψ@j^^^a#o : C ⇝ B@j^^^a#o // j in [:l] notex />
∀ a : { a : Nat → TypeVarId // a.Injective' }, Γc; ε,, </ a@k : κ₁@k // k in [:o] notex /> ⊢ τ^^^a#o : κ₀ ⇝ B'^^^a#o
</ ⊢ κ₁@k ⇝ K₁@k // k in [:o] notex />
∀ a : { a : Nat → «F⊗⊕ω».TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, ε,, </ a@k : K₁@k // k in [:o] notex />,,, </ x@j : B@j^^^a#o // j in [:l] notex /> ⊢ E^^^x#l^^^a#o : A^^(B'^^^a#o)/a
</ ∀ a : { a : Nat → «F⊗⊕ω».TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, ε,, </ a@k : K₁@k // k in [:o] notex />,,, </ x@j : B@j^^^a#o // j in [:l] notex /> ⊢ Eₛ@i^^^x#l^^^a#o : Aₛ@i^^(B'^^^a#o)/a // i in [:n] notex />
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ext {TC}
Γc ⊢ Γᵢ, (∀ </ a@k : κ₁@k // k in [:o] />. </ ψ@j ⇝ x@j // j in [:l] /> ⇒ TC τ) ↦ E; </ Eₛ@i // i in [:n] notex />

end TabularTypeInterpreter
