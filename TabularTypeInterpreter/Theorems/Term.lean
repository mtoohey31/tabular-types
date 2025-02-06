import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Theorems.Type

namespace TabularTypeInterpreter

theorem Term.TypingAndElaboration.soundness (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]])
  (σke : [[Γc; Γ ⊢ σ : * ⇝ A]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : [[Δ ⊢ E : A]] := by
  induction Mte using rec
    (motive_2 := fun Γᵢ Γc Γ ψ E ψce => [[Γc; Γ ⊢ ψ : C ⇝ A]] → [[Γc ⊢ Γ ⇝ Δ]] → [[Δ ⊢ E : A]]) with
  | var xinΓ => exact .var Γwe.soundness sorry

end TabularTypeInterpreter
