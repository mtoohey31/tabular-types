import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.Lemmas.TypeEnvironment
import TabularTypeInterpreter.Theorems.Kind
import TabularTypeInterpreter.Theorems.Type.KindingAndElaboration

namespace TabularTypeInterpreter.TypeScheme.KindingAndElaboration

open «F⊗⊕ω»

theorem Monotype_open_preservation
  (σke : KindingAndElaboration Γc [[(Γ, a : κ₀, Γ')]] (TypeVar_open σ a n) κ₁
    (Type.TypeVar_open A a n)) (ΓaΓ'we : [[Γc ⊢ Γ, a : κ₀, Γ' ⇝ Δ]]) (aninΓ' : [[a ∉ dom(Γ')]])
  (aninσ : a ∉ σ.freeTypeVars) (aninA : a ∉ A.freeTypeVars) (τke : [[Γc; Γ ⊢ τ : κ₀ ⇝ B]])
  : KindingAndElaboration Γc [[(Γ, (Γ' [τ / a]))]] (σ.Monotype_open τ n) κ₁ (A.Type_open B n) := by
  sorry

end TabularTypeInterpreter.TypeScheme.KindingAndElaboration
