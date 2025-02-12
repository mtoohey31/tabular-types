import TabularTypeInterpreter.Semantics.Kind

namespace TabularTypeInterpreter.Kind

theorem Elaboration_total (κ : Kind) : ∃ K, [[⊢ κ ⇝ K]] := match κ with
  | .star => .intro _ .star
  | .arr κ₀ κ₁ =>
    let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
    let ⟨_, κ₁e⟩ := κ₁.Elaboration_total
    .intro _ <| .arr κ₀e κ₁e
  | .label => .intro _ .label
  | .comm => .intro _ .comm
  | .row κ =>
    let ⟨_, κe⟩ := κ.Elaboration_total
    .intro _ <| .row κe
  | .constr => .intro _ .constr

theorem Elaboration.deterministic (κe₀ : [[⊢ κ ⇝ K₀]]) (κe₁ : [[⊢ κ ⇝ K₁]]) : K₀ = K₁ :=
  match κ, κe₀, κe₁ with
  | .star, .star, .star => rfl
  | .arr _ _, .arr κ₀e κ₁e, .arr κ₀e' κ₁e' =>
    let .refl _ := κ₀e.deterministic κ₀e'
    let .refl _ := κ₁e.deterministic κ₁e'
    rfl
  | .label, .label, .label => rfl
  | .comm, .comm, .comm => rfl
  | .row _, .row κ'e, .row κ'e' => let .refl _ := κ'e.deterministic κ'e'; rfl
  | .constr, .constr, .constr => rfl

end TabularTypeInterpreter.Kind
