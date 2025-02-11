import TabularTypeInterpreter.Lemmas.Type.Basic
import TabularTypeInterpreter.Lemmas.Type.MonotypeOpenPreservation
import TabularTypeInterpreter.Semantics.Type
import TabularTypeInterpreter.Theorems.Type.KindingAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»

theorem Monotype.RowEquivalenceAndElaboration.to_Kinding (ρee : [[Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : ∃ κ A B, [[Γc; Γ ⊢ ρ₀ : R κ ⇝ A]] ∧ [[Γc; Γ ⊢ ρ₁ : R κ ⇝ B]] := by
  match ρee with
  | refl ρek .. => exact ⟨_, _, _, ρek, ρek⟩
  | comm perm _ _ ξτke κe (p := p) =>
    let ⟨⟨_, ξke⟩, uni, ⟨_, _, eq, eqκ, h, _, τke⟩⟩ := ξτke.row_inversion
    cases eqκ
    rw [← Std.Range.map_get!_eq (as := p), List.map_map]
    let length_eq := perm.length_eq
    rw [Std.Range.length_toList] at length_eq
    cases length_eq
    let ξke' := fun i (imem : i ∈ [:p.length]) =>
      ξke (p.get! i) <| Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.right
    let τke' := fun i (imem : i ∈ [:p.length]) =>
      τke (p.get! i) <| Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.right
    exact ⟨_, _, _, ξτke, .row ξke' (uni.Perm_preservation perm (fun _ => rfl)) τke' h⟩
  | trans ρ₀ke κe ρ₀₁ee ρ₁₂ee =>
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    let ⟨_, _, _, ρ₁ke', ρ₂ke⟩ := ρ₁₂ee.to_Kinding Γwe
    cases ρ₁ke.deterministic ρ₁ke' |>.left
    exact ⟨_, _, _, ρ₀ke, ρ₂ke⟩
  | liftL _ liftke@(.lift I τ₁ke κ₀e ξτ₀ke) _ (τ₁ := τ₁) =>
    let ⟨⟨_, ξke⟩, uni, ⟨_, _, eq, κeq, h, _, τ₀ke⟩⟩ := ξτ₀ke.row_inversion
    cases eq
    cases κeq
    exact ⟨
      _,
      _,
      _,
      liftke,
      .row ξke uni (fun i imem => by
        rename «Type» => A
        let ⟨a, anin⟩ := τ₁.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom ++ I |>.exists_fresh
        let ⟨aninτ₁AΓ, aninI⟩ := List.not_mem_append'.mp anin
        let ⟨aninτ₁A, aninΓ⟩ := List.not_mem_append'.mp aninτ₁AΓ
        let ⟨aninτ₁, aninA⟩ := List.not_mem_append'.mp aninτ₁A
        have := τ₁ke a aninI
        simp only
        rw [← QualifiedType.Monotype_open, ← TypeScheme.Monotype_open]
        rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at this
        exact this.Monotype_open_preservation (Γwe.typeExt aninΓ κ₀e) (nomatch ·) aninτ₁ aninA
          (τ₀ke i imem) (Γ' := .empty)) h
    ⟩
  | liftR _ liftke@(.lift I τ₁ke κ₀e ξτ₀ke) _ (τ₁ := τ₁) =>
    let ⟨⟨_, ξke⟩, uni, ⟨_, _, eq, κeq, h, _, τ₀ke⟩⟩ := ξτ₀ke.row_inversion
    cases eq
    cases κeq
    exact ⟨
      _,
      _,
      _,
      .row ξke uni (fun i imem => by
        rename «Type» => A
        let ⟨a, anin⟩ := τ₁.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom ++ I |>.exists_fresh
        let ⟨aninτ₁AΓ, aninI⟩ := List.not_mem_append'.mp anin
        let ⟨aninτ₁A, aninΓ⟩ := List.not_mem_append'.mp aninτ₁AΓ
        let ⟨aninτ₁, aninA⟩ := List.not_mem_append'.mp aninτ₁A
        have := τ₁ke a aninI
        simp only
        rw [← QualifiedType.Monotype_open, ← TypeScheme.Monotype_open]
        rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at this
        exact this.Monotype_open_preservation (Γwe.typeExt aninΓ κ₀e) (nomatch ·) aninτ₁ aninA
          (τ₀ke i imem) (Γ' := .empty)) h,
      liftke
    ⟩

end TabularTypeInterpreter
