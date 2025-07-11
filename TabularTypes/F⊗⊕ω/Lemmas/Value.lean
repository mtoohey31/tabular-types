import Mathlib.Tactic
import TabularTypes.Data.Range
import TabularTypes.«F⊗⊕ω».Semantics.Term
import TabularTypes.«F⊗⊕ω».Lemmas.Type.Equivalence
import TabularTypes.«F⊗⊕ω».Lemmas.Term

namespace TabularTypes.«F⊗⊕ω»

theorem TypeEquivalence.common_reduct_of (eq: [[Δ ⊢ A ≡ B]]) (wf: [[ ⊢ Δ ]]) (AkiStar: [[ Δ ⊢ A : * ]]) : ∃C, [[Δ ⊢ A ->* C]] ∧ [[Δ ⊢ B ->* C]] :=
  EqSmallStep.of_Equivalence eq (K := [[ * ]]) AkiStar wf |>.common_reduct
namespace Value

private
theorem TypeEq_forall_of_scheme (Ety: [[Δ ⊢ Λ a : K. E: T]]) : ∃ T', [[Δ ⊢ T ≡ ∀ a : K. T']] := by
  generalize SchemeEeq : [[Λ a : K. E]] = SchemeE at Ety
  induction Ety <;> simp_all
  . case typeLam => aesop (add unsafe TypeEquivalence)
  . case equiv Δ E' A B E'tyA eqAB ih =>
    have ⟨T, eqAT⟩ := ih
    exact ⟨T, eqAB.symm.trans eqAT⟩

private
theorem TypeEq_arr_of_lam (Ety: [[Δ ⊢ λ x : A. E: T]]) : ∃ T', [[Δ ⊢ T ≡ A → T']] := by
  generalize LamEeq : [[λ x : A. E]] = LamE at Ety
  induction Ety <;> simp_all
  . case lam => aesop (add unsafe TypeEquivalence)
  . case equiv Δ E' A B E'tyA eqAB ih =>
    have ⟨T, eqAT⟩ := ih
    exact ⟨T, eqAB.symm.trans eqAT⟩

private
theorem TypeEq_prod_of_prodIntro (Ety: Typing Δ (Term.prodIntro E) T) : ∃ T', [[Δ ⊢ T ≡ ⊗T']] := by
  generalize ProdEeq : Term.prodIntro E = ProdE at Ety
  induction Ety <;> simp_all
  . case prodIntro => aesop (add unsafe TypeEquivalence)
  . case equiv Δ E' A B E'tyA eqAB ih =>
    have ⟨T, eqAT⟩ := ih
    exact ⟨T, eqAB.symm.trans eqAT⟩

private
theorem TypeEq_sum_of_sumIntro (Ety: Typing Δ (Term.sumIntro n E) T) : ∃ T', [[Δ ⊢ T ≡ ⊕T']] := by
  generalize SumEeq : Term.sumIntro n E = SumE at Ety
  induction Ety <;> simp_all
  . case sumIntro => aesop (add unsafe TypeEquivalence)
  . case equiv Δ E' A B E'tyA eqAB ih =>
    have ⟨T, eqAT⟩ := ih
    exact ⟨T, eqAB.symm.trans eqAT⟩

theorem canonical_form_of_arr (VtyAarrB : [[ε ⊢ V : A → B]])
  : ∃ A' E, V.1 = [[λ x : A'. E]] := by
  obtain ⟨E, isV⟩ := V
  cases isV <;> simp_all
  .case typeLam K E =>
    have ⟨T, Eeq⟩ := TypeEq_forall_of_scheme VtyAarrB
    have ⟨U, mredArr, mredForall⟩ := Eeq.common_reduct_of .empty VtyAarrB.Kinding_of
    have := mredForall.preserve_shape_forall; rcases this
    have := mredArr.preserve_shape_arr; rcases this
    simp_all
  .case prodIntro E isV =>
    have ⟨T, Eeq⟩ := TypeEq_prod_of_prodIntro VtyAarrB
    have ⟨U, mredArr, mredProd⟩ := Eeq.common_reduct_of .empty VtyAarrB.Kinding_of
    have := mredProd.preserve_shape_prod; rcases this
    have := mredArr.preserve_shape_arr; rcases this
    simp_all
  .case sumIntro n E isV =>
    have ⟨T, Eeq⟩ := TypeEq_sum_of_sumIntro VtyAarrB
    have ⟨U, mredArr, mredSum⟩ := Eeq.common_reduct_of .empty VtyAarrB.Kinding_of
    have := mredSum.preserve_shape_sum; rcases this
    have := mredArr.preserve_shape_arr; rcases this
    simp_all

theorem canonical_form_of_forall (Vty : [[ε ⊢ V : ∀ a? : K. A]])
  : ∃ K E, V.1 = [[Λ a? : K. E]] := by
  obtain ⟨E, isV⟩ := V
  cases isV <;> simp_all
  . case lam T E =>
    have ⟨T', Eeq⟩ := TypeEq_arr_of_lam Vty
    have ⟨U, mredForall, mredArr⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredArr.preserve_shape_arr; rcases this
    have := mredForall.preserve_shape_forall; rcases this
    simp_all
  . case prodIntro E isV =>
    have ⟨T, Eeq⟩ := TypeEq_prod_of_prodIntro Vty
    have ⟨U, mredForall, mredProd⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredProd.preserve_shape_prod; rcases this
    have := mredForall.preserve_shape_forall; rcases this
    simp_all
  . case sumIntro n E isV =>
    have ⟨T, Eeq⟩ := TypeEq_sum_of_sumIntro Vty
    have ⟨U, mredForall, mredSum⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredSum.preserve_shape_sum; rcases this
    have := mredForall.preserve_shape_forall; rcases this
    simp_all

local instance : Inhabited Term where
  default := .prodIntro []
in
theorem canonical_form_of_prod (Vty : [[ε ⊢ V : ⊗ {</ A@i // i in [:n] />}]])
  : ∃ V' : Nat → Value, V.1 = [[(</ V'@i // i in [:n] />)]] := by
  obtain ⟨E, isV⟩ := V
  cases isV <;> simp_all
  . case lam T E =>
    have ⟨T', Eeq⟩ := TypeEq_arr_of_lam Vty
    have ⟨U, mredProd, mredArr⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredArr.preserve_shape_arr; rcases this
    have := mredProd.preserve_shape_prod; rcases this
    simp_all
  . case typeLam K E =>
    have ⟨T, Eeq⟩ := TypeEq_forall_of_scheme Vty
    have ⟨U, mredProd, mredForall⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredForall.preserve_shape_forall; rcases this
    have := mredProd.preserve_shape_prod; rcases this
    simp_all
  . case prodIntro E isV =>
    rw [← Std.Range.map_get!_eq (as := E)] at Vty
    have ⟨eq_len, _⟩ := Vty.inv_prod; subst n
    refine ⟨λ i => ⟨E.get! i, ?_⟩, ?_⟩
    . simp [default, getElem?, decidableGetElem?]
      split
      . case isTrue h => simp_all
      . case isFalse contra => exact .prodIntro (λ E _ => nomatch E)
    . simp_all only
      eta_reduce
      rw [Std.Range.map_get!_eq (as := E)]
  . case sumIntro n E isV =>
    have ⟨T, Eeq⟩ := TypeEq_sum_of_sumIntro Vty
    have ⟨U, mredProd, mredSum⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredSum.preserve_shape_sum; rcases this
    have := mredProd.preserve_shape_prod; rcases this
    simp_all

theorem canonical_form_of_sum (Vty : [[ε ⊢ V : ⊕ {</ A@i // i in [:n'] />}]])
  : ∃ n ∈ [0:n'], ∃ V', V.1 = [[ι n V']] := by
  obtain ⟨E, isV⟩ := V
  cases isV <;> simp_all
  . case lam T E =>
    have ⟨T', Eeq⟩ := TypeEq_arr_of_lam Vty
    have ⟨U, mredSum, mredArr⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredArr.preserve_shape_arr; rcases this
    have := mredSum.preserve_shape_sum; rcases this
    simp_all
  . case typeLam K E =>
    have ⟨T, Eeq⟩ := TypeEq_forall_of_scheme Vty
    have ⟨U, mredSum, mredForall⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredForall.preserve_shape_forall; rcases this
    have := mredSum.preserve_shape_sum; rcases this
    simp_all
  . case prodIntro E isV =>
    have ⟨T, Eeq⟩ := TypeEq_prod_of_prodIntro Vty
    have ⟨U, mredSum, mredProd⟩ := Eeq.common_reduct_of .empty Vty.Kinding_of
    have := mredProd.preserve_shape_prod; rcases this
    have := mredSum.preserve_shape_sum; rcases this
    simp_all
  . case sumIntro n E isV =>
    have ⟨nin, _⟩ := Vty.inv_sum
    exact ⟨nin, ⟨E, isV⟩, rfl⟩

end Value
