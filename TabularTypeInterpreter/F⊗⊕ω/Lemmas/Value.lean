import Mathlib.Tactic
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Equivalence
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.ParallelReduction

namespace TabularTypeInterpreter.«F⊗⊕ω»

theorem TypeEquivalence.common_reduct_of (eq: [[Δ ⊢ A ≡ B]]) (wf: [[ ⊢ Δ ]]) (Alc: A.TypeVarLocallyClosed) : ∃C, [[Δ ⊢ A ≡>* C]] ∧ [[Δ ⊢ B ≡>* C]] :=
  have ered := eq.EqParallelReduction_of
  have Blc := ered.preserve_lc.1 Alc
  ered.common_reduct wf Alc Blc
namespace Value

-- TODO rename, and will be affected by equiv definition change
private
theorem ty_lam_ty_eq_forall (Ety: [[Δ ⊢ Λ a : K. E: T]]) : ∃ T', [[Δ ⊢ T ≡ ∀ a : K. T']] := by
  generalize LamEeq : [[Λ a : K. E]] = LamE at Ety
  induction Ety <;> (try (aesop; done))
  . case typeLam =>
    aesop (add unsafe TypeEquivalence)
  . case equiv =>
    aesop
    exists w
    exact (a_1.symm).trans h

private
theorem ty_prodIntro_ty_eq_prod (Ety: Typing Δ (Term.prodIntro E) T) : ∃ T', [[Δ ⊢ T ≡ ⊗T']] := sorry

private
theorem ty_sumIntro_ty_eq_sum (Ety: Typing Δ (Term.sumIntro n E) T) : ∃ T', [[Δ ⊢ T ≡ ⊕T']] := sorry

-- canonical form of abstractions
theorem eq_lam_of_ty_arr (VtyAarrB : [[ε ⊢ V : A → B]]) (Alc: A.TypeVarLocallyClosed) (Blc: B.TypeVarLocallyClosed)
  : ∃ A' E, V.1 = [[λ x : A'. E]] := by
  obtain ⟨E, isV⟩ := V ; simp
  cases isV <;> simp at *
  .case typeLam K E =>
    have ⟨T, Eeq⟩ := ty_lam_ty_eq_forall VtyAarrB
    have ⟨U, mredArr, mredForall⟩ := Eeq.common_reduct_of .empty (by constructor <;> simp_all)
    have := mredForall.inv_typeLam; rcases this
    have := mredArr.inv_arr; rcases this
    simp_all
  .case prodIntro E isV =>
    have ⟨T, Eeq⟩ := ty_prodIntro_ty_eq_prod VtyAarrB
    have ⟨U, mredArr, mredProd⟩ := Eeq.common_reduct_of .empty (by constructor <;> simp_all)
    have := mredProd.inv_prodIntro; rcases this
    have := mredArr.inv_arr; rcases this
    simp_all
  .case sumIntro n E isV =>
    have ⟨T, Eeq⟩ := ty_sumIntro_ty_eq_sum VtyAarrB
    have ⟨U, mredArr, mredSum⟩ := Eeq.common_reduct_of .empty (by constructor <;> simp_all)
    have := mredSum.inv_sumIntro; rcases this
    have := mredArr.inv_arr; rcases this
    simp_all

theorem eq_typeApp_of_ty_forall (Vty : [[ε ⊢ V : ∀ a : K. A]])
  : ∃ K E, V.1 = [[Λ a : K. E]] := sorry

theorem eq_prodIntro_of_ty_prod (Vty : [[ε ⊢ V : ⊗ {</ A@i // i in [:n] />}]])
  : ∃ V' : Nat → Value, V.1 = [[(</ V'@i // i in [:n] />)]] := sorry

theorem eq_sumIntro_of_ty_sum (Vty : [[ε ⊢ V : ⊕ {</ A@i // i in [:n'] />}]])
  : ∃ n ∈ [0:n'], ∃ V', V.1 = [[ι n V']] := sorry

end Value
