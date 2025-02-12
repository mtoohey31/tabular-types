import Aesop
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type

namespace TabularTypeInterpreter.«F⊗⊕ω».Value

-- TODO rename
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

-- canonical form of abstractions
theorem eq_lam_of_ty_arr (VtyAarrB : [[ε ⊢ V : A → B]])
  : ∃ A' E, V.1 = [[λ x : A'. E]] := by
  obtain ⟨E, isV⟩ := V ; simp
  cases isV <;> simp at *
  .case typeLam K E =>
    have ⟨T, Eeq⟩ := ty_lam_ty_eq_forall VtyAarrB
    -- have ⟨U, mredArr, mredForall⟩ := equiv_common_reduct Eeq
    -- have ⟨A', E', Eeq', AarrBeq⟩ := mredForall.inv_lam
    -- have ⟨A'', E'', Eeq'', AarrBeq'⟩ := mredArr.inv_arr
    -- aesop
    sorry
  .case prodIntro => sorry
  .case sumIntro => sorry

theorem eq_typeApp_of_ty_forall (Vty : [[ε ⊢ V : ∀ a : K. A]])
  : ∃ K E, V.1 = [[Λ a : K. E]] := sorry

theorem eq_prodIntro_of_ty_prod (Vty : [[ε ⊢ V : ⊗ {</ A@i // i in [:n] />}]])
  : ∃ V' : Nat → Value, V.1 = [[(</ V'@i // i in [:n] />)]] := sorry

theorem eq_sumIntro_of_ty_sum (Vty : [[ε ⊢ V : ⊕ {</ A@i // i in [:n'] />}]])
  : ∃ n ∈ [0:n'], ∃ V', V.1 = [[ι n V']] := sorry

end TabularTypeInterpreter.«F⊗⊕ω».Value
