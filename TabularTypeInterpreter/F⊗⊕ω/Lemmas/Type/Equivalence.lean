import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.ParallelReduction

namespace TabularTypeInterpreter.«F⊗⊕ω»

def TypeEquivalence.symm (h: [[Δ ⊢ A ≡ B]]): [[Δ ⊢ B ≡ A]] := by
  induction h with
  | refl => exact .refl
  | lamAppL => exact .lamAppR
  | lamAppR => exact .lamAppL
  | listAppL => exact .listAppR
  | listAppR => exact .listAppL
  | listAppIdL => exact .listAppIdR
  | listAppIdR => exact .listAppIdL
  | lam I h ih => exact .lam I ih
  | app h₁ h₂ ih₁ ih₂ => exact .app ih₁ ih₂
  | scheme I h ih => exact .scheme I ih
  | arr h₁ h₂ ih₁ ih₂ => exact .arr ih₁ ih₂
  | list h ih => exact .list ih
  | listApp h₁ h₂ ih₁ ih₂ => exact .listApp ih₁ ih₂
  | prod h ih => exact .prod ih
  | sum h ih => exact .sum ih
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₂ ih₁

theorem ParallelReduction.TypeEquivalence_of (h: [[ Δ ⊢ A ≡> B ]]) : [[ Δ ⊢ A ≡ B ]] := by
  induction h with
  | refl => exact .refl
  | lamApp _ _ _ ih1 ih2 => exact .trans (.app (.lam _ ih1) ih2) .lamAppL
  | lamListApp _ _ _ _ ih1 ih2 =>
      exact .trans (.listApp (.lam _ ih1) (.list ih2))
                (.trans .listAppL (.list λx xin => .lamAppL))
  | lam _ ih => exact .lam _ ih
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | scheme _ ih => exact .scheme _ ih
  | arr _ _ ih1 ih2 => exact .arr ih1 ih2
  | list _ ih => exact .list ih
  | listApp _ _ ih1 ih2 => exact .listApp ih1 ih2
  | prod _ ih => exact .prod ih
  | sum _ ih => exact .sum ih

theorem EqParallelReduction.TypeEquivalence_of (h: [[ Δ ⊢ A <≡>* B ]]) : [[ Δ ⊢ A ≡ B ]] := by
  induction h with
  | refl => exact .refl
  | step h => exact h.TypeEquivalence_of
  | sym BA ih => exact ih.symm
  | trans AB BC ih1 ih2 => exact ih1.trans ih2

namespace TypeEquivalence

theorem EqParallelReduction_of (eq: [[Δ ⊢ A ≡ B]]) : [[Δ ⊢ A <≡>* B]] := sorry

theorem weakening (equiv: [[ Δ, Δ'' ⊢ A ≡ B ]]) (wfτ: [[ ⊢τ Δ, Δ', Δ'' ]]) : [[ Δ, Δ', Δ'' ⊢ A ≡ B ]] :=
  equiv.EqParallelReduction_of |>.weakening wfτ |>.TypeEquivalence_of

theorem subst' {A T T' : «Type»} (equiv : [[ Δ, a: K, Δ' ⊢ T ≡ T' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡ T'[A/a] ]] :=
  equiv.EqParallelReduction_of |>.subst_out' wf kindA |>.TypeEquivalence_of

-- TODO this is not dt so properties on typing apparently have nothing to do with terms in env
theorem TermVar_drop (equiv: [[ Δ, x: T, Δ'' ⊢ A ≡ B ]]): [[ Δ, Δ'' ⊢ A ≡ B ]] := sorry

end TypeEquivalence

end TabularTypeInterpreter.«F⊗⊕ω»
