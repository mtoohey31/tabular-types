import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Theorems.Term

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std
open Term.TypingAndElaboration
open TypeScheme
open Monotype

instance : Inhabited Monotype where
  default := .row [] none
in
theorem ana_emulation (ρke : [[Γc; Γ ⊢ ρ : R κ ⇝ A₀]]) (ϕke : [[Γc; Γ ⊢ ϕ : κ ↦ * ⇝ A₁]])
  (μ₀ke : [[Γc; Γ ⊢ μ₀ : U ⇝ B₀]]) (μ₁ke : [[Γc; Γ ⊢ μ₁ : U ⇝ B₁]]) (τke : [[Γc; Γ ⊢ τ : * ⇝ A₂]])
  (Mte : [[Γᵢ; Γc; Γ ⊢ M : ∀ aₗ : L. ∀ aₜ : κ. ∀ aₚ : R κ. ∀ aᵢ : R κ. ∀ aₙ : R κ. aₚ$2 ⊙(μ₀) ⟨aₗ$4 ▹ aₜ$3⟩ ~ aᵢ$1 ⇒ aᵢ$1 ⊙(μ₀) aₙ$0 ~ ρ ⇒ ⌊aₗ$4⌋ → ϕ aₜ$3 → τ ⇝ E]])
  (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ F, [[Γᵢ; Γc; Γ ⊢ ind (λ a : R κ. (Σ(μ₁) (Lift (λ a' : κ. ϕ a'$0) a$0)) → τ) ρ; (λ xₗ. λ xₐ. xₐ$0 ▿ (M xₗ$1)); (λ x. x$0) : (Σ(μ₁) (Lift (λ a : κ. ϕ a$0) ρ)) → τ ⇝ F]] := by
  let ⟨K, κe⟩ := κ.Elaboration_total
  apply Exists.intro _
  let .qual (.mono μ₁lc) := μ₁ke.TypeVarLocallyClosed_of
  let .qual (.mono ϕlc) := ϕke.TypeVarLocallyClosed_of
  let .qual (.mono τlc) := τke.TypeVarLocallyClosed_of
  let A₁lc := ϕke.soundness Γcw Γwe (.arr κe .star) |>.TypeVarLocallyClosed_of
  have : Monotype.arr (.prodOrSum .sum μ₁ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) ρ)) τ =
    .Monotype_open (.arr (.prodOrSum .sum μ₁ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) (.var (.bound 0)))) τ) ρ := by
    simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
    exact ⟨
      ⟨μ₁lc.Monotype_open_id.symm, ϕlc.weakening (n := 1).Monotype_open_id.symm⟩,
      τlc.Monotype_open_id.symm
    ⟩
  rw [this]
  apply «ind» [] [] ρke _ κe
  · intro aₗ aₗnin
    intro aₜ aₜnin
    intro aₚ aₚnin
    intro aᵢ aᵢnin
    intro aₙ aₙnin
    -- apply qualI []
    -- apply lam []
    simp [TypeScheme.TypeVar_open, Monotype.TypeVar_open]
  · simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
    rw [μ₁lc.Monotype_open_id, ϕlc.weakening (n := 1).Monotype_open_id, τlc.Monotype_open_id]
    let sumke : [[Γc; Γ ⊢ Σ(μ₁) (Lift (λ a : κ. ϕ a$0) ⟨ : κ ⟩) : * ⇝ ⊕ (λ a : K. A₁ a$0) ⟦{ }⟧]] := by
      apply KindingAndElaboration.sum μ₁ke
      apply KindingAndElaboration.lift Γ.typeVarDom
      · intro a anin
        let Γawe := Γwe.typeExt anin κe
        rw [Monotype.TypeVar_open, Monotype.TypeVar_open, if_pos rfl, ϕlc.TypeVar_open_id]
        let ϕappa := ϕke.weakening Γawe (Γ' := .typeExt .empty ..) (Γ'' := .empty).app (.var .head)
        simp [Type.TypeVar_open]
        rw [A₁lc.TypeVar_open_id]
        exact ϕappa
      · exact κe
      · exact .empty_row
    apply lam Γ.termVarDom
    · intro x xnin
      rw [Term.TermVar_open, if_pos rfl]
      let Γxwe := Γwe.termExt xnin sumke
      let xke := var .head (Γᵢ := Γᵢ) (Γc := Γc) (Γ := Γ.termExt ..) (x := x)
        (σ := qual <| .mono <| .prodOrSum .sum μ₁
          (.lift (.mk κ (ϕ.app (.var (.bound 0)))) (.row [] (some κ))))
      let τke' := τke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
      let xke' := xke.sub (σ₁ := qual (.mono τ)) <| by
        let sumke' := sumke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
        apply SubtypingAndElaboration.trans sumke' _ <| .never τke'
        swap
        let μ₁ke' := μ₁ke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
        apply SubtypingAndElaboration.trans sumke' _ <| .decay (.sum μ₁ke' .empty_row) .comm .C
        swap
        apply SubtypingAndElaboration.sumRow ?ee sumke'
        case ee =>
        let ξ (i : Nat) : Monotype := default
        let τ' (i : Nat) : Monotype := default
        rw [← Range.map_get!_eq (as := []), List.length_nil, ← Option.someIf_true,
            ← Option.someIf_true, Range.map_eq_of_eq_of_mem'' (by
              intro i mem
              show _ = (ξ i, τ' i)
              nomatch mem
            )]
        rw (occs := .pos [3]) [Range.map_eq_of_eq_of_mem'' (by
              intro i mem
              show _ = (ξ i, (ϕ.app (.var (.bound 0))).Monotype_open (τ' i))
              nomatch mem
            )]
        apply RowEquivalenceAndElaboration.liftL _ _ .star
        swap
        rw (occs := .pos [4, 8]) [← List.length_nil]
        rw [Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          show _ = [].get! i
          nomatch mem
        ), Option.someIf_true, Range.map_get!_eq]
        let .sum _ liftke := sumke'
        exact liftke
      -- let f := ((«F⊗⊕ω».Term.lam ((«Type».lam K (A₁.app («Type».var («F⊗⊕ω».TypeVar.bound 0)))).listApp («Type».list [])).sum
      --       ((«F⊗⊕ω».Term.lam («Type».list []).sum ((«F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.bound 0)).sumElim [])).app
      --         ((«F⊗⊕ω».Term.lam
      --               ((«Type».lam K (A₁.app («Type».var («F⊗⊕ω».TypeVar.bound 0)))).listApp («Type».list [])).sum
      --               ((«F⊗⊕ω».Term.lam («Type».list []).sum («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.bound 0))).app
      --                 (((Term.typeLam («F⊗⊕ω».Kind.star.arr «F⊗⊕ω».Kind.star)
      --                           («F⊗⊕ω».Term.lam
      --                             ((«Type».var («F⊗⊕ω».TypeVar.bound 0)).listApp
      --                                 ((«Type».lam K (A₁.app («Type».var («F⊗⊕ω».TypeVar.bound 0)))).listApp
      --                                   («Type».list []))).sum
      --                             («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.bound 0)))).typeApp
      --                       («Type».lam «F⊗⊕ω».Kind.star («Type».var («F⊗⊕ω».TypeVar.bound 0)))).app
      --                   («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.bound 0))))).app
      --           («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.bound 0))))).app
      --   («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free x)))
      let .app E'lc _ := xke'.soundness τke' Γᵢw Γcw Γxwe |>.TermVarLocallyClosed_of
      have : «F⊗⊕ω».Term.var (.free x) = .TermVar_open (.var (.bound 0)) x := by
        rw [«F⊗⊕ω».Term.TermVar_open, if_pos rfl]
      rw [← E'lc.TermVar_open_id (x := x), this, ← «F⊗⊕ω».Term.TermVar_open] at xke'
      exact xke'
    · exact sumke

end TabularTypeInterpreter
