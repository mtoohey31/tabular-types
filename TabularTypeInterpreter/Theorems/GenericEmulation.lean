import TabularTypeInterpreter.Lemmas.Term
import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Theorems.Term

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std
open Term
open Term.TypingAndElaboration
open TypeScheme
open Monotype

instance : Inhabited Monotype where
  default := .row [] none
in
theorem ana_emulation (ρke : [[Γc; Γ ⊢ ρ : R κ ⇝ A₀]]) (ϕke : [[Γc; Γ ⊢ ϕ : κ ↦ * ⇝ A₁]])
  (μke : [[Γc; Γ ⊢ μ : U ⇝ B₁]]) (τke : [[Γc; Γ ⊢ τ : * ⇝ A₂]])
  (Mte : [[Γᵢ; Γc; Γ ⊢ M : ∀ aₗ : L. ∀ aₜ : κ. ∀ aₚ : R κ. ∀ aᵢ : R κ. ∀ aₙ : R κ. aₚ$2 ⊙(N) ⟨aₗ$4 ▹ aₜ$3⟩ ~ aᵢ$1 ⇒ aᵢ$1 ⊙(N) aₙ$0 ~ ρ ⇒ ⌊aₗ$4⌋ → (ϕ aₜ$3) → τ ⇝ E]])
  (indce : [[Γᵢ; Γc; Γ ⊨ Ind ρ ⇝ F]]) (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ F, [[Γᵢ; Γc; Γ ⊢ ind (λ a : R κ. (Σ(μ) (Lift (λ a' : κ. ϕ a'$0) a$0)) → τ) ρ; (λ xₗ. λ xₐ. xₐ$0 ▿ (λ x. (M xₗ$2) x$0/xₗ$2)); (λ x. x$0) : (Σ(μ) (Lift (λ a : κ. ϕ a$0) ρ)) → τ ⇝ F]] := by
  let ⟨K, κe⟩ := κ.Elaboration_total
  apply Exists.intro _
  let Mlc := Mte.TermVarLocallyClosed_of
  let .qual (.mono ρlc) := ρke.TypeVarLocallyClosed_of
  let .qual (.mono τlc) := τke.TypeVarLocallyClosed_of
  let .qual (.mono ϕlc) := ϕke.TypeVarLocallyClosed_of
  let Elc := Mte.soundness (by
    apply KindingAndElaboration.scheme Γ.typeVarDom
    intro aₗ aₗnin
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
    rw [ρlc.weakening (n := 4).TypeVar_open_id, τlc.weakening (n := 4).TypeVar_open_id,
        ϕlc.weakening (n := 4).TypeVar_open_id]
    apply defer_equality'
    · apply KindingAndElaboration.scheme <| aₗ :: Γ.typeVarDom
      intro aₜ aₜnin
      simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
      rw [ρlc.weakening (n := 3).TypeVar_open_id, τlc.weakening (n := 3).TypeVar_open_id,
          ϕlc.weakening (n := 3).TypeVar_open_id]
      apply defer_equality'
      · apply KindingAndElaboration.scheme <| aₜ :: aₗ :: Γ.typeVarDom
        intro aₚ aₚnin
        simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
        rw [ρlc.weakening (n := 2).TypeVar_open_id, τlc.weakening (n := 2).TypeVar_open_id,
            ϕlc.weakening (n := 2).TypeVar_open_id]
        apply defer_equality'
        · apply KindingAndElaboration.scheme <| aₚ :: aₜ :: aₗ :: Γ.typeVarDom
          intro aᵢ aᵢnin
          simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
          rw [ρlc.weakening (n := 1).TypeVar_open_id, τlc.weakening (n := 1).TypeVar_open_id,
              ϕlc.weakening (n := 1).TypeVar_open_id]
          apply defer_equality'
          · apply KindingAndElaboration.scheme <| aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom
            intro aₙ aₙnin
            simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
            rw [ρlc.TypeVar_open_id, τlc.TypeVar_open_id, ϕlc.TypeVar_open_id]
            apply defer_equality'
            · let Γawe := Γwe.typeExt aₗnin .label |>.typeExt aₜnin κe |>.typeExt aₚnin κe.row
                |>.typeExt aᵢnin κe.row |>.typeExt aₙnin κe.row
              apply KindingAndElaboration.qual <| .concat .comm
                (.var (.typeExt sorry (.typeExt sorry .head)))
                (.singleton_row
                  (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
                  (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
                (.var (.typeExt sorry .head)) κe
                (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head)))
                  (.var (.typeExt sorry .head)) κe)
                (.contain .comm
                  (.singleton_row
                    (.var (.typeExt sorry (.typeExt sorry
                      (.typeExt sorry (.typeExt sorry .head)))))
                    (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
                  (.var (.typeExt sorry .head)) κe)
              · let ρke' := ρke.weakening Γawe (Γ'' := .empty)
                  (Γ' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
                apply KindingAndElaboration.qual <| .concat .comm (.var (.typeExt sorry .head))
                  (.var .head) ρke' κe (.contain .comm (.var (.typeExt sorry .head)) ρke' κe)
                  (.contain .comm (.var .head) ρke' κe)
                · apply KindingAndElaboration.arr <| .floor <| .var <| .typeExt sorry <|
                    .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
                  let ϕke' := ϕke.weakening Γawe (Γ'' := .empty) (Γ' := .typeExt (.typeExt
                      (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
                  let τke' := τke.weakening Γawe (Γ'' := .empty) (Γ' := .typeExt (.typeExt
                      (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
                  exact ϕke'.app (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))
                    |>.arr τke'
                · exact .star
              · exact .star




                  -- (.singleton_row
                  --   (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
                  --   (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))
                  -- (.var (.typeExt sorry .head)) κe
                  -- (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head)))
                  --   (.var (.typeExt sorry .head)) κe)
                  -- (.contain .comm
                  --   (.singleton_row
                  --     (.var (.typeExt sorry (.typeExt sorry
                  --       (.typeExt sorry (.typeExt sorry .head)))))
                  --     (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
                  --   (.var (.typeExt sorry .head)) κe)

  ) Γᵢw Γcw Γwe |>.TermVarLocallyClosed_of
  let .qual (.mono μlc) := μke.TypeVarLocallyClosed_of
  let A₁lc := ϕke.soundness Γcw Γwe (.arr κe .star) |>.TypeVarLocallyClosed_of
  let A₂lc := τke.soundness Γcw Γwe .star |>.TypeVarLocallyClosed_of
  have : Monotype.arr (.prodOrSum .sum μ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) ρ)) τ =
    .Monotype_open (.arr (.prodOrSum .sum μ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) (.var (.bound 0)))) τ) ρ := by
    simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
    exact ⟨
      ⟨μlc.Monotype_open_id.symm, ϕlc.weakening (n := 1).Monotype_open_id.symm⟩,
      τlc.Monotype_open_id.symm
    ⟩
  rw [this]
  apply «ind» Γ.typeVarDom Γ.typeVarDom ρke ?ϕappake κe ?M'te ?Nte indce
  case ϕappake =>
    intro a anin
    simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open]
    rw [μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id]
    let Γawe := Γwe.typeExt anin κe.row
    let μke' := μke.weakening Γawe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
    let sumke := KindingAndElaboration.sum μke' <| .lift [[Γ, a : R κ]].typeVarDom (by
      intro a' a'nin
      let Γaa'we := Γawe.typeExt a'nin κe
      let ϕke' := ϕke.weakening Γaa'we (Γ' := .typeExt (.typeExt .empty ..) ..) (Γ'' := .empty)
      let ϕappa'ke := ϕke'.app <| .var .head
      have : ϕ.app (.var (.free a')) = .TypeVar_open (ϕ.app (.var (.bound 0))) a' := by
        rw [Monotype.TypeVar_open, Monotype.TypeVar_open, if_pos rfl, ϕlc.TypeVar_open_id]
      rw [this] at ϕappa'ke
      have : A₁.app (.var (.free a')) = .TypeVar_open (A₁.app (.var (.bound 0))) a' := by
        rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl, A₁lc.TypeVar_open_id]
      rw [this] at ϕappa'ke
      exact ϕappa'ke
    ) κe (.var .head)
    let sumarrke := sumke.arr <| τke.weakening Γawe (Γ' := .typeExt .empty ..)
    have : ((«Type».lam K (A₁.app (.var (.bound 0)))).listApp (.var (.free a))).sum.arr A₂ =
      .TypeVar_open
        (((«Type».lam K (A₁.app (.var (.bound 0)))).listApp (.var (.bound 0))).sum.arr A₂) a := by
      simp [Type.TypeVar_open]
      rw [A₁lc.weaken (n := 1).TypeVar_open_id, A₂lc.TypeVar_open_id]
      exact ⟨rfl, rfl⟩
    rw [this] at sumarrke
    exact sumarrke
  case M'te =>
    intro aₗ aₗnin
    intro aₜ aₜnin
    let aₗneaₜ := List.ne_of_not_mem_cons aₜnin
    intro aₚ aₚnin
    let aₜneaₚ := List.ne_of_not_mem_cons aₚnin
    let aₗneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₚnin
    intro aᵢ aᵢnin
    let aₚneaᵢ := List.ne_of_not_mem_cons aᵢnin
    let aₜneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aᵢnin
    let aₗneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons aᵢnin
    intro aₙ aₙnin
    let aᵢneaₙ := List.ne_of_not_mem_cons aₙnin
    let aₚneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙnin
    let aₜneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons aₙnin
    let aₗneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙnin
    symm at aₗneaₜ aₜneaₚ aₗneaₚ aₚneaᵢ aₜneaᵢ aₗneaᵢ aᵢneaₙ aₚneaₙ aₜneaₙ aₗneaₙ
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
          TypeLambda.TypeVar_open]
    rw [μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id,
        μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id]
    let Γawe := Γwe.typeExt aₗnin .label |>.typeExt aₜnin κe |>.typeExt aₚnin κe.row
      |>.typeExt aᵢnin κe.row |>.typeExt aₙnin κe.row
    let Mte' := Mte.weakening Γawe (Γ'' := .empty)
      (Γ' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
    let Mte'' := Mte'.schemeE <| .var <| .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <|
      .typeExt aₗneaₜ .head
    let Mte''' := Mte''.schemeE <| .var <| .typeExt aₜneaₙ <| .typeExt aₜneaᵢ <|
      .typeExt aₜneaₚ .head
    let Mte'''' := Mte'''.schemeE <| .var <| .typeExt aₚneaₙ <| .typeExt aₚneaᵢ .head
    let Mte''''' := Mte''''.schemeE <| .var <| .typeExt aᵢneaₙ .head
    let Mte'''''' := Mte'''''.schemeE <| .var .head
    simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
          Monotype.Monotype_open] at Mte''''''
    rw [ρlc.weakening (n := 4).Monotype_open_id, ρlc.weakening (n := 3).Monotype_open_id,
        ρlc.weakening (n := 2).Monotype_open_id, ρlc.weakening (n := 1).Monotype_open_id,
        ρlc.Monotype_open_id, ϕlc.weakening (n := 4).Monotype_open_id,
        ϕlc.weakening (n := 3).Monotype_open_id, ϕlc.weakening (n := 2).Monotype_open_id,
        ϕlc.weakening (n := 1).Monotype_open_id, ϕlc.Monotype_open_id,
        τlc.weakening (n := 4).Monotype_open_id, τlc.weakening (n := 3).Monotype_open_id,
        τlc.weakening (n := 2).Monotype_open_id, τlc.weakening (n := 1).Monotype_open_id,
        τlc.Monotype_open_id] at Mte''''''
    let ⟨_, .qual ψ₀ke (.qual ψ₁ke _ _) _⟩ := Mte''''''.to_Kinding Γᵢw Γcw Γawe
    apply defer_equality
    · apply qualI Γ.termVarDom ψ₀ke
      intro xₙₗ xₙₗnin
      let Γaxₙₗwe := Γawe.constrExt xₙₗnin ψ₀ke
      apply defer_equality
      · let ψ₁ke' := ψ₁ke.weakening Γaxₙₗwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
        apply qualI (xₙₗ :: Γ.termVarDom) ψ₁ke'
        intro xₙᵣ xₙᵣnin
        let Γaxₙₗᵣwe := Γaxₙₗwe.constrExt xₙᵣnin ψ₁ke'
        apply defer_equality
        · apply lam (xₙᵣ :: xₙₗ :: Γ.termVarDom) ?bodyke <| .floor <| .var <| .constrExt <| .constrExt <|
            .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <| .typeExt aₗneaₜ .head
          case bodyke =>
          intro xₗ xₗnin
          let Γaxₙₗᵣxₗwe := Γaxₙₗᵣwe.termExt xₗnin <| .floor <| .var <| .constrExt <| .constrExt <|
            .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <| .typeExt aₗneaₜ .head
          simp [Term.TermVar_open]
          rw [Mlc.weakening (n := 2).TermVar_open_id]
          apply defer_equality
          · let μke' := μke.weakening Γaxₙₗᵣxₗwe (Γ'' := .empty)
              (Γ' := .termExt (.constrExt (.constrExt (.typeExt (.typeExt
                (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..)
            let τke' := τke.weakening Γaxₙₗᵣxₗwe (Γ'' := .empty)
              (Γ' := .termExt (.constrExt (.constrExt (.typeExt (.typeExt
                (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..)
            let arrke := KindingAndElaboration.arr (.sum μke' <| .lift
              (aₙ :: aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom) (by
                intro a anin
                let Γaxₙₗᵣxₗawe := Γaxₙₗᵣxₗwe.typeExt anin κe
                let ϕke' := ϕke.weakening Γaxₙₗᵣxₗawe (Γ'' := .empty)
                  (Γ' := .typeExt (.termExt (.constrExt (.constrExt (.typeExt (.typeExt
                    (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..) ..)
                let ϕappake := ϕke'.app <| .var .head
                have : ϕ.app (.var (.free a)) = .TypeVar_open (ϕ.app (.var (.bound 0))) a := by
                  simp [Monotype.TypeVar_open]
                  rw [ϕlc.TypeVar_open_id]
                rw [this] at ϕappake
                have : A₁.app (.var (.free a)) = .TypeVar_open (A₁.app (.var (.bound 0))) a := by
                  simp [Type.TypeVar_open]
                  rw [A₁lc.TypeVar_open_id]
                rw [this] at ϕappake
                exact ϕappake
              ) κe (.var (.termExt (.constrExt (.constrExt (.typeExt sorry (.typeExt sorry .head))))))) τke'
            apply lam (xₗ :: xₙᵣ :: xₙₗ :: Γ.termVarDom) ?elimte arrke
            case elimte =>
            intro xₐ xₐnin
            let Γaxₙₗᵣxₗₐwe := Γaxₙₗᵣxₗwe.termExt xₐnin arrke
            simp [Term.TermVar_open]
            rw [Mlc.weakening (n := 1).TermVar_open_id]
            apply defer_equality
            · apply elim <| .var .head
              let μke'' := μke'.weakening Γaxₙₗᵣxₗₐwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
              let ϕke' := ϕke.weakening Γaxₙₗᵣxₗₐwe (Γ'' := .empty)
                (Γ' := .termExt (.termExt (.constrExt (.constrExt (.typeExt (.typeExt
                  (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..) ..)
              let sumke := KindingAndElaboration.sum μke'' <| .singleton_row
                (.var (.termExt (.termExt (.constrExt (.constrExt (.typeExt sorry
                  (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))))))) <|
                ϕke'.app <| .var <| .termExt <| .termExt <| .constrExt <| .constrExt <| .typeExt sorry <|
                  .typeExt sorry <| .typeExt sorry .head
              apply lam (xₐ :: xₗ :: xₙᵣ :: xₙₗ :: Γ.termVarDom) ?appke sumke
              case appke =>
              intro x xnin
              let Γaxₙₗᵣxₗₐxwe := Γaxₙₗᵣxₗₐwe.termExt xnin sumke
              simp [Term.TermVar_open]
              rw [Mlc.TermVar_open_id]
              apply defer_equality
              · apply TypingAndElaboration.app (.app _ (.var (.termExt sorry (.termExt sorry .head))))
                · apply unlabelSum (.var .head) (.var (.termExt sorry (.termExt sorry .head)))
                  let ϕke'' := ϕke'.weakening Γaxₙₗᵣxₗₐxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
                  exact ϕke''.app <| .var <| .termExt <| .termExt <| .termExt <| .constrExt <| .constrExt <|
                    .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
                swap
                · let Mte''''''' := Mte''''''.weakening Γaxₙₗᵣxₗₐxwe (Γ'' := .empty)
                    (Γ' := .termExt (.termExt (.termExt (.constrExt (.constrExt .empty ..) ..) ..) ..) ..)
                  let Mte'''''''' := Mte'''''''.qualE <| .local <| .termExt sorry <| .termExt sorry <|
                    .termExt sorry <| .constrExt sorry .head
                  exact Mte''''''''.qualE <| .local <| .termExt sorry <| .termExt sorry <|
                    .termExt sorry .head
              · show _ = «F⊗⊕ω».Term.TermVar_open (((((((((E.typeApp («Type».var («F⊗⊕ω».TypeVar.free aₗ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aₜ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aₚ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aᵢ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aₙ))).app («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free xₙₗ))).app («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free xₙᵣ))).app («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free xₗ))).app ((«F⊗⊕ω».Term.var (.bound 0)).sumElim [«F⊗⊕ω».Term.lam (A₁.app («Type».var («F⊗⊕ω».TypeVar.free aₜ))) («F⊗⊕ω».Term.var (.bound 0))])) x
                simp [«F⊗⊕ω».Term.TermVar_open]
            · sorry
          · sorry
        · sorry
      · sorry
    · sorry
  case Nte =>
    simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
    rw [μlc.Monotype_open_id, ϕlc.weakening (n := 1).Monotype_open_id, τlc.Monotype_open_id]
    let sumke : [[Γc; Γ ⊢ Σ(μ) (Lift (λ a : κ. ϕ a$0) ⟨ : κ ⟩) : * ⇝ ⊕ (λ a : K. A₁ a$0) ⟦{ }⟧]] := by
      apply KindingAndElaboration.sum μke
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
        (σ := qual <| .mono <| .prodOrSum .sum μ
          (.lift (.mk κ (ϕ.app (.var (.bound 0)))) (.row [] (some κ))))
      let τke' := τke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
      let xke' := xke.sub (σ₁ := qual (.mono τ)) <| by
        let sumke' := sumke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
        apply SubtypingAndElaboration.trans sumke' _ <| .never τke'
        swap
        let μke' := μke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
        apply SubtypingAndElaboration.trans sumke' _ <| .decay (.sum μke' .empty_row) .comm .C
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
      let .app E'lc _ := xke'.soundness τke' Γᵢw Γcw Γxwe |>.TermVarLocallyClosed_of
      have : «F⊗⊕ω».Term.var (.free x) = .TermVar_open (.var (.bound 0)) x := by
        rw [«F⊗⊕ω».Term.TermVar_open, if_pos rfl]
      rw [← E'lc.TermVar_open_id (x := x), this, ← «F⊗⊕ω».Term.TermVar_open] at xke'
      exact xke'
    · exact sumke
where
  defer_equality {Γᵢ Γc Γ M σ E F} (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) (eq : E = F)
    : TypingAndElaboration Γᵢ Γc Γ M σ F := by rwa [eq] at Mte
  defer_equality' {Γc Γ σ κ A B} (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]]) (eq : A = B)
    : KindingAndElaboration Γc Γ σ κ B := by rwa [eq] at σke

end TabularTypeInterpreter
