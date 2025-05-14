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

-- instance : Inhabited Monotype where
--   default := .row [] none
-- in
-- theorem ana_emulation (ρke : [[Γc; Γ ⊢ ρ : R κ ⇝ A₀]]) (ϕke : [[Γc; Γ ⊢ ϕ : κ ↦ * ⇝ A₁]])
--   (μke : [[Γc; Γ ⊢ μ : U ⇝ B₁]]) (τke : [[Γc; Γ ⊢ τ : * ⇝ A₂]])
--   (Mte : [[Γᵢ; Γc; Γ ⊢ M : ∀ aₗ : L. ∀ aₜ : κ. ∀ aₚ : R κ. ∀ aᵢ : R κ. ∀ aₙ : R κ. aₚ$2 ⊙(N) ⟨aₗ$4 ▹ aₜ$3⟩ ~ aᵢ$1 ⇒ aᵢ$1 ⊙(N) aₙ$0 ~ ρ ⇒ ⌊aₗ$4⌋ → (ϕ aₜ$3) → τ ⇝ E]])
--   (indce : [[Γᵢ; Γc; Γ ⊨ Ind ρ ⇝ F]]) (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
--   : ∃ F, [[Γᵢ; Γc; Γ ⊢ ind (λ a : R κ. (Σ(μ) (Lift (λ a' : κ. ϕ a'$0) a$0)) → τ) ρ; (λ xₗ. λ xₐ. xₐ$0 ▿ (λ x. (M xₗ$2) x$0/xₗ$2)); (λ x. x$0) : (Σ(μ) (Lift (λ a : κ. ϕ a$0) ρ)) → τ ⇝ F]] := by
--   let ⟨K, κe⟩ := κ.Elaboration_total
--   apply Exists.intro _
--   let Mlc := Mte.TermVarLocallyClosed_of
--   let .qual (.mono ρlc) := ρke.TypeVarLocallyClosed_of
--   let .qual (.mono τlc) := τke.TypeVarLocallyClosed_of
--   let .qual (.mono ϕlc) := ϕke.TypeVarLocallyClosed_of
--   let Elc := Mte.soundness (by
--     apply KindingAndElaboration.scheme Γ.typeVarDom
--     intro aₗ aₗnin
--     simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
--     rw [ρlc.weakening (n := 4).TypeVar_open_id, τlc.weakening (n := 4).TypeVar_open_id,
--         ϕlc.weakening (n := 4).TypeVar_open_id]
--     apply defer_equality'
--     · apply KindingAndElaboration.scheme <| aₗ :: Γ.typeVarDom
--       intro aₜ aₜnin
--       simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
--       rw [ρlc.weakening (n := 3).TypeVar_open_id, τlc.weakening (n := 3).TypeVar_open_id,
--           ϕlc.weakening (n := 3).TypeVar_open_id]
--       apply defer_equality'
--       · apply KindingAndElaboration.scheme <| aₜ :: aₗ :: Γ.typeVarDom
--         intro aₚ aₚnin
--         simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
--         rw [ρlc.weakening (n := 2).TypeVar_open_id, τlc.weakening (n := 2).TypeVar_open_id,
--             ϕlc.weakening (n := 2).TypeVar_open_id]
--         apply defer_equality'
--         · apply KindingAndElaboration.scheme <| aₚ :: aₜ :: aₗ :: Γ.typeVarDom
--           intro aᵢ aᵢnin
--           simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
--           rw [ρlc.weakening (n := 1).TypeVar_open_id, τlc.weakening (n := 1).TypeVar_open_id,
--               ϕlc.weakening (n := 1).TypeVar_open_id]
--           apply defer_equality'
--           · apply KindingAndElaboration.scheme <| aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom
--             intro aₙ aₙnin
--             simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open]
--             rw [ρlc.TypeVar_open_id, τlc.TypeVar_open_id, ϕlc.TypeVar_open_id]
--             apply defer_equality'
--             · let Γawe := Γwe.typeExt aₗnin .label |>.typeExt aₜnin κe |>.typeExt aₚnin κe.row
--                 |>.typeExt aᵢnin κe.row |>.typeExt aₙnin κe.row
--               apply KindingAndElaboration.qual <| .concat .comm
--                 (.var (.typeExt sorry (.typeExt sorry .head)))
--                 (.singleton_row
--                   (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
--                   (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
--                 (.var (.typeExt sorry .head)) κe
--                 (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head)))
--                   (.var (.typeExt sorry .head)) κe)
--                 (.contain .comm
--                   (.singleton_row
--                     (.var (.typeExt sorry (.typeExt sorry
--                       (.typeExt sorry (.typeExt sorry .head)))))
--                     (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
--                   (.var (.typeExt sorry .head)) κe)
--               · let ρke' := ρke.weakening Γawe (Γ'' := .empty)
--                   (Γ' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
--                 apply KindingAndElaboration.qual <| .concat .comm (.var (.typeExt sorry .head))
--                   (.var .head) ρke' κe (.contain .comm (.var (.typeExt sorry .head)) ρke' κe)
--                   (.contain .comm (.var .head) ρke' κe)
--                 · apply KindingAndElaboration.arr <| .floor <| .var <| .typeExt sorry <|
--                     .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
--                   let ϕke' := ϕke.weakening Γawe (Γ'' := .empty) (Γ' := .typeExt (.typeExt
--                       (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
--                   let τke' := τke.weakening Γawe (Γ'' := .empty) (Γ' := .typeExt (.typeExt
--                       (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
--                   exact ϕke'.app (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))
--                     |>.arr τke'
--                 · exact .star
--               · exact .star




--                   -- (.singleton_row
--                   --   (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
--                   --   (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))
--                   -- (.var (.typeExt sorry .head)) κe
--                   -- (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head)))
--                   --   (.var (.typeExt sorry .head)) κe)
--                   -- (.contain .comm
--                   --   (.singleton_row
--                   --     (.var (.typeExt sorry (.typeExt sorry
--                   --       (.typeExt sorry (.typeExt sorry .head)))))
--                   --     (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
--                   --   (.var (.typeExt sorry .head)) κe)

--   ) Γᵢw Γcw Γwe |>.TermVarLocallyClosed_of
--   let .qual (.mono μlc) := μke.TypeVarLocallyClosed_of
--   let A₁lc := ϕke.soundness Γcw Γwe (.arr κe .star) |>.TypeVarLocallyClosed_of
--   let A₂lc := τke.soundness Γcw Γwe .star |>.TypeVarLocallyClosed_of
--   have : Monotype.arr (.prodOrSum .sum μ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) ρ)) τ =
--     .Monotype_open (.arr (.prodOrSum .sum μ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) (.var (.bound 0)))) τ) ρ := by
--     simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
--     exact ⟨
--       ⟨μlc.Monotype_open_id.symm, ϕlc.weakening (n := 1).Monotype_open_id.symm⟩,
--       τlc.Monotype_open_id.symm
--     ⟩
--   rw [this]
--   apply «ind» Γ.typeVarDom Γ.typeVarDom ρke ?ϕappake κe ?M'te ?Nte indce
--   case ϕappake =>
--     intro a anin
--     simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open]
--     rw [μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id]
--     let Γawe := Γwe.typeExt anin κe.row
--     let μke' := μke.weakening Γawe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
--     let sumke := KindingAndElaboration.sum μke' <| .lift [[Γ, a : R κ]].typeVarDom (by
--       intro a' a'nin
--       let Γaa'we := Γawe.typeExt a'nin κe
--       let ϕke' := ϕke.weakening Γaa'we (Γ' := .typeExt (.typeExt .empty ..) ..) (Γ'' := .empty)
--       let ϕappa'ke := ϕke'.app <| .var .head
--       have : ϕ.app (.var (.free a')) = .TypeVar_open (ϕ.app (.var (.bound 0))) a' := by
--         rw [Monotype.TypeVar_open, Monotype.TypeVar_open, if_pos rfl, ϕlc.TypeVar_open_id]
--       rw [this] at ϕappa'ke
--       have : A₁.app (.var (.free a')) = .TypeVar_open (A₁.app (.var (.bound 0))) a' := by
--         rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl, A₁lc.TypeVar_open_id]
--       rw [this] at ϕappa'ke
--       exact ϕappa'ke
--     ) κe (.var .head)
--     let sumarrke := sumke.arr <| τke.weakening Γawe (Γ' := .typeExt .empty ..)
--     have : ((«Type».lam K (A₁.app (.var (.bound 0)))).listApp (.var (.free a))).sum.arr A₂ =
--       .TypeVar_open
--         (((«Type».lam K (A₁.app (.var (.bound 0)))).listApp (.var (.bound 0))).sum.arr A₂) a := by
--       simp [Type.TypeVar_open]
--       rw [A₁lc.weaken (n := 1).TypeVar_open_id, A₂lc.TypeVar_open_id]
--       exact ⟨rfl, rfl⟩
--     rw [this] at sumarrke
--     exact sumarrke
--   case M'te =>
--     intro aₗ aₗnin
--     intro aₜ aₜnin
--     let aₗneaₜ := List.ne_of_not_mem_cons aₜnin
--     intro aₚ aₚnin
--     let aₜneaₚ := List.ne_of_not_mem_cons aₚnin
--     let aₗneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₚnin
--     intro aᵢ aᵢnin
--     let aₚneaᵢ := List.ne_of_not_mem_cons aᵢnin
--     let aₜneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aᵢnin
--     let aₗneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
--       List.not_mem_of_not_mem_cons aᵢnin
--     intro aₙ aₙnin
--     let aᵢneaₙ := List.ne_of_not_mem_cons aₙnin
--     let aₚneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙnin
--     let aₜneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
--       List.not_mem_of_not_mem_cons aₙnin
--     let aₗneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
--       List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙnin
--     symm at aₗneaₜ aₜneaₚ aₗneaₚ aₚneaᵢ aₜneaᵢ aₗneaᵢ aᵢneaₙ aₚneaₙ aₜneaₙ aₗneaₙ
--     simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
--           TypeLambda.TypeVar_open]
--     rw [μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id,
--         μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id]
--     let Γawe := Γwe.typeExt aₗnin .label |>.typeExt aₜnin κe |>.typeExt aₚnin κe.row
--       |>.typeExt aᵢnin κe.row |>.typeExt aₙnin κe.row
--     let Mte' := Mte.weakening Γawe (Γ'' := .empty)
--       (Γ' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
--     let Mte'' := Mte'.schemeE <| .var <| .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <|
--       .typeExt aₗneaₜ .head
--     let Mte''' := Mte''.schemeE <| .var <| .typeExt aₜneaₙ <| .typeExt aₜneaᵢ <|
--       .typeExt aₜneaₚ .head
--     let Mte'''' := Mte'''.schemeE <| .var <| .typeExt aₚneaₙ <| .typeExt aₚneaᵢ .head
--     let Mte''''' := Mte''''.schemeE <| .var <| .typeExt aᵢneaₙ .head
--     let Mte'''''' := Mte'''''.schemeE <| .var .head
--     simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
--           Monotype.Monotype_open] at Mte''''''
--     rw [ρlc.weakening (n := 4).Monotype_open_id, ρlc.weakening (n := 3).Monotype_open_id,
--         ρlc.weakening (n := 2).Monotype_open_id, ρlc.weakening (n := 1).Monotype_open_id,
--         ρlc.Monotype_open_id, ϕlc.weakening (n := 4).Monotype_open_id,
--         ϕlc.weakening (n := 3).Monotype_open_id, ϕlc.weakening (n := 2).Monotype_open_id,
--         ϕlc.weakening (n := 1).Monotype_open_id, ϕlc.Monotype_open_id,
--         τlc.weakening (n := 4).Monotype_open_id, τlc.weakening (n := 3).Monotype_open_id,
--         τlc.weakening (n := 2).Monotype_open_id, τlc.weakening (n := 1).Monotype_open_id,
--         τlc.Monotype_open_id] at Mte''''''
--     let ⟨_, .qual ψ₀ke (.qual ψ₁ke _ _) _⟩ := Mte''''''.to_Kinding Γᵢw Γcw Γawe
--     apply defer_equality
--     · apply qualI Γ.termVarDom ψ₀ke
--       intro xₙₗ xₙₗnin
--       let Γaxₙₗwe := Γawe.constrExt xₙₗnin ψ₀ke
--       apply defer_equality
--       · let ψ₁ke' := ψ₁ke.weakening Γaxₙₗwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
--         apply qualI (xₙₗ :: Γ.termVarDom) ψ₁ke'
--         intro xₙᵣ xₙᵣnin
--         let Γaxₙₗᵣwe := Γaxₙₗwe.constrExt xₙᵣnin ψ₁ke'
--         apply defer_equality
--         · apply lam (xₙᵣ :: xₙₗ :: Γ.termVarDom) ?bodyke <| .floor <| .var <| .constrExt <| .constrExt <|
--             .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <| .typeExt aₗneaₜ .head
--           case bodyke =>
--           intro xₗ xₗnin
--           let Γaxₙₗᵣxₗwe := Γaxₙₗᵣwe.termExt xₗnin <| .floor <| .var <| .constrExt <| .constrExt <|
--             .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <| .typeExt aₗneaₜ .head
--           simp [Term.TermVar_open]
--           rw [Mlc.weakening (n := 2).TermVar_open_id]
--           apply defer_equality
--           · let μke' := μke.weakening Γaxₙₗᵣxₗwe (Γ'' := .empty)
--               (Γ' := .termExt (.constrExt (.constrExt (.typeExt (.typeExt
--                 (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..)
--             let τke' := τke.weakening Γaxₙₗᵣxₗwe (Γ'' := .empty)
--               (Γ' := .termExt (.constrExt (.constrExt (.typeExt (.typeExt
--                 (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..)
--             let arrke := KindingAndElaboration.arr (.sum μke' <| .lift
--               (aₙ :: aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom) (by
--                 intro a anin
--                 let Γaxₙₗᵣxₗawe := Γaxₙₗᵣxₗwe.typeExt anin κe
--                 let ϕke' := ϕke.weakening Γaxₙₗᵣxₗawe (Γ'' := .empty)
--                   (Γ' := .typeExt (.termExt (.constrExt (.constrExt (.typeExt (.typeExt
--                     (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..) ..)
--                 let ϕappake := ϕke'.app <| .var .head
--                 have : ϕ.app (.var (.free a)) = .TypeVar_open (ϕ.app (.var (.bound 0))) a := by
--                   simp [Monotype.TypeVar_open]
--                   rw [ϕlc.TypeVar_open_id]
--                 rw [this] at ϕappake
--                 have : A₁.app (.var (.free a)) = .TypeVar_open (A₁.app (.var (.bound 0))) a := by
--                   simp [Type.TypeVar_open]
--                   rw [A₁lc.TypeVar_open_id]
--                 rw [this] at ϕappake
--                 exact ϕappake
--               ) κe (.var (.termExt (.constrExt (.constrExt (.typeExt sorry (.typeExt sorry .head))))))) τke'
--             apply lam (xₗ :: xₙᵣ :: xₙₗ :: Γ.termVarDom) ?elimte arrke
--             case elimte =>
--             intro xₐ xₐnin
--             let Γaxₙₗᵣxₗₐwe := Γaxₙₗᵣxₗwe.termExt xₐnin arrke
--             simp [Term.TermVar_open]
--             rw [Mlc.weakening (n := 1).TermVar_open_id]
--             apply defer_equality
--             · apply elim <| .var .head
--               let μke'' := μke'.weakening Γaxₙₗᵣxₗₐwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
--               let ϕke' := ϕke.weakening Γaxₙₗᵣxₗₐwe (Γ'' := .empty)
--                 (Γ' := .termExt (.termExt (.constrExt (.constrExt (.typeExt (.typeExt
--                   (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..) ..)
--               let sumke := KindingAndElaboration.sum μke'' <| .singleton_row
--                 (.var (.termExt (.termExt (.constrExt (.constrExt (.typeExt sorry
--                   (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))))))) <|
--                 ϕke'.app <| .var <| .termExt <| .termExt <| .constrExt <| .constrExt <| .typeExt sorry <|
--                   .typeExt sorry <| .typeExt sorry .head
--               apply lam (xₐ :: xₗ :: xₙᵣ :: xₙₗ :: Γ.termVarDom) ?appke sumke
--               case appke =>
--               intro x xnin
--               let Γaxₙₗᵣxₗₐxwe := Γaxₙₗᵣxₗₐwe.termExt xnin sumke
--               simp [Term.TermVar_open]
--               rw [Mlc.TermVar_open_id]
--               apply defer_equality
--               · apply TypingAndElaboration.app (.app _ (.var (.termExt sorry (.termExt sorry .head))))
--                 · apply unlabelSum (.var .head) (.var (.termExt sorry (.termExt sorry .head)))
--                   let ϕke'' := ϕke'.weakening Γaxₙₗᵣxₗₐxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
--                   exact ϕke''.app <| .var <| .termExt <| .termExt <| .termExt <| .constrExt <| .constrExt <|
--                     .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
--                 swap
--                 · let Mte''''''' := Mte''''''.weakening Γaxₙₗᵣxₗₐxwe (Γ'' := .empty)
--                     (Γ' := .termExt (.termExt (.termExt (.constrExt (.constrExt .empty ..) ..) ..) ..) ..)
--                   let Mte'''''''' := Mte'''''''.qualE <| .local <| .termExt sorry <| .termExt sorry <|
--                     .termExt sorry <| .constrExt sorry .head
--                   exact Mte''''''''.qualE <| .local <| .termExt sorry <| .termExt sorry <|
--                     .termExt sorry .head
--               · show _ = «F⊗⊕ω».Term.TermVar_open (((((((((E.typeApp («Type».var («F⊗⊕ω».TypeVar.free aₗ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aₜ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aₚ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aᵢ))).typeApp («Type».var («F⊗⊕ω».TypeVar.free aₙ))).app («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free xₙₗ))).app («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free xₙᵣ))).app («F⊗⊕ω».Term.var («F⊗⊕ω».TermVar.free xₗ))).app ((«F⊗⊕ω».Term.var (.bound 0)).sumElim [«F⊗⊕ω».Term.lam (A₁.app («Type».var («F⊗⊕ω».TypeVar.free aₜ))) («F⊗⊕ω».Term.var (.bound 0))])) x
--                 simp [«F⊗⊕ω».Term.TermVar_open]
--             · sorry
--           · sorry
--         · sorry
--       · sorry
--     · sorry
--   case Nte =>
--     simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
--     rw [μlc.Monotype_open_id, ϕlc.weakening (n := 1).Monotype_open_id, τlc.Monotype_open_id]
--     let sumke : [[Γc; Γ ⊢ Σ(μ) (Lift (λ a : κ. ϕ a$0) ⟨ : κ ⟩) : * ⇝ ⊕ (λ a : K. A₁ a$0) ⟦{ }⟧]] := by
--       apply KindingAndElaboration.sum μke
--       apply KindingAndElaboration.lift Γ.typeVarDom
--       · intro a anin
--         let Γawe := Γwe.typeExt anin κe
--         rw [Monotype.TypeVar_open, Monotype.TypeVar_open, if_pos rfl, ϕlc.TypeVar_open_id]
--         let ϕappa := ϕke.weakening Γawe (Γ' := .typeExt .empty ..) (Γ'' := .empty).app (.var .head)
--         simp [Type.TypeVar_open]
--         rw [A₁lc.TypeVar_open_id]
--         exact ϕappa
--       · exact κe
--       · exact .empty_row
--     apply lam Γ.termVarDom
--     · intro x xnin
--       rw [Term.TermVar_open, if_pos rfl]
--       let Γxwe := Γwe.termExt xnin sumke
--       let xke := var .head (Γᵢ := Γᵢ) (Γc := Γc) (Γ := Γ.termExt ..) (x := x)
--         (σ := qual <| .mono <| .prodOrSum .sum μ
--           (.lift (.mk κ (ϕ.app (.var (.bound 0)))) (.row [] (some κ))))
--       let τke' := τke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
--       let xke' := xke.sub (σ₁ := qual (.mono τ)) <| by
--         let sumke' := sumke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
--         apply SubtypingAndElaboration.trans sumke' _ <| .never τke'
--         swap
--         let μke' := μke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
--         apply SubtypingAndElaboration.trans sumke' _ <| .decay (.sum μke' .empty_row) .comm .C
--         swap
--         apply SubtypingAndElaboration.sumRow ?ee sumke'
--         case ee =>
--         let ξ (i : Nat) : Monotype := default
--         let τ' (i : Nat) : Monotype := default
--         rw [← Range.map_get!_eq (as := []), List.length_nil, ← Option.someIf_true,
--             ← Option.someIf_true, Range.map_eq_of_eq_of_mem'' (by
--               intro i mem
--               show _ = (ξ i, τ' i)
--               nomatch mem
--             )]
--         rw (occs := .pos [3]) [Range.map_eq_of_eq_of_mem'' (by
--               intro i mem
--               show _ = (ξ i, (ϕ.app (.var (.bound 0))).Monotype_open (τ' i))
--               nomatch mem
--             )]
--         apply RowEquivalenceAndElaboration.liftL _ _ .star
--         swap
--         rw (occs := .pos [4, 8]) [← List.length_nil]
--         rw [Range.map_eq_of_eq_of_mem'' (by
--           intro i mem
--           show _ = [].get! i
--           nomatch mem
--         ), Option.someIf_true, Range.map_get!_eq]
--         let .sum _ liftke := sumke'
--         exact liftke
--       let .app E'lc _ := xke'.soundness τke' Γᵢw Γcw Γxwe |>.TermVarLocallyClosed_of
--       have : «F⊗⊕ω».Term.var (.free x) = .TermVar_open (.var (.bound 0)) x := by
--         rw [«F⊗⊕ω».Term.TermVar_open, if_pos rfl]
--       rw [← E'lc.TermVar_open_id (x := x), this, ← «F⊗⊕ω».Term.TermVar_open] at xke'
--       exact xke'
--     · exact sumke
-- where
--   defer_equality {Γᵢ Γc Γ M σ E F} (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) (eq : E = F)
--     : TypingAndElaboration Γᵢ Γc Γ M σ F := by rwa [eq] at Mte
--   defer_equality' {Γc Γ σ κ A B} (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]]) (eq : A = B)
--     : KindingAndElaboration Γc Γ σ κ B := by rwa [eq] at σke

theorem syn_emulation (ρke : [[Γc; Γ ⊢ ρ : R κ ⇝ A₀]]) (ϕke : [[Γc; Γ ⊢ ϕ : κ ↦ * ⇝ A₁]])
  (μke : [[Γc; Γ ⊢ μ : U ⇝ B]])
  (Mte : [[Γᵢ; Γc; Γ ⊢ M : ∀ aₗ : L. ∀ aₜ : κ. ∀ aₚ : R κ. ∀ aᵢ : R κ. ∀ aₙ : R κ. aₚ$2 ⊙(N) ⟨aₗ$4 ▹ aₜ$3⟩ ~ aᵢ$1 ⇒ aᵢ$1 ⊙(N) aₙ$0 ~ ρ ⇒ ⌊aₗ$4⌋ → ϕ aₜ$3 ⇝ E]])
  (indce : [[Γᵢ; Γc; Γ ⊨ Ind ρ ⇝ F]]) (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ F, [[Γᵢ; Γc; Γ ⊢ ind (λ a : R κ. Π(μ) (Lift (λ a' : κ. ϕ a'$0) a$0)) ρ; (λ xₗ. λ xₐ. xₐ$0 ++ {xₗ$1 ▹ M xₗ$1}); {} : Π(μ) (Lift (λ a : κ. ϕ a$0) ρ) ⇝ F]] := by
  let ⟨K, κe⟩ := κ.Elaboration_total
  let Eₛ : «F⊗⊕ω».Term := sorry
  let .qual (.mono ρlc) := ρke.TypeVarLocallyClosed_of
  let A₀lc := ρke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of
  let .qual (.mono ϕlc) := ϕke.TypeVarLocallyClosed_of
  let A₁lc := ϕke.soundness Γcw Γwe (κe.arr .star) |>.TypeVarLocallyClosed_of
  let .qual (.mono μlc) := μke.TypeVarLocallyClosed_of
  let Mlc := Mte.TermVarLocallyClosed_of
  let Ety := Mte.soundness (open KindingAndElaboration in by
    show KindingAndElaboration _ _ _ _ [[∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. (⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aₚ$3⟧)) → (⊗ (a$0 ⟦{aₜ$4}⟧)) → ⊗ (a$0 ⟦aᵢ$2⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦aₚ$4⟧)) → aₜ$0) → ((⊕ (a$1 ⟦{aₜ$5}⟧)) → aₜ$0) → (⊕ (a$1 ⟦aᵢ$3⟧)) → aₜ$0, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aᵢ$2⟧)) → ⊗ (a$0 ⟦aₚ$3⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦aₚ$3⟧)) → ⊕ (a$0 ⟦aᵢ$2⟧)}, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aᵢ$2⟧)) → ⊗ (a$0 ⟦{aₜ$4}⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦{aₜ$4}⟧)) → ⊕ (a$0 ⟦aᵢ$2⟧)}}) → (⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aᵢ$2⟧)) → (⊗ (a$0 ⟦aₙ$1⟧)) → ⊗ (a$0 ⟦A₀⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦aᵢ$3⟧)) → aₜ$0) → ((⊕ (a$1 ⟦aₙ$2⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₀⟧)) → aₜ$0, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → ⊗ (a$0 ⟦aᵢ$2⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦aᵢ$2⟧)) → ⊕ (a$0 ⟦A₀⟧)}, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → ⊗ (a$0 ⟦aₙ$1⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦aₙ$1⟧)) → ⊕ (a$0 ⟦A₀⟧)}}) → (⊗ { }) → A₁ aₜ$3]]
    apply scheme Γ.typeVarDom _ .label
    intro aₗ aₗnin
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
          Type.TypeVar_open]
    rw [ρlc.weakening (n := 4).TypeVar_open_id, ϕlc.weakening (n := 4).TypeVar_open_id,
        A₀lc.weaken (n := 5).TypeVar_open_id, A₀lc.weaken (n := 6).TypeVar_open_id,
        A₁lc.weaken (n := 4).TypeVar_open_id]
    apply scheme (aₗ :: Γ.typeVarDom) _ κe
    intro aₜ aₜnin
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
          Type.TypeVar_open]
    rw [ρlc.weakening (n := 3).TypeVar_open_id, ϕlc.weakening (n := 3).TypeVar_open_id,
        A₀lc.weaken (n := 4).TypeVar_open_id, A₀lc.weaken (n := 5).TypeVar_open_id,
        A₁lc.weaken (n := 3).TypeVar_open_id]
    apply scheme (aₜ :: aₗ :: Γ.typeVarDom) _ κe.row
    intro aₚ aₚnin
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
          Type.TypeVar_open]
    rw [ρlc.weakening (n := 2).TypeVar_open_id, ϕlc.weakening (n := 2).TypeVar_open_id,
        A₀lc.weaken (n := 3).TypeVar_open_id, A₀lc.weaken (n := 4).TypeVar_open_id,
        A₁lc.weaken (n := 2).TypeVar_open_id]
    apply scheme (aₚ :: aₜ :: aₗ :: Γ.typeVarDom) _ κe.row
    intro aᵢ aᵢnin
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
          Type.TypeVar_open]
    rw [ρlc.weakening (n := 1).TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id,
        A₀lc.weaken (n := 2).TypeVar_open_id, A₀lc.weaken (n := 3).TypeVar_open_id,
        A₁lc.weaken (n := 1).TypeVar_open_id]
    apply scheme (aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom) _ κe.row
    intro aₙ aₙnin
    simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
          Type.TypeVar_open]
    rw [ρlc.TypeVar_open_id, ϕlc.TypeVar_open_id, A₀lc.weaken (n := 1).TypeVar_open_id,
        A₀lc.weaken (n := 2).TypeVar_open_id, A₁lc.TypeVar_open_id]
    apply qual
      (.concat .comm (.var (.typeExt sorry (.typeExt sorry .head)))
        (.singleton_row
          (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
          (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
        (.var (.typeExt sorry .head)) κe
        (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head))) (.var (.typeExt sorry .head))
          κe)
        (.contain .comm
          (.singleton_row
            (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
            (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
          (.var (.typeExt sorry .head)) κe)) _ .star
    let Γawe := Γwe.typeExt aₗnin .label |>.typeExt aₜnin κe |>.typeExt aₚnin κe.row
      |>.typeExt aᵢnin κe.row |>.typeExt aₙnin κe.row
    let ρke' := ρke.weakening Γawe (Γ'' := .empty)
      (Γ' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
    apply qual
      (.concat .comm (.var (.typeExt sorry .head)) (.var .head) ρke' κe
        (.contain .comm (.var (.typeExt sorry .head)) ρke' κe)
        (.contain .comm (.var .head) ρke' κe)) _ .star
    exact .arr
      (.floor (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))) <|
      ϕke.weakening Γawe (Γ'' := .empty)
        (Γ' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) |>.app <|
      .var <| .typeExt sorry <| .typeExt sorry <| .typeExt sorry <| .head
  ) Γᵢw Γcw Γwe
  let Elc := Ety.TermVarLocallyClosed_of
  let Etlc := Ety.TermTypeVarLocallyClosed_of
  have : Monotype.prodOrSum .prod μ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) ρ) =
    .Monotype_open (.prodOrSum .prod μ (.lift (.mk κ (.app ϕ (.var (.bound 0)))) (.var (.bound 0)))) ρ := by
    simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
    exact ⟨μlc.Monotype_open_id.symm, ϕlc.weakening (n := 1).Monotype_open_id.symm⟩
  rw [this]
  apply Exists.intro [[⦅F [λ a : L K. ⊗ (λ a' : K. A₁ a'$0) ⟦a$0⟧] ⦅Λ aₗ : *. Λ aₜ : K. Λ aₚ : L K. Λ aᵢ : L K. Λ aₙ : L K. ⦅λ xₙₗ : ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aₚ$3⟧)) → (⊗ (a$0 ⟦{aₜ$4}⟧)) → ⊗ (a$0 ⟦aᵢ$2⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦aₚ$4⟧)) → aₜ$0) → ((⊕ (a$1 ⟦{aₜ$5}⟧)) → aₜ$0) → (⊕ (a$1 ⟦aᵢ$3⟧)) → aₜ$0, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aᵢ$2⟧)) → ⊗ (a$0 ⟦aₚ$3⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦aₚ$3⟧)) → ⊕ (a$0 ⟦aᵢ$2⟧)}, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aᵢ$2⟧)) → ⊗ (a$0 ⟦{aₜ$4}⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦{aₜ$4}⟧)) → ⊕ (a$0 ⟦aᵢ$2⟧)}}. ⦅λ xₙᵣ : ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦aᵢ$2⟧)) → (⊗ (a$0 ⟦aₙ$1⟧)) → ⊗ (a$0 ⟦A₀⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦aᵢ$3⟧)) → aₜ$0) → ((⊕ (a$1 ⟦aₙ$2⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₀⟧)) → aₜ$0, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → ⊗ (a$0 ⟦aᵢ$2⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦aᵢ$2⟧)) → ⊕ (a$0 ⟦A₀⟧)}, ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → ⊗ (a$0 ⟦aₙ$1⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦aₙ$1⟧)) → ⊕ (a$0 ⟦A₀⟧)}}. ⦅λ xₗ : ⊗ { }. ⦅λ xₐ : ⊗ ((λ a' : K. A₁ a'$0) ⟦aₚ$2⟧). ⦅E ⦅λ xₙₗ' : A₀. ⦅⦅π 0 xₙₗ'$0⦆ [λ a' : *. a'$0] xₐ$1⦆ ⦅⦅λ x : ⊗ {A₁}. x$0⦆ (⦅⦅E [aₗ$4] [aₜ$3] [aₚ$2] [aᵢ$1] [aₙ$0] xₙₗ$4⦆ xₙᵣ$3⦆ xₗ$2)⦆⦆⦆ xₙₗ$3⦆⦆⦆⦆⦆⦆ ⦅⦅⦅Λ a : * ↦ *. λ x : ⊗ (a$0 ⟦(λ a' : K. A₁ a'$0) ⟦{ }⟧⟧). x$0⦆ [λ a : *. a$0]⦆ ⦅⦅λ x : ⊗ { }. x$0⦆ ()⦆⦆]]
  apply «ind» Γ.typeVarDom Γ.typeVarDom ρke _ κe _ _ indce
  · intro a anin
    let Γawe := Γwe.typeExt anin κe.row
    simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open, Type.TypeVar_open]
    rw [μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id,
        A₁lc.weaken (n := 1).TypeVar_open_id]
    apply KindingAndElaboration.prod <| μke.weakening Γawe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
    apply KindingAndElaboration.lift (a :: Γ.typeVarDom) _ κe <| .var .head
    intro a' a'nin
    let Γaa'we := Γawe.typeExt a'nin κe
    simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open, Type.TypeVar_open]
    rw [ϕlc.TypeVar_open_id, A₁lc.TypeVar_open_id]
    exact .app (ϕke.weakening Γaa'we (Γ' := .typeExt (.typeExt .empty ..) ..) (Γ'' := .empty)) <|
      .var .head
  · intro aₗ aₗnin aₜ aₜnin aₚ aₚnin aᵢ aᵢnin aₙ aₙnin
    let Γawe := Γwe.typeExt aₗnin .label |>.typeExt aₜnin κe |>.typeExt aₚnin κe.row
      |>.typeExt aᵢnin κe.row |>.typeExt aₙnin κe.row
    simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open, «F⊗⊕ω».Term.TypeVar_open,
          Type.TypeVar_open]
    rw [μlc.TypeVar_open_id, μlc.TypeVar_open_id, ϕlc.weakening (n := 1).TypeVar_open_id,
        ϕlc.weakening (n := 1).TypeVar_open_id, Etlc.weaken (n := 4).TypeVar_open_id,
        Etlc.weaken (n := 3).TypeVar_open_id, Etlc.weaken (n := 2).TypeVar_open_id,
        Etlc.weaken (n := 1).TypeVar_open_id, Etlc.TypeVar_open_id,
        A₀lc.weaken (n := 5).TypeVar_open_id, A₀lc.weaken (n := 6).TypeVar_open_id,
        A₀lc.weaken (n := 4).TypeVar_open_id, A₀lc.weaken (n := 5).TypeVar_open_id,
        A₀lc.weaken (n := 3).TypeVar_open_id, A₀lc.weaken (n := 4).TypeVar_open_id,
        A₀lc.weaken (n := 2).TypeVar_open_id, A₀lc.weaken (n := 3).TypeVar_open_id,
        A₀lc.weaken (n := 1).TypeVar_open_id, A₀lc.weaken (n := 2).TypeVar_open_id,
        A₁lc.weaken (n := 5).TypeVar_open_id, A₁lc.weaken (n := 4).TypeVar_open_id,
        A₁lc.weaken (n := 3).TypeVar_open_id, A₁lc.weaken (n := 4).TypeVar_open_id,
        A₁lc.weaken (n := 2).TypeVar_open_id, A₁lc.weaken (n := 3).TypeVar_open_id,
        A₁lc.weaken (n := 1).TypeVar_open_id, A₁lc.weaken (n := 2).TypeVar_open_id,
        A₁lc.weaken (n := 1).TypeVar_open_id]
    apply qualI Γ.termVarDom <|
      .concat .comm (.var (.typeExt sorry (.typeExt sorry .head)))
        (.singleton_row
          (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
          (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
        (.var (.typeExt sorry .head)) κe
        (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head))) (.var (.typeExt sorry .head))
          κe)
        (.contain .comm
          (.singleton_row
            (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
            (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
          (.var (.typeExt sorry .head)) κe)
    intro xₙₗ xₙₗnin
    let Γaxₙₗwe := Γawe.constrExt xₙₗnin <|
      .concat (.comm (u := .non)) (.var (.typeExt sorry (.typeExt sorry .head)))
        (.singleton_row
          (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
          (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
        (.var (.typeExt sorry .head)) κe
        (.contain .comm (.var (.typeExt sorry (.typeExt sorry .head))) (.var (.typeExt sorry .head))
          κe)
        (.contain .comm
          (.singleton_row
            (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
            (.var (.typeExt sorry (.typeExt sorry (.typeExt sorry .head)))))
          (.var (.typeExt sorry .head)) κe)
    let ρke' := ρke.weakening Γaxₙₗwe (Γ'' := .empty) (Γ' := .constrExt (.typeExt (.typeExt
        (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..)
    simp [«F⊗⊕ω».Term.TermVar_open]
    rw [Elc.weaken (n := 4).TermVar_open_id]
    apply qualI (xₙₗ :: Γ.termVarDom) <|
      .concat .comm (.var (.constrExt (.typeExt sorry .head))) (.var (.constrExt .head))
        ρke' κe (.contain .comm (.var (.constrExt (.typeExt sorry .head))) ρke' κe)
        (.contain .comm (.var (.constrExt .head)) ρke' κe)
    intro xₙᵣ xₙᵣnin
    let Γaxₙₗᵣwe := Γaxₙₗwe.constrExt xₙᵣnin <|
      .concat (.comm (u := .non)) (.var (.constrExt (.typeExt sorry .head)))
        (.var (.constrExt .head)) ρke' κe
        (.contain .comm (.var (.constrExt (.typeExt sorry .head))) ρke' κe)
        (.contain .comm (.var (.constrExt .head)) ρke' κe)
    simp [«F⊗⊕ω».Term.TermVar_open]
    rw [Elc.weaken (n := 3).TermVar_open_id]
    apply lam (xₙᵣ :: xₙₗ :: Γ.termVarDom) _ <| .floor <| .var <| .constrExt <| .constrExt <|
      .typeExt sorry <| .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
    intro xₗ xₗnin
    let Γaxₙₗᵣxₗwe := Γaxₙₗᵣwe.termExt xₗnin <| .floor <| .var <| .constrExt <| .constrExt <|
      .typeExt sorry <| .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
    simp [Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open]
    rw [Mlc.weakening (n := 1).TermVar_open_id, Elc.weaken (n := 2).TermVar_open_id]
    let μke' := μke.weakening Γaxₙₗᵣxₗwe (Γ'' := .empty) (Γ' := .termExt (.constrExt (.constrExt
      (.typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..) ..) ..)
    apply lam (xₗ :: xₙᵣ :: xₙₗ :: Γ.termVarDom) _ <| .prod μke' <|
      .lift (aₙ :: aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom) (by
        intro a' a'nin
        let Γaxₙₗᵣxₗa'we := Γaxₙₗᵣxₗwe.typeExt a'nin κe
        simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open, «F⊗⊕ω».Term.TypeVar_open,
              Type.TypeVar_open]
        rw [ϕlc.TypeVar_open_id, A₁lc.TypeVar_open_id]
        exact ϕke.weakening Γaxₙₗᵣxₗa'we (Γ'' := .empty) (Γ' := .typeExt (.termExt (.constrExt
          (.constrExt (.typeExt (.typeExt (.typeExt (.typeExt (.typeExt
             .empty ..) ..) ..) ..) ..) ..) ..) ..) ..) |>.app <| .var .head
      ) κe <| .var <| .termExt <| .constrExt <| .constrExt <| .typeExt sorry <| .typeExt sorry .head
    intro xₐ xₐnin
    let Γaxₙₗᵣxₗₐwe := Γaxₙₗᵣxₗwe.termExt xₐnin <| .prod μke' <|
      .lift (aₙ :: aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom) (by
        intro a' a'nin
        show KindingAndElaboration _ _ (.qual (.mono (.TypeVar_open (ϕ.app (.var (.bound 0))) a')))
          _ (.TypeVar_open (A₁.app (.var (.bound 0))) a')
        let Γaxₙₗᵣxₗa'we := Γaxₙₗᵣxₗwe.typeExt a'nin κe
        simp [Monotype.TypeVar_open, TypeLambda.TypeVar_open, «F⊗⊕ω».Term.TypeVar_open,
              Type.TypeVar_open]
        rw [ϕlc.TypeVar_open_id, A₁lc.TypeVar_open_id]
        exact ϕke.weakening Γaxₙₗᵣxₗa'we (Γ'' := .empty) (Γ' := .typeExt (.termExt (.constrExt
          (.constrExt (.typeExt (.typeExt (.typeExt (.typeExt (.typeExt
             .empty ..) ..) ..) ..) ..) ..) ..) ..) ..) |>.app <| .var .head
      ) κe <| .var <| .termExt <| .constrExt <| .constrExt <| .typeExt sorry <| .typeExt sorry .head
    simp [Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open]
    rw [Mlc.TermVar_open_id, Elc.weaken (n := 1).TermVar_open_id]
    apply qualE <| .local <| .termExt sorry <| .termExt sorry <| .constrExt sorry .head
    apply sub _ (by
      show _
    ) (σ₀ := .qual
        (.qual
          (.concat
            (lift (.mk κ (ϕ.app (.var (.bound 0)))) (.var (.free aₚ))) μ
            (row [(.var (.free aₗ), ϕ.app (.var (.free aₜ)))] none)
            (lift (.mk κ (ϕ.app (.var (.bound 0)))) (.var (.free aᵢ))))
          (.mono (prodOrSum .prod μ (lift (.mk κ (ϕ.app (.var (.bound 0)))) (.var (.free aᵢ)))))))
    apply qualI (xₐ :: xₗ :: xₙᵣ :: xₙₗ :: Γ.termVarDom) sorry
    intro xₙₗ' xₙₗ'nin
    simp [«F⊗⊕ω».Term.TermVar_open]
    apply TypingAndElaboration.concat (.var (.constrExt sorry .head)) _ <| .local .head
    apply singleton_prod (.var (.constrExt sorry (.termExt sorry .head))) ?h (.var (.constrExt (.termExt (.termExt (.constrExt (.constrExt (.typeExt sorry (.typeExt sorry (.typeExt sorry (.typeExt sorry .head))))))))))
    case h =>
      apply TypingAndElaboration.app _ <| .var <| .constrExt sorry <| .termExt sorry .head
      let Mte' := Mte.weakening Γaxₙₗᵣxₗₐwe (Γ'' := .empty) (Γ' := .termExt (.termExt (.constrExt
        (.constrExt (.typeExt (.typeExt (.typeExt (.typeExt (.typeExt
          .empty ..) ..) ..) ..) ..) ..) ..) ..) ..)
      let Mte'' := Mte'.schemeE <| .var <| .termExt <| .termExt <| .constrExt <| .constrExt <|
        .typeExt sorry <| .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
      simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
            Monotype.Monotype_open] at Mte''
      let Mte''' := Mte''.schemeE <| .var <| .termExt <| .termExt <| .constrExt <| .constrExt <|
        .typeExt sorry <| .typeExt sorry <| .typeExt sorry .head
      simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
            Monotype.Monotype_open] at Mte'''
      let Mte'''' := Mte'''.schemeE <| .var <| .termExt <| .termExt <| .constrExt <| .constrExt <|
        .typeExt sorry <| .typeExt sorry .head
      simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
            Monotype.Monotype_open] at Mte''''
      let Mte''''' := Mte''''.schemeE <| .var <| .termExt <| .termExt <| .constrExt <|
        .constrExt <| .typeExt sorry .head
      simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
            Monotype.Monotype_open] at Mte'''''
      let Mte'''''' := Mte'''''.schemeE <| .var <| .termExt <| .termExt <| .constrExt <|
        .constrExt .head
      simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
            Monotype.Monotype_open] at Mte''''''
      rw [ρlc.weakening (n := 4).Monotype_open_id, ρlc.weakening (n := 3).Monotype_open_id,
          ρlc.weakening (n := 2).Monotype_open_id, ρlc.weakening (n := 1).Monotype_open_id,
          ρlc.Monotype_open_id, ϕlc.weakening (n := 4).Monotype_open_id,
          ϕlc.weakening (n := 3).Monotype_open_id, ϕlc.weakening (n := 2).Monotype_open_id,
          ϕlc.weakening (n := 1).Monotype_open_id, ϕlc.Monotype_open_id] at Mte''''''
      apply qualE (.local (.termExt sorry (.termExt sorry (.constrExt sorry .head)))) at Mte''''''
      apply qualE (.local (.termExt sorry (.termExt sorry .head))) at Mte''''''
      exact Mte''''''
  · simp [Monotype.Monotype_open, TypeLambda.Monotype_open]
    rw [μlc.Monotype_open_id, ϕlc.weakening (n := 1).Monotype_open_id]
    apply sub <| .unit μke
    apply SubtypingAndElaboration.prodRow _ <| .prod μke .empty_row
    swap
    let liftee := RowEquivalenceAndElaboration.liftR μ (.lift Γ.typeVarDom (by
      intro a' a'nin
      let Γa'we := Γwe.typeExt a'nin κe
      show KindingAndElaboration _ _ (.qual (.mono (.TypeVar_open (ϕ.app (.var (.bound 0))) a'))) _ (.TypeVar_open (A₁.app (.var (.bound 0))) a')
      simp [Monotype.TypeVar_open, Type.TypeVar_open]
      rw [ϕlc.TypeVar_open_id, A₁lc.TypeVar_open_id]
      exact ϕke.weakening Γa'we (Γ' := .typeExt .empty ..) (Γ'' := .empty) |>.app <| .var .head
    ) κe (by
      rw [Range.map_same_eq_nil, Option.someIf, if_pos rfl]
      exact .empty_row
      · exact fun _ => default
      · exact fun _ => default)) .star (n := 0) (Γc := Γc) (Γ := Γ)
    rw [Range.map_same_eq_nil, Range.map_same_eq_nil, Option.someIf, if_pos rfl, Option.someIf,
        if_pos rfl] at liftee
    exact liftee

-- theorem fold_emulation (ρke : [[Γc; Γ ⊢ ρ : R κ ⇝ A₀]]) (μke : [[Γc; Γ ⊢ μ : U ⇝ B]])
--   (τke : [[Γc; Γ ⊢ τ : * ⇝ A₁]])
--   (M₁te : [[Γᵢ; Γc; Γ ⊢ M₁ : ∀ aₗ : L. ∀ aₜ : *. ∀ aₚ : R *. ∀ aᵢ : R *. ∀ aₙ : R *. aₚ$2 ⊙(N) ⟨aₗ$4 ▹ aₜ$3⟩ ~ aᵢ$1 ⇒ aᵢ$1 ⊙(N) aₙ$0 ~ ρ ⇒ ⌊aₗ$4⌋ → aₜ$3 → τ ⇝ E₁]])
--   (M₂te : [[Γᵢ; Γc; Γ ⊢ M₂ : τ → τ → τ ⇝ E₂]]) (M₃te : [[Γᵢ; Γc; Γ ⊢ M₃ : τ ⇝ E₂]])
--   (Nty : [[Γᵢ; Γc; Γ ⊢ «N» : Π(μ) ρ ⇝ E₂]]) (indce : [[Γᵢ; Γc; Γ ⊨ Ind ρ ⇝ F]]) (Γᵢw : [[Γc ⊢ Γᵢ]])
--   (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
--   : ∃ F, [[Γᵢ; Γc; Γ ⊢ ind (λ a : R κ. τ) ρ; (λ xₗ. λ xₐ. (M₂ xₐ$0) ((M₁ xₗ$1) ((prj «N»)/xₗ$1))); M₃ : τ ⇝ F]] := sorry

end TabularTypeInterpreter
