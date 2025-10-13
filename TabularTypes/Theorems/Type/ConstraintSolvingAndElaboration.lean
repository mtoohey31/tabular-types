import TabularTypes.«F⊗⊕ω».Theorems
import TabularTypes.Lemmas.InstanceEnvironment
import TabularTypes.Lemmas.Type
import TabularTypes.Lemmas.TypeEnvironment
import TabularTypes.Semantics.Type.ConstraintSolvingAndElaboration
import TabularTypes.Theorems.Type.KindingAndElaboration

namespace TabularTypes

open «F⊗⊕ω»
open Std

namespace Monotype.ConstraintSolvingAndElaboration

theorem to_Kinding (ψce : [[Γᵢ; Γc; Γ ⊨ ψ ⇝ E]]) (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : ∃ A, [[Γc; Γ ⊢ ψ : C ⇝ A]] := by
  induction ψce generalizing Δ with
  | «local» ψinΓ => exact Γwe.KindingAndElaboration_of_ConstrIn ψinΓ
  | containTrans _ _ ρ₀ke ρ₂ke _ ρ₀₁ih _ =>
    let ⟨_, .contain μke ρ₀ke' ρ₁ke κe⟩ := ρ₀₁ih Γᵢw Γcw Γwe
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    exact ⟨_, .contain μke ρ₀ke ρ₂ke κe⟩
  | containConcat _ _ _ _ _ _ ρ₂ke ρ₅ke κe concat₂ih =>
    let ⟨_, concat₂ke⟩ := concat₂ih Γᵢw Γcw Γwe
    let .concat μke .. := concat₂ke
    exact ⟨_, .contain μke ρ₂ke ρ₅ke κe⟩
  | concatConcrete ξτke ξτ'ke ξττ'ke κe => exact ⟨
      _,
      .concat .comm ξτke ξτ'ke ξττ'ke κe (.contain .comm ξτke ξττ'ke κe)
        (.contain .comm ξτ'ke ξττ'ke κe)
    ⟩
  | concatEmptyL ρke κe => exact ⟨
      _,
      .concat .comm (.empty_row κe) ρke ρke κe (.contain .comm (.empty_row κe) ρke κe)
        (.contain .comm ρke ρke κe)
    ⟩
  | concatEmptyR ρke κe => exact ⟨
      _,
      .concat .comm ρke (.empty_row κe) ρke κe (.contain .comm ρke ρke κe)
        (.contain .comm (.empty_row κe) ρke κe)
    ⟩
  | concatAssocL _ _ _ _ _ ρ₂ke ρ₃ke ρ₅ke κe concat₀₁ih =>
    let ⟨_, .concat μke ..⟩ := concat₀₁ih Γᵢw Γcw Γwe
    exact ⟨_, .concat μke ρ₃ke ρ₂ke ρ₅ke κe (.contain μke ρ₃ke ρ₅ke κe) (.contain μke ρ₂ke ρ₅ke κe)⟩
  | concatAssocR _ _ _ ρ₀ke _ _ ρ₄ke ρ₅ke κe concat₀₁ih =>
    let ⟨_, .concat μke ..⟩ := concat₀₁ih Γᵢw Γcw Γwe
    exact ⟨_, .concat μke ρ₀ke ρ₄ke ρ₅ke κe (.contain μke ρ₀ke ρ₅ke κe) (.contain μke ρ₄ke ρ₅ke κe)⟩
  | concatSwap _ ρ₀ke ρ₁ke κe ih =>
    let ⟨_, .concat _ ρ₀ke' ρ₁ke' ρ₂ke κe' contain₀₂ke contain₁₂ke⟩ := ih Γᵢw Γcw Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨
      _,
      .concat .comm ρ₁ke ρ₀ke ρ₂ke κe (.contain .comm ρ₁ke ρ₂ke κe) (.contain .comm ρ₀ke ρ₂ke κe)
    ⟩
  | concatContainL _ ih =>
    let ⟨_, .concat μke ρ₀ke _ ρ₂ke κe ..⟩ := ih Γᵢw Γcw Γwe
    exact ⟨_, .contain μke ρ₀ke ρ₂ke κe⟩
  | concatContainR _ ih =>
    let ⟨_, .concat μke _ ρ₁ke ρ₂ke κe ..⟩ := ih Γᵢw Γcw Γwe
    exact ⟨_, .contain μke ρ₁ke ρ₂ke κe⟩
  | containDecay _ _ μ₁ke ih =>
    let ⟨_, .contain _ ρ₀ke ρ₁ke κe⟩ := ih Γᵢw Γcw Γwe
    exact ⟨_, .contain μ₁ke ρ₀ke ρ₁ke κe⟩
  | concatDecay _ _ μ₁ke ih =>
    let ⟨_, .concat _ ρ₀ke ρ₁ke ρ₂ke κe ..⟩ := ih Γᵢw Γcw Γwe
    exact ⟨
      _,
      .concat μ₁ke ρ₀ke ρ₁ke ρ₂ke κe (.contain μ₁ke ρ₀ke ρ₂ke κe) (.contain μ₁ke ρ₁ke ρ₂ke κe)
    ⟩
  | liftContain I _ ρ₀ke τke κ₀e κ₁e ih =>
    rename Kind => κ₁
    let ⟨_, .contain μke ρ₀ke' ρ₁ke _⟩ := ih Γᵢw Γcw Γwe
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    exact ⟨_, .contain μke (.lift I τke κ₀e ρ₀ke) (.lift I τke κ₀e ρ₁ke) κ₁e⟩
  | liftConcat I _ ρ₀ke τke κ₀e κ₁e ih =>
    rename Kind => κ₁
    let ⟨_, .concat μke ρ₀ke' ρ₁ke ρ₂ke ..⟩ := ih Γᵢw Γcw Γwe
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    let lift₀ := TypeScheme.KindingAndElaboration.lift I τke κ₀e ρ₀ke
    let lift₁ := TypeScheme.KindingAndElaboration.lift I τke κ₀e ρ₁ke
    let lift₂ := TypeScheme.KindingAndElaboration.lift I τke κ₀e ρ₂ke
    exact ⟨
      _,
      .concat μke lift₀ lift₁ lift₂ κ₁e (.contain μke lift₀ lift₂ κ₁e)
        (.contain μke lift₁ lift₂ κ₁e)
    ⟩
  | TCInst γᵢin τ'ke ψce ψih =>
    rename_i o κ' _ _ τ _ _ _ _ Γc Γ τ' B _ _
    let ⟨_, _, κ, _, _, A, _, B', _, γcin, _, τke, _⟩ := Γᵢw.In_inversion Γcw γᵢin
    suffices τopke : ∃ B, [[Γc; Γ ⊢ τ^^^^τ'@@k#o/a : κ ⇝ B]] by
      let ⟨_, τopke'⟩ := τopke
      exact ⟨_, .tc γcin τopke'⟩
    let ⟨a, ainj, anin⟩ := τ.freeTypeVars ++ ([:o].map (Monotype.freeTypeVars ∘ τ')).flatten ++
      ↑A.freeTypeVars ++ ↑B'.freeTypeVars ++ ↑([:o].map (Type.freeTypeVars ∘ B)).flatten ++
      Γ.typeVarDom |>.exists_fresh_inj
    let aninΓ i := List.not_mem_append'.mp (anin i) |>.right
    let aninττ'AB'B i := List.not_mem_append'.mp (anin i) |>.left
    let aninB i := List.not_mem_append'.mp (aninττ'AB'B i) |>.right
    let aninττ'AB' i := List.not_mem_append'.mp (aninττ'AB'B i) |>.left
    let aninB' i := List.not_mem_append'.mp (aninττ'AB' i) |>.right
    let aninττ'A i := List.not_mem_append'.mp (aninττ'AB' i) |>.left
    let aninA i := List.not_mem_append'.mp (aninττ'A i) |>.right
    let aninττ' i := List.not_mem_append'.mp (aninττ'A i) |>.left
    let aninτ' i := List.not_mem_append'.mp (aninττ' i) |>.right
    let aninτ i := List.not_mem_append'.mp (aninττ' i) |>.left
    let ⟨K₁, κ'e⟩ := Classical.skolem.mp (κ' · |>.Elaboration_total)
    let Γawe := Γwe.multiTypeExt aninΓ ainj (fun i _ => κ'e i) (n := o)
    let τke' := τke ⟨a, ainj⟩
    rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at τke'
    rw [← TypeEnvironment.empty_append (.multiTypeExt ..),
        ← TypeEnvironment.append_empty (.multiTypeExt ..), TypeEnvironment.multiTypeExt_eq_append,
        TypeEnvironment.append_empty] at Γawe
    let τke'' := τke' |>.weakening Γawe (Γ := .empty) (Γ' := Γ)
    rw [← TypeEnvironment.append_empty (.multiTypeExt ..), ← TypeEnvironment.multiTypeExt_eq_append,
        TypeEnvironment.append_empty, TypeEnvironment.empty_append] at τke''
    exact ⟨
      _,
      τke''.Monotype_multi_open Γcw Γwe (a := ⟨a, ainj⟩) (fun i _ => aninΓ i) (fun i _ => aninτ i)
        (by
          intro i mem j lt
          exact List.not_mem_flatten.mp (aninτ' i) _ <|
            Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
        ) (fun i _ => aninB' i) (by
          intro i mem j lt
          exact List.not_mem_flatten.mp (aninB i) _ <|
            Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
        ) τ'ke (Γ' := .empty)
    ⟩
  | TCSuper γcin _ mem ih =>
    rename_i TC' A' κ' _ _ _ Γc _ Γ _ _ i _ _
    let ⟨_, .tc γcin' τke⟩ := ih Γᵢw Γcw Γwe
    rcases ClassEnvironmentEntry.mk.inj <| γcin.deterministic γcin' rfl with ⟨_, _, rfl, _⟩
    let ⟨_, κ'e, _, _, TC'ke, _⟩ := Γcw.In_inversion γcin
    let ⟨a, anin⟩ := ↑(A' i).freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninA', aninΓ⟩ := List.not_mem_append'.mp anin
    let Γawe := Γwe.typeExt aninΓ κ'e
    rw [← Γ.empty_append] at Γawe
    let TC'ke' : TypeScheme.KindingAndElaboration Γc [[(ε, Γ, a : κ')]]
      (.TypeVar_open (.qual (.mono (.typeClass (TC' i) (.var (.bound 0))))) a) .constr
      [[(A'@i^a)]] := by
      rw [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, TypeVar_open, TypeVar_open,
          if_pos rfl]
      exact TC'ke a _ mem |>.weakening Γawe (Γ' := Γ) (Γ'' := .typeExt .empty ..)
    rw [TypeEnvironment.empty_append] at TC'ke' Γawe
    let TC'ke'' := TC'ke'.Monotype_open_preservation Γcw Γawe nofun (by
        rw [TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars, freeTypeVars]
        nofun
      ) aninA' τke (Γ' := .empty)
    rw [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open, Monotype_open,
        if_pos rfl] at TC'ke''
    exact ⟨_, TC'ke''⟩
  | allEmpty I ψke =>
    rename Kind => κ
    let ⟨_, κe⟩ := κ.Elaboration_total
    exact ⟨_, .all I ψke κe <| .empty_row κe⟩
  | allSingletonIntro I _ ψke ξke τke =>
    rename Kind => κ
    let ⟨_, κe⟩ := κ.Elaboration_total
    exact ⟨_, .all I ψke κe <| .singleton_row ξke τke⟩
  | allSingletonElim _ ih =>
    rename_i Γ _ ψ _ _ _ _
    let ⟨_, .all I ψke κe rowke (A := A)⟩ := ih Γᵢw Γcw Γwe
    let ⟨_, _, κeq, _, _, τke⟩ := rowke.singleton_row_inversion
    cases κeq
    let ⟨a, anin⟩ := I ++ ψ.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninIψA, aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninIψ, aninA⟩ := List.not_mem_append'.mp aninIψA
    let ⟨aninI, aninψ⟩ := List.not_mem_append'.mp aninIψ
    have := ψke a aninI
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at this
    exact ⟨
      _,
      this.Monotype_open_preservation Γcw (Γwe.typeExt aninΓ κe) nofun aninψ aninA τke
        (Γ' := .empty)
    ⟩
  | allContain I _ _ ψke κe containih allih =>
    let ⟨_, .contain μke ρ₀ke ρ₁ke _⟩ := containih Γᵢw Γcw Γwe
    let ⟨_, .all _ _ _ ρ₁ke'⟩ := allih Γᵢw Γcw Γwe
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨κeq, rfl⟩
    cases κeq
    exact ⟨_, .all I ψke κe ρ₀ke⟩
  | allConcat I _ _ _ ψke κe concatih all₀ih all₁ih =>
    let ⟨_, .concat μke ρ₀ke ρ₁ke ρ₂ke ..⟩ := concatih Γᵢw Γcw Γwe
    let ⟨_, .all _ _ _ ρ₀ke'⟩ := all₀ih Γᵢw Γcw Γwe
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    exact ⟨_, .all I ψke κe ρ₂ke⟩
  | ind I₀ I₁ τke κe keBₗ keBᵣ =>
    rename «Type» => Bᵣ
    let ⟨aᵢ, aᵢnin⟩ := I₁.exists_fresh
    let ⟨aₙ, aₙnin⟩ := aᵢ :: I₁ |>.exists_fresh
    let ⟨_, .concat _ _ _ ξτke ..⟩ := generalize <| keBᵣ _ aᵢnin _ aₙnin
    let ⟨_, uni, _, _, _, _, _, _, h, _⟩ := ξτke.row_inversion
    exact ⟨_, .ind I₀ I₁ (.row (fun _ _ => .label) uni τke κe h) κe keBₗ keBᵣ⟩
  | splitEmpty I τke =>
    rename Kind => κ
    let ⟨_, κe⟩ := κ.Elaboration_total
    let liftke := TypeScheme.KindingAndElaboration.lift I τke κe <| .empty_row κe
    exact ⟨
      _,
      .split <| .concat .comm liftke (.empty_row .star) (.empty_row .star) .star
        (.contain .comm liftke (.empty_row .star) .star)
        (.contain .comm (.empty_row .star) (.empty_row .star) .star)
    ⟩
  | splitSingletonMatch I τopke τ'ke ξke =>
    rename_i Γ κ τ A _ _ _ _
    let ⟨_, κe⟩ := κ.Elaboration_total
    let liftke := TypeScheme.KindingAndElaboration.lift I τopke κe <| ξke.singleton_row τ'ke
    let ⟨a, anin⟩ := I ++ τ.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninIτA, aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninIτ, aninA⟩ := List.not_mem_append'.mp aninIτA
    let ⟨aninI, aninτ⟩ := List.not_mem_append'.mp aninIτ
    let τopake := τopke a aninI
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at τopake
    let Γawe := Γwe.typeExt aninΓ κe
    let τopτ'ke :=
      τopake.Monotype_open_preservation Γcw Γawe nofun aninτ aninA τ'ke (Γ' := .empty)
    let ξτopτ'ke := ξke.singleton_row τopτ'ke
    exact .intro _ <| .split <| .concat .comm liftke (.empty_row .star) ξτopτ'ke .star
      (.contain .comm liftke ξτopτ'ke .star) (.contain .comm (.empty_row .star) ξτopτ'ke .star)
  | splitSingletonRest I _ τopke τ'ke ξke =>
    rename Kind => κ
    let ⟨_, κe⟩ := κ.Elaboration_total
    let liftke := TypeScheme.KindingAndElaboration.lift I τopke κe <| .empty_row κe
    let ξτ'ke := TypeScheme.KindingAndElaboration.singleton_row ξke τ'ke
    exact .intro _ <| .split <| .concat .comm liftke ξτ'ke ξτ'ke .star
      (.contain .comm liftke ξτ'ke .star) (.contain .comm ξτ'ke ξτ'ke .star)
  | splitPiecewise _ _ _ _ _ _ _ _ _ _ _ concatih =>
    let ⟨_, concatke⟩ := concatih Γᵢw Γcw Γwe
    exact ⟨_, .split concatke⟩
  | splitConcat _ ih =>
    let ⟨_, .split liftke⟩ := ih Γᵢw Γcw Γwe
    exact ⟨_, liftke⟩
where
  generalize {Γc Γ σ κ A} : [[Γc; Γ ⊢ σ : κ ⇝ A]] → ∃ B, [[Γc; Γ ⊢ σ : κ ⇝ B]] := (⟨_, ·⟩)

set_option maxHeartbeats 2000000 in
instance : Inhabited «Type» where
  default := .list [] none
in
theorem soundness (ψce : [[Γᵢ; Γc; Γ ⊨ ψ ⇝ E]]) (ψke : [[Γc; Γ ⊢ ψ : C ⇝ A]])
  (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : [[Δ ⊢ E : A]] := by
  induction ψce generalizing Δ A with
  | «local» ψinΓ => exact .var (Γwe.soundness Γcw) <| Γwe.ConstrIn_preservation ψinΓ ψke
  | containTrans contain₀₁ce contain₁₂ce ρ₀ke ρ₂ke κe contain₀₁ih contain₁₂ih =>
    rename_i A₀ A₂ K
    let .contain μke ρ₀ke' ρ₂ke' κe' := ψke
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨_, rfl⟩
    cases κeq
    cases κe.deterministic κe'
    apply Typing.pair
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp only [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
      apply Typing.lam Δ.termVarDom
      intro x xnin
      simp only [«F⊗⊕ω».Term.TermVar_open, if_pos]
      let ⟨_, .contain _ ρ₀ke'' ρ₁ke κe''⟩ := contain₀₁ce.to_Kinding Γᵢw Γcw Γwe
      rcases ρ₀ke.deterministic ρ₀ke'' with ⟨κeq, rfl⟩
      cases κeq
      cases κe.deterministic κe''
      let ⟨_, .contain _ ρ₁ke' ρ₂ke'' κe''⟩ := contain₁₂ce.to_Kinding Γᵢw Γcw Γwe
      rcases ρ₂ke.deterministic ρ₂ke'' with ⟨κeq, rfl⟩
      cases κeq
      cases κe.deterministic κe''
      let A₂ki := ρ₂ke.soundness Γcw Γwe κe.row
      let A₂lc := A₂ki.TypeVarLocallyClosed_of
      rw [A₂lc.TypeVar_open_id]
      let Δawf : [[⊢ Δ, a : K ↦ *]] := Γwe.soundness Γcw |>.typeVarExt anin
      let Δaxwf : [[⊢ Δ, a : K ↦ *, x : ⊗ (a ⟦A₂⟧)]] := Δawf.termVarExt xnin <| .prod <|
        .listApp (.var .head) <| A₂ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      apply Typing.app
      · let Ety := contain₀₁ih (.contain μke ρ₀ke ρ₁ke κe) Γᵢw Γcw Γwe
        rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id,
            Ety.TermVarLocallyClosed_of.TermVar_open_id]
        rw [← Range.map_get!_eq (as := [_, _])] at Ety
        let πty := Ety.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
        rw [List.get!_cons_zero] at πty
        simp only at πty
        have := πty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          |>.typeApp (B := .var a) <| .var <| .termVarExt .head
        simp [Type.Type_open] at this
        rw [← Type.TypeVar_open_eq_Type_open_var, ← Type.TypeVar_open_eq_Type_open_var] at this
        exact this
      · apply Typing.app
        · let Fty := contain₁₂ih (.contain μke ρ₁ke ρ₂ke κe) Γᵢw Γcw Γwe
          rw [Fty.TermTypeVarLocallyClosed_of.TypeVar_open_id,
              Fty.TermVarLocallyClosed_of.TermVar_open_id]
          rw [← Range.map_get!_eq (as := [_, _])] at Fty
          let πty := Fty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          rw [List.get!_cons_zero] at πty
          simp only at πty
          let A₁lc := ρ₁ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of
          rw [A₁lc.TypeVar_open_id]
          have := πty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
            |>.typeApp (B := .var a) <| .var <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [← Type.TypeVar_open_eq_Type_open_var, ← Type.TypeVar_open_eq_Type_open_var,
              A₁lc.TypeVar_open_id] at this
          exact this
        · rw [A₂lc.TypeVar_open_id]
          exact .var Δaxwf .head
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp only [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
      apply Typing.lam Δ.termVarDom
      intro x xnin
      simp only [«F⊗⊕ω».Term.TermVar_open, if_pos]
      let ⟨_, .contain _ ρ₀ke'' ρ₁ke κe''⟩ := contain₀₁ce.to_Kinding Γᵢw Γcw Γwe
      rcases ρ₀ke.deterministic ρ₀ke'' with ⟨κeq, rfl⟩
      cases κeq
      cases κe.deterministic κe''
      let ⟨_, .contain _ ρ₁ke' ρ₂ke'' κe''⟩ := contain₁₂ce.to_Kinding Γᵢw Γcw Γwe
      rcases ρ₂ke.deterministic ρ₂ke'' with ⟨κeq, rfl⟩
      cases κeq
      cases κe.deterministic κe''
      let A₀ki := ρ₀ke.soundness Γcw Γwe κe.row
      let A₀lc := A₀ki.TypeVarLocallyClosed_of
      rw [A₀lc.TypeVar_open_id]
      let Δawf : [[⊢ Δ, a : K ↦ *]] := Γwe.soundness Γcw |>.typeVarExt anin
      let Δaxwf : [[⊢ Δ, a : K ↦ *, x : ⊕ (a ⟦A₀⟧)]] := Δawf.termVarExt xnin <| .sum <|
        .listApp (.var .head) <| A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      apply Typing.app
      · let Fty := contain₁₂ih (.contain μke ρ₁ke ρ₂ke κe) Γᵢw Γcw Γwe
        rw [Fty.TermTypeVarLocallyClosed_of.TypeVar_open_id,
            Fty.TermVarLocallyClosed_of.TermVar_open_id]
        rw [← Range.map_get!_eq (as := [_, _])] at Fty
        let πty := Fty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
        rw [List.get!_cons_succ, List.get!_cons_zero] at πty
        simp only at πty
        have := πty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          |>.typeApp (B := .var a) <| .var <| .termVarExt .head
        simp [Type.Type_open] at this
        rw [← Type.TypeVar_open_eq_Type_open_var, ← Type.TypeVar_open_eq_Type_open_var] at this
        exact this
      · apply Typing.app
        · let Ety := contain₀₁ih (.contain μke ρ₀ke ρ₁ke κe) Γᵢw Γcw Γwe
          rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id,
              Ety.TermVarLocallyClosed_of.TermVar_open_id]
          rw [← Range.map_get!_eq (as := [_, _])] at Ety
          let πty := Ety.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          rw [List.get!_cons_succ, List.get!_cons_zero] at πty
          simp only at πty
          let A₁lc := ρ₁ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of
          rw [A₁lc.TypeVar_open_id]
          have := πty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
            |>.typeApp (B := .var a) <| .var <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [← Type.TypeVar_open_eq_Type_open_var, ← Type.TypeVar_open_eq_Type_open_var,
              A₁lc.TypeVar_open_id] at this
          exact this
        · rw [A₀lc.TypeVar_open_id]
          exact .var Δaxwf .head
  | containConcat _ concat₅ce _ _ ρ₀ke ρ₁ke ρ₂ke ρ₅ke κe concat₂ih concat₅ih containₗih containᵣih =>
    rename «F⊗⊕ω».Kind => K
    let .contain μke ρ₂ke' ρ₅ke' κe' := ψke
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₅ke.deterministic ρ₅ke' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe'
    let ⟨_, concat₅ke⟩ := concat₅ce.to_Kinding Γᵢw Γcw Γwe
    let .concat _ ρ₃ke ρ₄ke ρ₅ke' κe' .. := concat₅ke
    rcases ρ₅ke.deterministic ρ₅ke' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe'
    let E₂ty := concat₂ih
      (.concat μke ρ₀ke ρ₁ke ρ₂ke κe (.contain μke ρ₀ke ρ₂ke κe) (.contain μke ρ₁ke ρ₂ke κe)) Γᵢw
      Γcw Γwe
    let E₂tlc := E₂ty.TermTypeVarLocallyClosed_of
    let E₂lc := E₂ty.TermVarLocallyClosed_of
    let E₅ty := concat₅ih
      (.concat μke ρ₃ke ρ₄ke ρ₅ke κe (.contain μke ρ₃ke ρ₅ke κe) (.contain μke ρ₄ke ρ₅ke κe)) Γᵢw
      Γcw Γwe
    let E₅tlc := E₅ty.TermTypeVarLocallyClosed_of
    let E₅lc := E₅ty.TermVarLocallyClosed_of
    let Fₗty := containₗih (.contain μke ρ₀ke ρ₃ke κe) Γᵢw Γcw Γwe
    let Fₗtlc := Fₗty.TermTypeVarLocallyClosed_of
    let Fₗlc := Fₗty.TermVarLocallyClosed_of
    let Fᵣty := containᵣih (.contain μke ρ₁ke ρ₄ke κe) Γᵢw Γcw Γwe
    let Fᵣtlc := Fᵣty.TermTypeVarLocallyClosed_of
    let Fᵣlc := Fᵣty.TermVarLocallyClosed_of
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at E₂ty E₅ty
    rw [← Range.map_get!_eq (as := [_, _])] at Fₗty Fᵣty
    let A₀ki := ρ₀ke.soundness Γcw Γwe κe.row
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    let A₁ki := ρ₁ke.soundness Γcw Γwe κe.row
    let A₁lc := A₁ki.TypeVarLocallyClosed_of
    let A₂lc := ρ₂ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of
    let A₃lc := ρ₃ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of
    let A₄lc := ρ₄ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of
    let A₅ki := ρ₅ke.soundness Γcw Γwe κe.row
    let A₅lc := A₅ki.TypeVarLocallyClosed_of
    let Δwf := Γwe.soundness Γcw
    apply Typing.pair
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₂lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₂tlc.TypeVar_open_id, E₅tlc.TypeVar_open_id,
          Fₗtlc.TypeVar_open_id, Fᵣtlc.TypeVar_open_id]
      apply Typing.lam Δ.termVarDom
      intro x xnin
      let A₅ki' := A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      let Δaxwf := Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) A₅ki'
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₂lc.TermVar_open_id, E₅lc.TermVar_open_id, Fₗlc.TermVar_open_id, Fᵣlc.TermVar_open_id]
      apply Typing.app
      · apply Typing.app
        · let πty := E₂ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          let πty' := πty.typeApp <| .var <| .termVarExt .head
          simp [Type.Type_open] at πty'
          rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at πty'
          exact πty'
        · apply Typing.app
          · let πty := Fₗty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
              |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
            simp at πty
            let πty' := πty.typeApp <| .var <| .termVarExt .head
            simp [Type.Type_open] at πty'
            rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at πty'
            exact πty'
          · apply Typing.app _ <| .var Δaxwf .head
            let πty := E₅ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let πty' := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            simp at πty'
            let πty'' := πty'.typeApp <| .var <| .termVarExt .head
            simp [Type.Type_open] at πty''
            rw [A₃lc.Type_open_id, A₅lc.Type_open_id] at πty''
            exact πty''
      · apply Typing.app
        · let πty := Fᵣty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          let πty' := πty.typeApp <| .var <| .termVarExt .head
          simp [Type.Type_open] at πty'
          rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at πty'
          exact πty'
        · apply Typing.app _ <| .var Δaxwf .head
          let πty := E₅ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let πty' := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          simp at πty'
          let πty'' := πty'.typeApp <| .var <| .termVarExt .head
          simp [Type.Type_open] at πty''
          rw [A₄lc.Type_open_id, A₅lc.Type_open_id] at πty''
          exact πty''
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id, A₂lc.TypeVar_open_id, A₅lc.TypeVar_open_id,
          E₂tlc.TypeVar_open_id, E₅tlc.TypeVar_open_id, Fₗtlc.TypeVar_open_id, Fᵣtlc.TypeVar_open_id]
      apply Typing.app
      · apply Typing.app
        · let πty := E₂ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          simp at πty
          let πty' := πty.typeApp <| .var <| .head
          simp [Type.Type_open] at πty'
          rw [A₀lc.weaken (n := 1).Type_open_id, A₁lc.weaken (n := 1).Type_open_id,
              A₂lc.weaken (n := 1).Type_open_id] at πty'
          let A₅ki' := A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          let πty'' := πty'.typeApp <| .sum <| .listApp (.var .head) A₅ki'
          simp [Type.Type_open] at πty''
          rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at πty''
          exact πty''
        · apply Typing.lam Δ.termVarDom
          intro x xnin
          let A₀ki' := A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) A₀ki'
          simp [«F⊗⊕ω».Term.TermVar_open]
          rw [E₅lc.TermVar_open_id, Fₗlc.TermVar_open_id]
          apply Typing.app
          · let πty := E₅ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let πty' := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            simp at πty'
            let πty'' := πty'.typeApp <| .var <| .termVarExt .head
            simp [Type.Type_open] at πty''
            rw [A₃lc.Type_open_id, A₅lc.Type_open_id] at πty''
            exact πty''
          · apply Typing.app _ <| .var Δaxwf .head
            let πty := Fₗty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
              |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
            simp at πty
            let πty' := πty.typeApp <| .var <| .termVarExt .head
            simp [Type.Type_open] at πty'
            rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at πty'
            exact πty'
      · apply Typing.lam Δ.termVarDom
        intro x xnin
        let A₁ki' := A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) A₁ki'
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₅lc.TermVar_open_id, Fᵣlc.TermVar_open_id]
        apply Typing.app
        · let πty := E₅ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let πty' := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          simp at πty'
          let πty'' := πty'.typeApp <| .var <| .termVarExt .head
          simp [Type.Type_open] at πty''
          rw [A₄lc.Type_open_id, A₅lc.Type_open_id] at πty''
          exact πty''
        · apply Typing.app _ <| .var Δaxwf .head
          let πty := Fᵣty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          let πty' := πty.typeApp <| .var <| .termVarExt .head
          simp [Type.Type_open] at πty'
          rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at πty'
          exact πty'
  | concatConcrete ξτke ξτ'ke ξττ'ke κe τke τ'ke =>
    rename_i m ξ τ _ _ A₀ n ξ' τ' _ A₁ A₂ K B B' _
    let .concat _ ξτke' ξτ'ke' ξττ'ke' κe' contain₀ke contain₁ke := ψke
    let .contain _ ξτke'' ξττ'ke'' κe'' := contain₀ke
    let .contain _ ξτ'ke'' ξττ'ke''' κe''' := contain₁ke
    rcases ξτke.deterministic ξτke' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe'
    rcases ξτke.deterministic ξτke'' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe''
    rcases ξτ'ke.deterministic ξτ'ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ξτ'ke.deterministic ξτ'ke'' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe'''
    let ξξ' i := if i < m then ξ i else ξ' (i - m)
    let ττ' i := if i < m then τ i else τ' (i - m)
    rw (occs := .pos [2]) [Range.map_shift' (j := m)] at ξττ'ke ξττ'ke' ξττ'ke'' ξττ'ke'''
    rw [Nat.zero_add, Nat.add_comm, Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = (ξξ' i, ττ' i)
        dsimp [ξξ', ττ']
        rw [if_pos mem.upper, if_pos mem.upper]
      ), Range.map_eq_of_eq_of_mem'' (m := m) (by
        intro i mem
        show _ = (ξξ' i, ττ' i)
        dsimp [ξξ', ττ']
        rw [if_neg <| Nat.not_lt_of_le mem.lower, if_neg <| Nat.not_lt_of_le mem.lower]
      ), Range.map, Range.map,
      Range.map_append (l := 0) (m := m) (n := m + n) (Nat.zero_le _) (Nat.le_add_right ..),
      ← Range.map] at ξττ'ke ξττ'ke' ξττ'ke'' ξττ'ke'''
    rcases ξττ'ke.deterministic ξττ'ke' with ⟨_, rfl⟩
    rcases ξττ'ke.deterministic ξττ'ke'' with ⟨_, rfl⟩
    rcases ξττ'ke.deterministic ξττ'ke''' with ⟨_, rfl⟩
    rcases ξτke.row_inversion with ⟨_, _, A₀', _, _, A₀eq, κeq, κe', h₀, _, τke'⟩
    cases κeq
    rcases ξτ'ke.row_inversion with ⟨_, _, A₁', _, _, A₁eq, κeq, κe'', h₁, _, τ'ke'⟩
    cases κeq
    rcases ξττ'ke.row_inversion with ⟨_, _, A₂', _, _, A₂eq, κeq, κe''', _, _, ττ'ke'⟩
    cases κeq
    cases κe.deterministic κe'
    cases κe.deterministic κe''
    cases κe.deterministic κe'''
    let Δwf := Γwe.soundness Γcw
    let A₀ki := ξτke.soundness Γcw Γwe κe.row
    let A₁ki := ξτ'ke.soundness Γcw Γwe κe.row
    let A₂ki := ξττ'ke.soundness Γcw Γwe κe.row
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open, if_pos]
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open, if_pos]
      rw [← Range.map, ← Range.map, A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id,
          A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id,
          A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      let xne := List.ne_of_not_mem_cons xᵣnin
      let Δawf : [[⊢ Δ, a : K ↦ *]] := Δwf.typeVarExt anin
      let Δaxₗwf : [[⊢ Δ, a : K ↦ *, xₗ : ⊗ (a ⟦A₀⟧)]] := Δawf.termVarExt xₗnin <| .prod <|
        .listApp (.var .head) <| A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      let Δaxₗᵣwf : [[⊢ Δ, a : K ↦ *, xₗ : ⊗ (a ⟦A₀⟧), xᵣ : ⊗ (a ⟦A₁⟧)]] := Δaxₗwf.termVarExt xᵣnin <|
        .prod <| .listApp (.var (.termVarExt .head)) <| A₁ki.weakening Δaxₗwf
        (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
      cases A₂eq
      apply Typing.equiv _ <| .prod <| .symm <| .listAppList <| .var <| .termVarExt <|
        .termVarExt .head
      rw [Range.map_eq_of_eq_of_mem'' (by
        intro _ _
        rw [Function.comp, Function.comp, Function.comp, «F⊗⊕ω».Term.TypeVar_open,
            «F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open,
            if_pos rfl, «F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open, if_neg nofun]
      ), Range.map_eq_of_eq_of_mem'' (n := n) (by
        intro _ _
        rw [Function.comp, Function.comp, Function.comp, «F⊗⊕ω».Term.TypeVar_open,
            «F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open,
            if_neg nofun, «F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open, if_pos rfl]
      )]
      apply Typing.prodIntro' Δaxₗᵣwf _ (by
        rw [List.length_append, List.length_map, List.length_map, Range.length_toList,
            Range.length_toList, Nat.sub_zero, Nat.sub_zero]
        match h₀, h₁ with
        | .inl ne, _ =>
          exact .inl <| Nat.pos_iff_ne_zero.mp <| Nat.lt_add_right _ <| Nat.pos_of_ne_zero ne
        | _, .inl ne =>
          exact .inl <| Nat.pos_iff_ne_zero.mp <| Nat.lt_add_left _ <| Nat.pos_of_ne_zero ne
        | .inr b₀eq, .inr b₁eq =>
          right
          rw [b₀eq, b₁eq, Bool.and]
      ) <| by
        rw [List.length_map, List.length_append, List.length_map, List.length_map,
            Range.length_toList, Range.length_toList, Range.length_toList, Nat.sub_zero,
            Nat.sub_zero, Nat.sub_zero]
      intro EA mem
      rw [Range.map_shift' (j := m) (n := n), Nat.zero_add, Nat.add_comm] at mem
      match Range.mem_zip_map_append (Nat.zero_le _) (Nat.le_add_right _ _) mem with
      | .inl ⟨i, imem, eq⟩ =>
        cases eq
        cases A₀eq
        simp only
        let τike := τke' i imem
        let ττ'ike := ττ'ke' i ⟨imem.lower, Nat.lt_add_right n imem.upper, imem.step⟩
        dsimp [ττ'] at ττ'ike
        rw [if_pos imem.upper] at ττ'ike
        rw [ττ'ike.deterministic τike |>.right]
        exact .prodElim (.equiv (.var Δaxₗᵣwf (.termVarExt .head xne.symm)) <| .prod <|
          .listAppList <| .var <| .termVarExt <| .termVarExt .head) imem
      | .inr ⟨j, jmem, eq⟩ =>
        cases eq
        cases A₁eq
        simp only
        let i := j - m
        let imem : i ∈ [:n] := ⟨
          Nat.zero_le _,
          by
            dsimp [i]
            apply Nat.sub_lt_right_of_lt_add jmem.lower
            rw [Nat.add_comm]
            exact jmem.upper,
          Nat.mod_one _
        ⟩
        let τ'ike := τ'ke' i imem
        let ττ'ike := ττ'ke' j ⟨Nat.zero_le _, jmem.upper, Nat.mod_one _⟩
        dsimp [ττ'] at ττ'ike
        rw [if_neg <| Nat.not_lt_of_le jmem.lower] at ττ'ike
        rw [ττ'ike.deterministic τ'ike |>.right]
        exact .prodElim (.equiv (.var Δaxₗᵣwf .head) <| .prod <| .listAppList <| .var <|
          .termVarExt <| .termVarExt .head) imem
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let ane := List.ne_of_not_mem_cons aₜnin
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let xₗnexᵣ := List.ne_of_not_mem_cons xᵣnin
      symm at xₗnexᵣ
      apply Typing.lam <| xᵣ :: xₗ :: Δ.termVarDom
      intro x xnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let xₗnex := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xnin
      symm at xₗnex
      let xᵣnex := List.ne_of_not_mem_cons xnin
      symm at xᵣnex
      let F i := if i < m then
          [[λ x : a B@i. xₗ ⦅ι i x$0⦆]]
        else
          let j := i - m
          [[λ x : a B'@j. xᵣ ⦅ι j x$0⦆]]
      rw [← Range.map, ← Range.map, Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = F i
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, «F⊗⊕ω».Term.TermVar_open, F]
        let Bilc := τke _ mem |>.soundness Γcw Γwe κe |>.TypeVarLocallyClosed_of
        rw [Bilc.weaken (n := 1).TypeVar_open_id, Bilc.TypeVar_open_id, if_pos mem.upper]
      ), Range.map_eq_of_eq_of_mem'' (n := n) (by
        intro i mem
        show _ = F (i + m)
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, «F⊗⊕ω».Term.TermVar_open, F]
        let B'ilc := τ'ke _ mem |>.soundness Γcw Γwe κe |>.TypeVarLocallyClosed_of
        rw [B'ilc.weaken (n := 1).TypeVar_open_id, B'ilc.TypeVar_open_id]
      ), Range.map_shift' (n := n) (j := m), Nat.zero_add, Nat.add_comm,
      Range.map_eq_of_eq_of_mem'' (n := m + n) (by
        intro i mem
        rw [Nat.sub_add_cancel mem.lower]
      ), Range.map_append (Nat.zero_le _) (Nat.le_add_right _ _), ← Range.map]
      let A₀lc := A₀ki.TypeVarLocallyClosed_of
      let A₁lc := A₁ki.TypeVarLocallyClosed_of
      let A₂lc := A₂ki.TypeVarLocallyClosed_of
      rw [A₀lc.weaken (n := 1).TypeVar_open_id, A₀lc.TypeVar_open_id,
          A₁lc.weaken (n := 1).TypeVar_open_id, A₁lc.TypeVar_open_id,
          A₂lc.weaken (n := 1).TypeVar_open_id, A₂lc.TypeVar_open_id]
      let Δawf : [[⊢ Δ, a : K ↦ *]] := Δwf.typeVarExt anin
      let Δaaₜwf : [[⊢ Δ, a : K ↦ *, aₜ : *]] := Δawf.typeVarExt aₜnin
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr
        (.sum (.listApp (.var (.typeVarExt .head ane.symm))
          (A₀ki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty))))
        <| .var .head
      let Δaaₜxₗxᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr
        (.sum (.listApp (.var (.termVarExt (.typeVarExt .head ane.symm)))
          (A₁ki.weakening Δaaₜxₗwf (Δ' := .termExt (.typeExt (.typeExt .empty ..) ..) ..)
            (Δ'' := .empty))))
        <| .var <| .termVarExt .head
      let Δaaₜxₗxᵣxwf := Δaaₜxₗxᵣwf.termVarExt xnin <| .sum <|
        .listApp (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm))))
          (A₂ki.weakening Δaaₜxₗxᵣwf
            (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) (Δ'' := .empty))
      cases A₂eq
      apply Typing.sumElim (.equiv (.var Δaaₜxₗxᵣxwf .head) <| .sum <| .listAppList <| .var <|
        .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head ane.symm) _ <|
        .var <| .termVarExt <| .termVarExt <| .termVarExt .head
      intro i mem
      dsimp [F]
      split
      · case isTrue h =>
        let mem' : i ∈ [:m] := ⟨mem.lower, h, Nat.mod_one _⟩
        let τike := τke i mem'
        let ττ'ike := ττ'ke' i mem
        dsimp [ττ'] at ττ'ike
        rw [if_pos h] at ττ'ike
        rw [τike.deterministic ττ'ike |>.right]
        apply Typing.lam <| x :: xᵣ :: xₗ :: Δ.termVarDom
        intro x' x'nin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let xₗnex' := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
          List.not_mem_of_not_mem_cons x'nin
        symm at xₗnex'
        let Δaaₜxₗxᵣxxwf := Δaaₜxₗxᵣxwf.termVarExt x'nin <| .app
          (.var (.termVarExt (.termVarExt (.termVarExt (.typeVarExt .head ane.symm))))) <|
          ττ'ike.soundness Γcw Γwe κe |>.weakening Δaaₜxₗxᵣxwf
            (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
            (Δ'' := .empty)
        apply Typing.app <| .var Δaaₜxₗxᵣxxwf
          (.termVarExt (.termVarExt (.termVarExt .head xₗnexᵣ) xₗnex) xₗnex')
        cases A₀eq
        apply Typing.equiv _ <| .sum <| .symm <| .listAppList <| .var <| .termVarExt <|
          .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head ane.symm
        let τike' := τke' i mem'
        rw [← τike'.deterministic ττ'ike |>.right] at Δaaₜxₗxᵣxxwf ⊢
        apply Typing.sumIntro mem' (.var Δaaₜxₗxᵣxxwf .head) _ h₀
        intro j mem''
        apply Kinding.app <| .var <| .termVarExt <| .termVarExt <| .termVarExt <| .termVarExt <|
          .typeVarExt .head ane.symm
        exact τke' j mem'' |>.soundness Γcw Γwe κe |>.weakening Δaaₜxₗxᵣxxwf
          (Δ' := .termExt
            (.termExt (.termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..)
          (Δ'' := .empty)
      · case isFalse h =>
        let mem' : i - m ∈ [:n] := ⟨
          Nat.zero_le _,
          Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) mem.upper,
          Nat.mod_one _
        ⟩
        let τ'ike := τ'ke (i - m) mem'
        let ττ'ike := ττ'ke' i mem
        dsimp [ττ'] at ττ'ike
        rw [if_neg h] at ττ'ike
        rw [τ'ike.deterministic ττ'ike |>.right]
        apply Typing.lam <| x :: xᵣ :: xₗ :: Δ.termVarDom
        intro x' x'nin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let xᵣnex' := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons x'nin
        symm at xᵣnex'
        let Δaaₜxₗxᵣxxwf := Δaaₜxₗxᵣxwf.termVarExt x'nin <| .app
          (.var (.termVarExt (.termVarExt (.termVarExt (.typeVarExt .head ane.symm))))) <|
          ττ'ike.soundness Γcw Γwe κe |>.weakening Δaaₜxₗxᵣxwf
            (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
            (Δ'' := .empty)
        apply Typing.app <| .var Δaaₜxₗxᵣxxwf (.termVarExt (.termVarExt .head xᵣnex) xᵣnex')
        cases A₁eq
        apply Typing.equiv _ <| .sum <| .symm <| .listAppList <| .var <| .termVarExt <|
          .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head ane.symm
        let τ'ike' := τ'ke' (i - m) mem'
        rw [← τ'ike'.deterministic ττ'ike |>.right] at Δaaₜxₗxᵣxxwf ⊢
        apply Typing.sumIntro mem' (.var Δaaₜxₗxᵣxxwf .head) _ h₁
        intro j mem''
        apply Kinding.app <| .var <| .termVarExt <| .termVarExt <| .termVarExt <| .termVarExt <|
          .typeVarExt .head ane.symm
        exact τ'ke' j mem'' |>.soundness Γcw Γwe κe |>.weakening Δaaₜxₗxᵣxxwf
          (Δ' := .termExt
            (.termExt (.termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..) ..)
          (Δ'' := .empty)
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id,
            A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δawf : [[⊢ Δ, a : K ↦ *]] := Δwf.typeVarExt anin
        let Δaxwf : [[⊢ Δ, a : K ↦ *, x : ⊗ (a ⟦A₂⟧)]] := Δawf.termVarExt xnin <| .prod <|
          .listApp (.var .head) <| A₂ki.weakening Δawf (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
        cases A₀eq
        rw [← Range.map, Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          rw [Function.comp, Function.comp, «F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TypeVar_open,
              «F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open, if_pos rfl]
        )]
        apply Typing.equiv _ <| .prod <| .symm <| .listAppList <| .var <| .termVarExt .head
        apply Typing.prodIntro Δaxwf _ h₀
        intro i mem
        let τike := τke' i mem
        let ττ'ike := ττ'ke' i ⟨mem.lower, Nat.lt_add_right n mem.upper, mem.step⟩
        dsimp [ττ'] at ττ'ike
        rw [if_pos mem.upper] at ττ'ike
        rw [τike.deterministic ττ'ike |>.right]
        apply Typing.prodElim (n := m + n) _ ⟨mem.lower, Nat.lt_add_right n mem.upper, mem.step⟩
        swap
        cases A₂eq
        exact .equiv (.var Δaxwf .head) <| .prod <| .listAppList <| .var <| .termVarExt .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id,
            A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δawf : [[⊢ Δ, a : K ↦ *]] := Δwf.typeVarExt anin
        let Δaxwf : [[⊢ Δ, a : K ↦ *, x : ⊕ (a ⟦A₀⟧)]] := Δawf.termVarExt xnin <| .sum <|
          .listApp (.var .head) <| A₀ki.weakening Δawf (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
        cases A₀eq
        apply Typing.sumElim (.equiv (.var Δaxwf .head)
          (.sum <| .listAppList <| .var <| .termVarExt .head)) _ <|
          .sum <| .listApp (.var (.termVarExt .head)) <| ξττ'ke.soundness Γcw Γwe κe.row
            |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
        intro i mem
        simp [Function.comp, «F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open,
              «F⊗⊕ω».Term.TermVar_open]
        let τike := τke i mem
        let τike' := τke' i mem
        rw [τike.deterministic τike' |>.right,
            τike'.soundness Γcw Γwe κe |>.TypeVarLocallyClosed_of.TypeVar_open_id]
        apply Typing.lam <| x :: Δ.termVarDom
        intro x xnin
        rw [«F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open, if_pos rfl]
        let mem' : i ∈ [:m + n] := ⟨mem.lower, Nat.lt_add_right n mem.upper, mem.step⟩
        let ττ'ike := ττ'ke' i mem'
        dsimp [ττ'] at ττ'ike
        rw [if_pos mem.upper] at ττ'ike
        rw [τike'.deterministic ττ'ike |>.right]
        let Δaxxwf := Δaxwf.termVarExt xnin <| .app (.var (.termVarExt .head)) <|
          ττ'ike.soundness Γcw Γwe κe |>.weakening Δaxwf
          (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
        cases A₂eq
        apply Typing.equiv _ <| .sum <| .symm <| .listAppList <| .var <| .termVarExt <|
          .termVarExt .head
        apply Typing.sumIntro mem' (.var Δaxxwf .head) _ <| by
          match h₀, h₁ with
          | .inl ne, _ =>
            exact .inl <| Nat.pos_iff_ne_zero.mp <| Nat.lt_add_right _ <| Nat.pos_of_ne_zero ne
          | _, .inl ne =>
            exact .inl <| Nat.pos_iff_ne_zero.mp <| Nat.lt_add_left _ <| Nat.pos_of_ne_zero ne
          | .inr b₀eq, .inr b₁eq =>
            right
            rw [BoolId, id, b₀eq, b₁eq, Bool.and]
        intro j mem''
        exact .app (.var (.termVarExt (.termVarExt .head))) <|
          ττ'ke' j mem'' |>.soundness Γcw Γwe κe |>.weakening Δaxxwf
          (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id,
            A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δawf : [[⊢ Δ, a : K ↦ *]] := Δwf.typeVarExt anin
        let Δaxwf : [[⊢ Δ, a : K ↦ *, x : ⊗ (a ⟦A₂⟧)]] := Δawf.termVarExt xnin <| .prod <|
          .listApp (.var .head) <| A₂ki.weakening Δawf (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
        cases A₁eq
        rw [← Range.map, Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          rw [Function.comp, Function.comp, «F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TypeVar_open,
              «F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open, if_pos rfl]
        )]
        apply Typing.equiv _ <| .prod <| .symm <| .listAppList <| .var <| .termVarExt .head
        apply Typing.prodIntro Δaxwf _ h₁
        intro i mem
        let τ'ike := τ'ke' i mem
        let ττ'ike := ττ'ke' (m + i) ⟨
          Nat.zero_le _,
          Nat.add_lt_add_left mem.upper _,
          Nat.mod_one _
        ⟩
        dsimp [ττ'] at ττ'ike
        rw [if_neg <| Nat.not_lt_of_le <| Nat.le_add_right .., Nat.add_comm,
            Nat.add_sub_cancel, Nat.add_comm] at ττ'ike
        rw [τ'ike.deterministic ττ'ike |>.right]
        generalize jeq : m + i = j
        apply Typing.prodElim (n := m + n) _ ⟨
          Nat.zero_le _,
          by rw [← jeq]; exact Nat.add_lt_add_left mem.upper _,
          Nat.mod_one _
        ⟩
        swap
        cases A₂eq
        exact .equiv (.var Δaxwf .head) <| .prod <| .listAppList <| .var <| .termVarExt .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id,
            A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δawf : [[⊢ Δ, a : K ↦ *]] := Δwf.typeVarExt anin
        let Δaxwf : [[⊢ Δ, a : K ↦ *, x : ⊕ (a ⟦A₁⟧)]] := Δawf.termVarExt xnin <| .sum <|
          .listApp (.var .head) <| A₁ki.weakening Δawf (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
        cases A₁eq
        apply Typing.sumElim (.equiv (.var Δaxwf .head)
          (.sum <| .listAppList <| .var <| .termVarExt .head)) _ <|
          .sum <| .listApp (.var (.termVarExt .head)) <| ξττ'ke.soundness Γcw Γwe κe.row
            |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
        intro i mem
        simp [Function.comp, «F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open,
              «F⊗⊕ω».Term.TermVar_open]
        let τ'ike := τ'ke i mem
        let τ'ike' := τ'ke' i mem
        rw [τ'ike.deterministic τ'ike' |>.right,
            τ'ike'.soundness Γcw Γwe κe |>.TypeVarLocallyClosed_of.TypeVar_open_id]
        apply Typing.lam <| x :: Δ.termVarDom
        intro x xnin
        rw [«F⊗⊕ω».Term.TermVar_open, «F⊗⊕ω».Term.TermVar_open, if_pos rfl]
        let mem' : m + i ∈ [:m + n] := ⟨
          Nat.zero_le _,
          Nat.add_lt_add_left mem.upper _,
          Nat.mod_one _
        ⟩
        let ττ'ike := ττ'ke' (m + i) mem'
        dsimp [ττ'] at ττ'ike
        rw [if_neg <| Nat.not_lt_of_le <| Nat.le_add_right .., Nat.add_comm,
            Nat.add_sub_cancel, Nat.add_comm] at ττ'ike
        rw [τ'ike'.deterministic ττ'ike |>.right]
        let Δaxxwf := Δaxwf.termVarExt xnin <| .app (.var (.termVarExt .head)) <|
          ττ'ike.soundness Γcw Γwe κe |>.weakening Δaxwf
          (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
        cases A₂eq
        apply Typing.equiv _ <| .sum <| .symm <| .listAppList <| .var <| .termVarExt <|
          .termVarExt .head
        apply Typing.sumIntro mem' (.var Δaxxwf .head) _ <| by
          match h₀, h₁ with
          | .inl ne, _ =>
            exact .inl <| Nat.pos_iff_ne_zero.mp <| Nat.lt_add_right _ <| Nat.pos_of_ne_zero ne
          | _, .inl ne =>
            exact .inl <| Nat.pos_iff_ne_zero.mp <| Nat.lt_add_left _ <| Nat.pos_of_ne_zero ne
          | .inr b₀eq, .inr b₁eq =>
            right
            rw [BoolId, id, b₀eq, b₁eq, Bool.and]
        intro j mem''
        exact .app (.var (.termVarExt (.termVarExt .head))) <|
          ττ'ke' j mem'' |>.soundness Γcw Γwe κe |>.weakening Δaxxwf
          (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
  | concatEmptyL ρke κe =>
    rename «F⊗⊕ω».Kind => K
    rename Environment => Δ
    let .concat _ emptyke ρke' ρke'' κe' containke contain'ke := ψke
    let .contain _ emptyke' ρke''' κe'' := containke
    let .contain _ ρke'''' ρke''''' κe''' := contain'ke
    rcases emptyke.empty_row_inversion with ⟨_, κeq, κe'''', rfl⟩
    cases κeq
    rcases emptyke'.empty_row_inversion with ⟨_, κeq, κe''''', rfl⟩
    cases κeq
    rcases ρke.deterministic ρke' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    cases κe.deterministic κe''
    rcases ρke.deterministic ρke'' with ⟨_, rfl⟩
    rcases ρke.deterministic ρke''' with ⟨_, rfl⟩
    rcases ρke.deterministic ρke'''' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe'''
    rcases ρke.deterministic ρke''''' with ⟨_, rfl⟩
    cases κe.deterministic κe''''
    cases κe.deterministic κe'''''
    let Δwf := Γwe.soundness Γcw
    let Aki := ρke.soundness Γcw Γwe κe.row
    let Alc := Aki.TypeVarLocallyClosed_of
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Alc.TypeVar_open_id]
      apply Typing.equiv _ <| .arr (.prod (.listAppEmptyR (.var .head))) .refl
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.var _ .head
      let Δaxwf := Δwf.typeVarExt anin (K := [[(K ↦ *)]]) |>.termVarExt xₗnin .unit
      apply Δaxwf.termVarExt xᵣnin
      exact .prod <| .listApp (.var (.termVarExt .head)) <| Aki.weakening Δaxwf
        (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Alc.weaken (n := 1).TypeVar_open_id, Alc.TypeVar_open_id]
      let ane := List.ne_of_not_mem_cons aₜnin
      apply Typing.equiv _ <|
        .arr (.arr (.sum (.listAppEmptyR (.var <| .typeVarExt .head ane.symm))) .refl) .refl
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.var _ .head
      let Δaaₜxwf := Δwf.typeVarExt anin (K := [[(K ↦ *)]]) |>.typeVarExt aₜnin (K := .star)
        |>.termVarExt xₗnin <| .arr .never <| .var .head
      apply Δaaₜxwf.termVarExt xᵣnin
      apply Kinding.arr _ <| .var <| .termVarExt .head
      exact .sum <| .listApp (.var (.termVarExt (.typeVarExt .head ane.symm))) <|
        Aki.weakening Δaaₜxwf (Δ' := .termExt (.typeExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        apply Typing.equiv _ <| .prod (.listAppEmptyR (.var (.termVarExt .head)))
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.unit <| Δawf.termVarExt xnin _
        exact .prod <| .listApp (.var .head) <| Aki.weakening Δawf (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.equiv _ <| .arr (.sum (.listAppEmptyR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        let Δaxwf := Δwf.typeVarExt anin (K := [[(K ↦ *)]]) |>.termVarExt xnin .never
        exact .explode (.var Δaxwf .head) <| .sum <| .listApp (.var (.termVarExt .head)) <|
          Aki.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        apply Typing.var _ .head
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        exact Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
          Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
          Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        exact .var Δaxwf .head
  | concatEmptyR ρke κe =>
    rename «F⊗⊕ω».Kind => K
    rename Environment => Δ
    let .concat _ ρke' emptyke ρke'' κe' containke contain'ke := ψke
    let .contain _ ρke''' ρke'''' κe'' := containke
    let .contain _ emptyke' ρke''''' κe''' := contain'ke
    rcases emptyke.empty_row_inversion with ⟨_, κeq, κe'''', rfl⟩
    cases κeq
    rcases emptyke'.empty_row_inversion with ⟨_, κeq, κe''''', rfl⟩
    cases κeq
    rcases ρke.deterministic ρke' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    rcases ρke.deterministic ρke'' with ⟨_, rfl⟩
    rcases ρke.deterministic ρke''' with ⟨_, rfl⟩
    rcases ρke.deterministic ρke'''' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe''
    cases κe.deterministic κe'''
    cases κe.deterministic κe''''
    cases κe.deterministic κe'''''
    rcases ρke.deterministic ρke''''' with ⟨_, rfl⟩
    let Δwf := Γwe.soundness Γcw
    let Aki := ρke.soundness Γcw Γwe κe.row
    let Alc := Aki.TypeVarLocallyClosed_of
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Alc.TypeVar_open_id]
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.equiv _ <| .arr (.prod (.listAppEmptyR (.var (.termVarExt .head)))) .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.var _ <| .termVarExt .head <| Ne.symm <| List.ne_of_not_mem_cons xᵣnin
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      let Δaxₗwf := Δawf.termVarExt xₗnin <| .prod <| .listApp (.var .head) <|
        Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      exact Δaxₗwf.termVarExt xᵣnin .unit
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Alc.weaken (n := 1).TypeVar_open_id, Alc.TypeVar_open_id]
      let ane := List.ne_of_not_mem_cons aₜnin
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.equiv _ <|
        .arr (.arr (.sum (.listAppEmptyR (.var (.termVarExt (.typeVarExt .head ane.symm))))) .refl)
          .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      apply Typing.var _ <| .termVarExt .head <| Ne.symm <| List.ne_of_not_mem_cons xᵣnin
      let Δaaₜwf := Δwf.typeVarExt anin (K := [[(K ↦ *)]]) |>.typeVarExt aₜnin (K := .star)
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr
        (.sum (.listApp (.var (.typeVarExt .head ane.symm))
          (Aki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty))))
        (.var .head)
      exact Δaaₜxₗwf.termVarExt xᵣnin <| .arr .never <| .var <| .termVarExt .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        apply Typing.var _ .head
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        exact Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
          Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
          Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        exact .var Δaxwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        apply Typing.equiv _ <| .prod (.listAppEmptyR (.var (.termVarExt .head)))
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.unit <| Δawf.termVarExt xnin _
        exact .prod <| .listApp (.var .head) <| Aki.weakening Δawf (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        apply Typing.equiv _ <| .arr (.sum (.listAppEmptyR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [Alc.TypeVar_open_id]
        let Δaxwf := Δwf.typeVarExt anin (K := [[(K ↦ *)]]) |>.termVarExt xnin .never
        exact .explode (.var Δaxwf .head) <| .sum <| .listApp (.var (.termVarExt .head)) <|
          Aki.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
  | concatAssocL _ concat₁₂ce _ ρ₀ke ρ₁ke ρ₂ke ρ₃ke ρ₅ke κe concat₀₁ih concat₁₂ih concat₀₄ih =>
    rename_i A₅ K _ _
    let .concat μke ρ₃ke' ρ₂ke' ρ₅ke' κe' contain₃₅ke contain₂₅ke := ψke
    let .contain μke' ρ₃ke'' ρ₅ke'' κe'' := contain₃₅ke
    let .contain μke'' ρ₂ke'' ρ₅ke''' κe''' := contain₂₅ke
    let ⟨_, .concat μke''' ρ₁ke' ρ₂ke''' ρ₄ke κe'''' concat₁₄ke concat₂₄ke⟩ :=
      concat₁₂ce.to_Kinding Γᵢw Γcw Γwe
    let .contain μke'''' ρ₁ke'' ρ₄ke' κe''''' := concat₁₄ke
    let .contain μke''''' ρ₂ke'''' ρ₄ke'' κe'''''' := concat₂₄ke
    rcases μke.deterministic μke' with ⟨_, rfl⟩
    rcases μke.deterministic μke'' with ⟨_, rfl⟩
    rcases μke.deterministic μke''' with ⟨_, rfl⟩
    rcases μke.deterministic μke'''' with ⟨_, rfl⟩
    rcases μke.deterministic μke''''' with ⟨_, rfl⟩
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₁ke.deterministic ρ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke''' with ⟨_, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke'''' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₃ke.deterministic ρ₃ke' with ⟨_, rfl⟩
    rcases ρ₃ke.deterministic ρ₃ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₄ke.deterministic ρ₄ke' with ⟨_, rfl⟩
    rcases ρ₄ke.deterministic ρ₄ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₅ke.deterministic ρ₅ke' with ⟨_, rfl⟩
    rcases ρ₅ke.deterministic ρ₅ke'' with ⟨_, rfl⟩
    rcases ρ₅ke.deterministic ρ₅ke''' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    cases κe.deterministic κe''
    cases κe.deterministic κe'''
    cases κe.deterministic κe''''
    cases κe.deterministic κe'''''
    cases κe.deterministic κe''''''
    let E₀₁ty := concat₀₁ih
      (.concat μke ρ₀ke ρ₁ke ρ₃ke κe (.contain μke ρ₀ke ρ₃ke κe) (.contain μke ρ₁ke ρ₃ke κe))
      Γᵢw Γcw Γwe
    let E₀₁tlc := E₀₁ty.TermTypeVarLocallyClosed_of
    let E₀₁lc := E₀₁ty.TermVarLocallyClosed_of
    let E₁₂ty := concat₁₂ih
      (.concat μke ρ₁ke ρ₂ke ρ₄ke κe (.contain μke ρ₁ke ρ₄ke κe) (.contain μke ρ₂ke ρ₄ke κe))
      Γᵢw Γcw Γwe
    let E₁₂tlc := E₁₂ty.TermTypeVarLocallyClosed_of
    let E₁₂lc := E₁₂ty.TermVarLocallyClosed_of
    let E₀₄ty := concat₀₄ih
      (.concat μke ρ₀ke ρ₄ke ρ₅ke κe (.contain μke ρ₀ke ρ₅ke κe) (.contain μke ρ₄ke ρ₅ke κe))
      Γᵢw Γcw Γwe
    let E₀₄tlc := E₀₄ty.TermTypeVarLocallyClosed_of
    let E₀₄lc := E₀₄ty.TermVarLocallyClosed_of
    let A₀ki := ρ₀ke.soundness Γcw Γwe κe.row
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    let A₁ki := ρ₁ke.soundness Γcw Γwe κe.row
    let A₁lc := A₁ki.TypeVarLocallyClosed_of
    let A₂ki := ρ₂ke.soundness Γcw Γwe κe.row
    let A₂lc := A₂ki.TypeVarLocallyClosed_of
    let A₃ki := ρ₃ke.soundness Γcw Γwe κe.row
    let A₃lc := A₃ki.TypeVarLocallyClosed_of
    let A₄ki := ρ₄ke.soundness Γcw Γwe κe.row
    let A₄lc := A₄ki.TypeVarLocallyClosed_of
    let A₅ki := ρ₅ke.soundness Γcw Γwe κe.row
    let A₅lc := A₅ki.TypeVarLocallyClosed_of
    let Δwf := Γwe.soundness Γcw
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at E₀₁ty E₁₂ty E₀₄ty
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₂lc.TypeVar_open_id, A₃lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id,
          E₁₂tlc.TypeVar_open_id, E₀₄tlc.TypeVar_open_id]
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.weaken (n := 1).TermVar_open_id, E₁₂lc.weaken (n := 1).TermVar_open_id,
          E₀₄lc.weaken (n := 1).TermVar_open_id]
      let Δaxₗwf := Δawf.termVarExt xₗnin <| .prod <| .listApp (.var .head) <|
        A₃ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xne := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.TermVar_open_id, E₁₂lc.TermVar_open_id, E₀₄lc.TermVar_open_id]
      let Δaxₗᵣwf := Δaxₗwf.termVarExt xᵣnin <| .prod <| .listApp (.var (.termVarExt .head)) <|
        A₂ki.weakening Δaxₗwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
      apply Typing.app
      · apply Typing.app
        · let πty := E₀₄ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxₗᵣwf (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..)
              (Δ'' := .empty)
          simp at πty
          have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₀lc.Type_open_id, A₄lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxₗᵣwf
                (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at this
            exact this
          · exact .var Δaxₗᵣwf <| .termVarExt .head xne.symm
      · apply Typing.app
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxₗᵣwf
                (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
            simp at πty
            have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₂lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · apply Typing.app
            · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxₗᵣwf
                  (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₁lc.Type_open_id, A₃lc.Type_open_id] at this
              exact this
            · exact .var Δaxₗᵣwf <| .termVarExt .head xne.symm
        · exact .var Δaxₗᵣwf .head
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₀lc.weaken (n := 1).TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
          A₂lc.weaken (n := 1).TypeVar_open_id, A₃lc.weaken (n := 1).TypeVar_open_id,
          A₅lc.weaken (n := 1).TypeVar_open_id, E₀₁tlc.weaken (n := 1).TypeVar_open_id,
          E₁₂tlc.weaken (n := 1).TypeVar_open_id, E₀₄tlc.weaken (n := 1).TypeVar_open_id]
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      let ane := List.ne_of_not_mem_cons aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id, A₂lc.TypeVar_open_id, A₃lc.TypeVar_open_id,
          A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id, E₁₂tlc.TypeVar_open_id,
          E₀₄tlc.TypeVar_open_id]
      let Δaaₜwf := Δawf.typeVarExt aₜnin (K := .star)
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.weaken (n := 2).TermVar_open_id, E₁₂lc.weaken (n := 1).TermVar_open_id,
          E₀₄lc.weaken (n := 1).TermVar_open_id]
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr
        (.sum (.listApp (.var (.typeVarExt .head ane.symm))
          (A₃ki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty))))
        <| .var .head
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xᵣnexₗ := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.weaken (n := 1).TermVar_open_id, E₁₂lc.TermVar_open_id, E₀₄lc.TermVar_open_id]
      let Δaaₜxₗᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr
        (.sum (.listApp (.var (.termVarExt (.typeVarExt .head ane.symm)))
          (A₂ki.weakening Δaaₜxₗwf (Δ' := .termExt (.typeExt (.typeExt .empty ..) ..) ..)
            (Δ'' := .empty))))
        <| .var <| .termVarExt .head
      apply Typing.app
      · apply Typing.app
        · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
              (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
          simp at πty
          have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
            .typeVarExt .head ane.symm
          simp [Type.Type_open] at this
          rw [A₀lc.weaken (n := 1).Type_open_id, A₄lc.weaken (n := 1).Type_open_id,
              A₅lc.weaken (n := 1).Type_open_id] at this
          have := this.typeApp (B := .var aₜ) <| .var <| .termVarExt <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₀lc.Type_open_id, A₄lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
        · apply Typing.lam <| xᵣ :: xₗ :: Δ.termVarDom
          intro x xnin
          let xnexₗ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xnin
          let xnexᵣ := List.ne_of_not_mem_cons xnin
          simp [«F⊗⊕ω».Term.TermVar_open]
          rw [E₀₁lc.TermVar_open_id]
          let Δaaₜxₗᵣxwf := Δaaₜxₗᵣwf.termVarExt xnin <| .sum <| .listApp
            (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm)))) <|
            A₀ki.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
            (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
          apply Typing.app
          · exact .var Δaaₜxₗᵣxwf <| .termVarExt (.termVarExt .head xᵣnexₗ.symm) xnexₗ.symm
          · apply Typing.app
            · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaaₜxₗᵣxwf (Δ'' := .empty)
                  (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
                .termVarExt <| .typeVarExt .head ane.symm
              simp [Type.Type_open] at this
              rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at this
              exact this
            · exact .var Δaaₜxₗᵣxwf .head
      · apply Typing.app
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
                (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
            simp at πty
            have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
              .typeVarExt .head ane.symm
            simp [Type.Type_open] at this
            rw [A₁lc.weaken (n := 1).Type_open_id, A₂lc.weaken (n := 1).Type_open_id,
                A₄lc.weaken (n := 1).Type_open_id] at this
            have := this.typeApp (B := .var aₜ) <| .var <| .termVarExt <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₂lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · apply Typing.lam <| xᵣ :: xₗ :: Δ.termVarDom
            intro x xnin
            let xnexₗ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xnin
            let xnexᵣ := List.ne_of_not_mem_cons xnin
            simp [«F⊗⊕ω».Term.TermVar_open]
            rw [E₀₁lc.TermVar_open_id]
            let Δaaₜxₗᵣxwf := Δaaₜxₗᵣwf.termVarExt xnin <| .sum <| .listApp
              (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm)))) <|
              A₁ki.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
              (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
            apply Typing.app
            · exact .var Δaaₜxₗᵣxwf <| .termVarExt (.termVarExt .head xᵣnexₗ.symm) xnexₗ.symm
            · apply Typing.app
              · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
                  (b := false) |>.weakening Δaaₜxₗᵣxwf (Δ'' := .empty)
                    (Δ' := .termExt (.termExt (.termExt (.typeExt
                      (.typeExt .empty ..) ..) ..) ..) ..)
                simp at πty
                rw [← Range.map_get!_eq (as := [_, _])] at πty
                let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
                simp at π'ty
                have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
                  .termVarExt <| .typeVarExt .head ane.symm
                simp [Type.Type_open] at this
                rw [A₁lc.Type_open_id, A₃lc.Type_open_id] at this
                exact this
              · exact .var Δaaₜxₗᵣxwf .head
        · exact .var Δaaₜxₗᵣwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₃lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id,
            E₁₂tlc.TypeVar_open_id, E₀₄tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.lam Δ.termVarDom
        intro x xnin
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
          A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₀₁lc.TermVar_open_id, E₁₂lc.TermVar_open_id, E₀₄lc.TermVar_open_id]
        apply Typing.app
        · apply Typing.app
          · let πty := E₀₁ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            have := πty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₃lc.Type_open_id] at this
            exact this
          · apply Typing.app
            · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                  (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₀lc.Type_open_id, A₅lc.Type_open_id] at this
              exact this
            · exact .var Δaxwf .head
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · apply Typing.app
            · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                  (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₄lc.Type_open_id, A₅lc.Type_open_id] at this
              exact this
            · exact .var Δaxwf .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₁lc.TypeVar_open_id, A₃lc.TypeVar_open_id, A₅lc.TypeVar_open_id,
            E₀₁tlc.TypeVar_open_id, E₁₂tlc.TypeVar_open_id, E₀₄tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.app
        · apply Typing.app
          · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
            simp at πty
            have := πty.typeApp (B := .var a) <| .var .head
            simp [Type.Type_open] at this
            rw [A₀lc.weaken (n := 1).Type_open_id, A₁lc.weaken (n := 1).Type_open_id,
                A₃lc.weaken (n := 1).Type_open_id] at this
            have := this.typeApp (B := [[⊕ (a ⟦A₅⟧)]]) <| .sum <| .listApp (.var .head) <|
              A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
            simp [Type.Type_open] at this
            rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₃lc.Type_open_id] at this
            exact this
          · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var .head
            simp [Type.Type_open] at this
            rw [A₀lc.Type_open_id, A₅lc.Type_open_id] at this
            exact this
        · apply Typing.lam Δ.termVarDom
          intro x xnin
          let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
            A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          simp [«F⊗⊕ω».Term.TermVar_open]
          rw [E₁₂lc.TermVar_open_id, E₀₄lc.TermVar_open_id]
          apply Typing.app
          · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₄lc.Type_open_id, A₅lc.Type_open_id] at this
            exact this
          · apply Typing.app
            · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                  (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at this
              exact this
            · exact .var Δaxwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₂lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₁₂tlc.TypeVar_open_id,
            E₀₄tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.lam Δ.termVarDom
        intro x xnin
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
          A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₁₂lc.TermVar_open_id, E₀₄lc.TermVar_open_id]
        apply Typing.app
        · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          simp at π'ty
          have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₂lc.Type_open_id, A₄lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₄lc.Type_open_id, A₅lc.Type_open_id] at this
            exact this
          · exact .var Δaxwf .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₂lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₁₂tlc.TypeVar_open_id,
            E₀₄tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.lam Δ.termVarDom
        intro x xnin
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
          A₂ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₁₂lc.TermVar_open_id, E₀₄lc.TermVar_open_id]
        apply Typing.app
        · let πty := E₀₄ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          simp at π'ty
          have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₄lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₂lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · exact .var Δaxwf .head
  | concatAssocR concat₀₁ce _ _ ρ₀ke ρ₁ke ρ₂ke ρ₄ke ρ₅ke κe concat₀₁ih concat₁₂ih concat₃₂ih =>
    rename_i A₅ K _ _
    let .concat μke ρ₀ke' ρ₄ke' ρ₅ke' κe' contain₀₅ke contain₄₅ke := ψke
    let .contain μke' ρ₀ke'' ρ₅ke'' κe'' := contain₀₅ke
    let .contain μke'' ρ₄ke'' ρ₅ke''' κe''' := contain₄₅ke
    let ⟨_, .concat μke''' ρ₀ke''' ρ₁ke' ρ₃ke κe'''' concat₀₃ke concat₁₃ke⟩ :=
      concat₀₁ce.to_Kinding Γᵢw Γcw Γwe
    let .contain μke'''' ρ₀ke'''' ρ₃ke' κe''''' := concat₀₃ke
    let .contain μke''''' ρ₁ke'' ρ₃ke'' κe'''''' := concat₁₃ke
    rcases μke.deterministic μke' with ⟨_, rfl⟩
    rcases μke.deterministic μke'' with ⟨_, rfl⟩
    rcases μke.deterministic μke''' with ⟨_, rfl⟩
    rcases μke.deterministic μke'''' with ⟨_, rfl⟩
    rcases μke.deterministic μke''''' with ⟨_, rfl⟩
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₀ke.deterministic ρ₀ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₀ke.deterministic ρ₀ke''' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₀ke.deterministic ρ₀ke'''' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    rcases ρ₁ke.deterministic ρ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₃ke.deterministic ρ₃ke' with ⟨_, rfl⟩
    rcases ρ₃ke.deterministic ρ₃ke'' with ⟨_, rfl⟩
    rcases ρ₄ke.deterministic ρ₄ke' with ⟨_, rfl⟩
    rcases ρ₄ke.deterministic ρ₄ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₅ke.deterministic ρ₅ke' with ⟨_, rfl⟩
    rcases ρ₅ke.deterministic ρ₅ke'' with ⟨_, rfl⟩
    rcases ρ₅ke.deterministic ρ₅ke''' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    cases κe.deterministic κe''
    cases κe.deterministic κe'''
    cases κe.deterministic κe''''
    cases κe.deterministic κe'''''
    cases κe.deterministic κe''''''
    let E₀₁ty := concat₀₁ih
      (.concat μke ρ₀ke ρ₁ke ρ₃ke κe (.contain μke ρ₀ke ρ₃ke κe) (.contain μke ρ₁ke ρ₃ke κe))
      Γᵢw Γcw Γwe
    let E₀₁tlc := E₀₁ty.TermTypeVarLocallyClosed_of
    let E₀₁lc := E₀₁ty.TermVarLocallyClosed_of
    let E₁₂ty := concat₁₂ih
      (.concat μke ρ₁ke ρ₂ke ρ₄ke κe (.contain μke ρ₁ke ρ₄ke κe) (.contain μke ρ₂ke ρ₄ke κe))
      Γᵢw Γcw Γwe
    let E₁₂tlc := E₁₂ty.TermTypeVarLocallyClosed_of
    let E₁₂lc := E₁₂ty.TermVarLocallyClosed_of
    let E₃₂ty := concat₃₂ih
      (.concat μke ρ₃ke ρ₂ke ρ₅ke κe (.contain μke ρ₃ke ρ₅ke κe) (.contain μke ρ₂ke ρ₅ke κe))
      Γᵢw Γcw Γwe
    let E₃₂tlc := E₃₂ty.TermTypeVarLocallyClosed_of
    let E₃₂lc := E₃₂ty.TermVarLocallyClosed_of
    let A₀ki := ρ₀ke.soundness Γcw Γwe κe.row
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    let A₁ki := ρ₁ke.soundness Γcw Γwe κe.row
    let A₁lc := A₁ki.TypeVarLocallyClosed_of
    let A₂ki := ρ₂ke.soundness Γcw Γwe κe.row
    let A₂lc := A₂ki.TypeVarLocallyClosed_of
    let A₃ki := ρ₃ke.soundness Γcw Γwe κe.row
    let A₃lc := A₃ki.TypeVarLocallyClosed_of
    let A₄ki := ρ₄ke.soundness Γcw Γwe κe.row
    let A₄lc := A₄ki.TypeVarLocallyClosed_of
    let A₅ki := ρ₅ke.soundness Γcw Γwe κe.row
    let A₅lc := A₅ki.TypeVarLocallyClosed_of
    let Δwf := Γwe.soundness Γcw
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at E₀₁ty E₁₂ty E₃₂ty
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₀lc.TypeVar_open_id, A₄lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id,
          E₁₂tlc.TypeVar_open_id, E₃₂tlc.TypeVar_open_id]
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.weaken (n := 1).TermVar_open_id, E₁₂lc.weaken (n := 1).TermVar_open_id,
          E₃₂lc.weaken (n := 1).TermVar_open_id]
      let Δaxₗwf := Δawf.termVarExt xₗnin <| .prod <| .listApp (.var .head) <|
        A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xne := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.TermVar_open_id, E₁₂lc.TermVar_open_id, E₃₂lc.TermVar_open_id]
      let Δaxₗᵣwf := Δaxₗwf.termVarExt xᵣnin <| .prod <| .listApp (.var (.termVarExt .head)) <|
        A₄ki.weakening Δaxₗwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
      apply Typing.app
      · apply Typing.app
        · let πty := E₃₂ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxₗᵣwf (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..)
              (Δ'' := .empty)
          simp at πty
          have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₂lc.Type_open_id, A₃lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · apply Typing.app
            · let πty := E₀₁ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxₗᵣwf
                  (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
              simp at πty
              have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₃lc.Type_open_id] at this
              exact this
            · exact .var Δaxₗᵣwf <| .termVarExt .head xne.symm
          · apply Typing.app
            · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxₗᵣwf
                  (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at this
              exact this
            · exact .var Δaxₗᵣwf .head
      · apply Typing.app
        · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxₗᵣwf
              (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          simp at π'ty
          have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₂lc.Type_open_id, A₄lc.Type_open_id] at this
          exact this
        · exact .var Δaxₗᵣwf .head
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₀lc.weaken (n := 1).TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
          A₂lc.weaken (n := 1).TypeVar_open_id, A₄lc.weaken (n := 1).TypeVar_open_id,
          A₅lc.weaken (n := 1).TypeVar_open_id, E₀₁tlc.weaken (n := 1).TypeVar_open_id,
          E₁₂tlc.weaken (n := 1).TypeVar_open_id, E₃₂tlc.weaken (n := 1).TypeVar_open_id]
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      let ane := List.ne_of_not_mem_cons aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      rw [A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id, A₂lc.TypeVar_open_id, A₄lc.TypeVar_open_id,
          A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id, E₁₂tlc.TypeVar_open_id,
          E₃₂tlc.TypeVar_open_id]
      let Δaaₜwf := Δawf.typeVarExt aₜnin (K := .star)
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.weaken (n := 1).TermVar_open_id, E₁₂lc.weaken (n := 2).TermVar_open_id,
          E₃₂lc.weaken (n := 1).TermVar_open_id]
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr
        (.sum (.listApp (.var (.typeVarExt .head ane.symm))
          (A₀ki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty))))
        <| .var .head
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xᵣnexₗ := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [E₀₁lc.TermVar_open_id, E₁₂lc.weaken (n := 1).TermVar_open_id, E₃₂lc.TermVar_open_id]
      let Δaaₜxₗᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr
        (.sum (.listApp (.var (.termVarExt (.typeVarExt .head ane.symm)))
          (A₄ki.weakening Δaaₜxₗwf (Δ' := .termExt (.typeExt (.typeExt .empty ..) ..) ..)
            (Δ'' := .empty))))
        <| .var <| .termVarExt .head
      apply Typing.app
      · apply Typing.app
        · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
              (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
          simp at πty
          have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
            .typeVarExt .head ane.symm
          simp [Type.Type_open] at this
          rw [A₂lc.weaken (n := 1).Type_open_id, A₃lc.weaken (n := 1).Type_open_id,
              A₅lc.weaken (n := 1).Type_open_id] at this
          have := this.typeApp (B := .var aₜ) <| .var <| .termVarExt <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₂lc.Type_open_id, A₃lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · apply Typing.app
            · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
                  (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
              simp at πty
              have := πty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
                .typeVarExt .head ane.symm
              simp [Type.Type_open] at this
              rw [A₀lc.weaken (n := 1).Type_open_id, A₁lc.weaken (n := 1).Type_open_id,
                  A₃lc.weaken (n := 1).Type_open_id] at this
              have := this.typeApp (B := .var aₜ) <| .var <| .termVarExt <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₃lc.Type_open_id] at this
              exact this
            · exact .var Δaaₜxₗᵣwf <| .termVarExt .head xᵣnexₗ.symm
          · apply Typing.lam <| xᵣ :: xₗ :: Δ.termVarDom
            intro x xnin
            let xnexᵣ := List.ne_of_not_mem_cons xnin
            simp [«F⊗⊕ω».Term.TermVar_open]
            rw [E₁₂lc.TermVar_open_id]
            let Δaaₜxₗᵣxwf := Δaaₜxₗᵣwf.termVarExt xnin <| .sum <| .listApp
              (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm)))) <|
              A₁ki.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
              (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
            apply Typing.app
            · exact .var Δaaₜxₗᵣxwf <| .termVarExt .head xnexᵣ.symm
            · apply Typing.app
              · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                  (b := false) |>.weakening Δaaₜxₗᵣxwf (Δ'' := .empty)
                    (Δ' := .termExt (.termExt (.termExt (.typeExt
                      (.typeExt .empty ..) ..) ..) ..) ..)
                simp at πty
                rw [← Range.map_get!_eq (as := [_, _])] at πty
                let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
                simp at π'ty
                have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
                  .termVarExt <| .typeVarExt .head ane.symm
                simp [Type.Type_open] at this
                rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at this
                exact this
              · exact .var Δaaₜxₗᵣxwf .head
      · apply Typing.lam <| xᵣ :: xₗ :: Δ.termVarDom
        intro x xnin
        let xnexᵣ := List.ne_of_not_mem_cons xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₁₂lc.TermVar_open_id]
        let Δaaₜxₗᵣxwf := Δaaₜxₗᵣwf.termVarExt xnin <| .sum <| .listApp
          (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm)))) <|
          A₂ki.weakening Δaaₜxₗᵣwf (Δ'' := .empty)
          (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
        apply Typing.app
        · exact .var Δaaₜxₗᵣxwf <| .termVarExt .head xnexᵣ.symm
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
              (b := false) |>.weakening Δaaₜxₗᵣxwf (Δ'' := .empty)
                (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
              .termVarExt <| .typeVarExt .head ane.symm
            simp [Type.Type_open] at this
            rw [A₂lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · exact .var Δaaₜxₗᵣxwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₀lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id,
            E₃₂tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.lam Δ.termVarDom
        intro x xnin
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
          A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₀₁lc.TermVar_open_id, E₃₂lc.TermVar_open_id]
        apply Typing.app
        · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          simp at π'ty
          have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₃lc.Type_open_id, A₅lc.Type_open_id] at this
            exact this
          · exact .var Δaxwf .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₀lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id,
            E₃₂tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.lam Δ.termVarDom
        intro x xnin
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
          A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₀₁lc.TermVar_open_id, E₃₂lc.TermVar_open_id]
        apply Typing.app
        · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
            (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          simp at π'ty
          have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
          simp [Type.Type_open] at this
          rw [A₃lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
        · apply Typing.app
          · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at this
            exact this
          · exact .var Δaxwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₄lc.TypeVar_open_id, A₅lc.TypeVar_open_id, E₀₁tlc.TypeVar_open_id,
            E₁₂tlc.TypeVar_open_id, E₃₂tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.lam Δ.termVarDom
        intro x xnin
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
          A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp [«F⊗⊕ω».Term.TermVar_open]
        rw [E₀₁lc.TermVar_open_id, E₁₂lc.TermVar_open_id, E₃₂lc.TermVar_open_id]
        apply Typing.app
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            have := πty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₂lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · apply Typing.app
            · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                  (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₁lc.Type_open_id, A₃lc.Type_open_id] at this
              exact this
            · apply Typing.app
              · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                  (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                    (Δ'' := .empty)
                simp at πty
                rw [← Range.map_get!_eq (as := [_, _])] at πty
                let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
                simp at π'ty
                have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
                simp [Type.Type_open] at this
                rw [A₃lc.Type_open_id, A₅lc.Type_open_id] at this
                exact this
              · exact .var Δaxwf .head
        · apply Typing.app
          · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
              (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                (Δ'' := .empty)
            simp at πty
            rw [← Range.map_get!_eq (as := [_, _])] at πty
            let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
            simp at π'ty
            have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
            simp [Type.Type_open] at this
            rw [A₂lc.Type_open_id, A₅lc.Type_open_id] at this
            exact this
          · exact .var Δaxwf .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        rw [A₁lc.TypeVar_open_id, A₄lc.TypeVar_open_id, A₅lc.TypeVar_open_id,
            E₀₁tlc.TypeVar_open_id, E₁₂tlc.TypeVar_open_id, E₃₂tlc.TypeVar_open_id]
        let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
        apply Typing.app
        · apply Typing.app
          · let πty := E₁₂ty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
              (b := false) |>.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
            simp at πty
            have := πty.typeApp (B := .var a) <| .var .head
            simp [Type.Type_open] at this
            rw [A₁lc.weaken (n := 1).Type_open_id, A₂lc.weaken (n := 1).Type_open_id,
                A₄lc.weaken (n := 1).Type_open_id] at this
            have := this.typeApp (B := [[⊕ (a ⟦A₅⟧)]]) <| .sum <| .listApp (.var .head) <|
              A₅ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₂lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this
          · apply Typing.lam Δ.termVarDom
            intro x xnin
            let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
              A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
            simp [«F⊗⊕ω».Term.TermVar_open]
            rw [E₀₁lc.TermVar_open_id, E₃₂lc.TermVar_open_id]
            apply Typing.app
            · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
                (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                  (Δ'' := .empty)
              simp at πty
              rw [← Range.map_get!_eq (as := [_, _])] at πty
              let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
              simp at π'ty
              have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
              simp [Type.Type_open] at this
              rw [A₃lc.Type_open_id, A₅lc.Type_open_id] at this
              exact this
            · apply Typing.app
              · let πty := E₀₁ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
                  (b := false) |>.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..)
                    (Δ'' := .empty)
                simp at πty
                rw [← Range.map_get!_eq (as := [_, _])] at πty
                let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
                simp at π'ty
                have := π'ty.typeApp (B := .var a) <| .var <| .termVarExt .head
                simp [Type.Type_open] at this
                rw [A₁lc.Type_open_id, A₃lc.Type_open_id] at this
                exact this
              · exact .var Δaxwf .head
        · let πty := E₃₂ty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
            (b := false) |>.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          simp at πty
          rw [← Range.map_get!_eq (as := [_, _])] at πty
          let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          simp at π'ty
          have := π'ty.typeApp (B := .var a) <| .var .head
          simp [Type.Type_open] at this
          rw [A₂lc.Type_open_id, A₅lc.Type_open_id] at this
          exact this
  | concatContainL concatce ih =>
    let ⟨_, concatke@(.concat _ _ _ _ _ containke _)⟩ := concatce.to_Kinding Γᵢw Γcw Γwe
    rcases ψke.deterministic containke with ⟨_, rfl⟩
    let Ety := ih concatke Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
    let πty := Ety.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
    simp at πty
    exact πty
  | concatContainR concatce ih =>
    let ⟨_, concatke@(.concat _ _ _ _ _ _ containke)⟩ := concatce.to_Kinding Γᵢw Γcw Γwe
    rcases ψke.deterministic containke with ⟨_, rfl⟩
    let Ety := ih concatke Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
    let πty := Ety.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
    simp at πty
    exact πty
  | concatSwap concatce ρ₀ke ρ₁ke κe ih =>
    rename «F⊗⊕ω».Kind => K
    let .concat .comm ρ₁ke' ρ₀ke' ρ₂ke κe' contain₁₂ke contain₀₂ke := ψke
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    let .contain .comm ρ₁ke'' ρ₂ke' κe'' := contain₁₂ke
    rcases ρ₁ke.deterministic ρ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨_, rfl⟩
    cases κe.deterministic κe''
    let .contain .comm ρ₀ke'' ρ₂ke'' κe''' := contain₀₂ke
    rcases ρ₀ke.deterministic ρ₀ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke'' with ⟨_, rfl⟩
    cases κe.deterministic κe'''
    let Ety := ih
      (.concat .comm ρ₀ke ρ₁ke ρ₂ke κe (.contain .comm ρ₀ke ρ₂ke κe) (.contain .comm ρ₁ke ρ₂ke κe))
      Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
    let Δwf := Γwe.soundness Γcw
    let A₀ki := ρ₀ke.soundness Γcw Γwe κe.row
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    let A₁ki := ρ₁ke.soundness Γcw Γwe κe.row
    let A₁lc := A₁ki.TypeVarLocallyClosed_of
    let A₂ki := ρ₂ke.soundness Γcw Γwe κe.row
    let A₂lc := A₂ki.TypeVarLocallyClosed_of
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id, A₂lc.TypeVar_open_id,
          Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [Ety.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id]
      let Δaxₗwf := Δawf.termVarExt xₗnin <| .prod <| .listApp (.var .head) <|
        A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xne := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗᵣwf := Δaxₗwf.termVarExt xᵣnin <| .prod <| .listApp (.var (.termVarExt .head)) <|
        A₀ki.weakening Δaxₗwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
      rw [Ety.TermVarLocallyClosed_of.TermVar_open_id]
      let πty := Ety.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩ (b := false)
      simp at πty
      let πty' := πty.weakening Δaxₗᵣwf (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..)
        (Δ'' := .empty)
      have := πty'.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt .head
      simp [Type.Type_open] at this
      rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at this
      exact this.app (.var Δaxₗᵣwf .head) |>.app <| .var Δaxₗᵣwf <| .termVarExt .head xne.symm
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [A₀lc.weaken (n := 1).TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
          A₂lc.weaken (n := 1).TypeVar_open_id,
          Ety.TermTypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_id]
      let Δawf := Δwf.typeVarExt anin (K := [[(K ↦ *)]])
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      let ane := List.ne_of_not_mem_cons aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id, A₂lc.TypeVar_open_id,
          Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
      let Δaaₜwf := Δawf.typeVarExt aₜnin (K := .star)
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      rw [Ety.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id]
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr
        (.sum (.listApp (.var (.typeVarExt .head ane.symm))
          (A₁ki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty)))) <|
        .var .head
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xne := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr
        (.sum (.listApp (.var (.termVarExt (.typeVarExt .head ane.symm)))
          (A₀ki.weakening Δaaₜxₗwf (Δ' := .termExt (.typeExt (.typeExt .empty ..) ..) ..)
            (Δ'' := .empty)))) <|
        .var <| .termVarExt .head
      rw [Ety.TermVarLocallyClosed_of.TermVar_open_id]
      let πty := Ety.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩ (b := false)
      simp at πty
      let πty' :=
        πty.weakening Δaaₜxₗᵣwf (Δ' := .termExt (.termExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
        (Δ'' := .empty)
      have := πty'.typeApp (B := .var a) <| .var <| .termVarExt <| .termVarExt <|
        .typeVarExt .head ane.symm
      simp [Type.Type_open] at this
      rw [A₀lc.weaken (n := 1).Type_open_id, A₁lc.weaken (n := 1).Type_open_id,
          A₂lc.weaken (n := 1).Type_open_id] at this
      have := this.typeApp (B := .var aₜ) <| .var <| .termVarExt <| .termVarExt .head
      simp [Type.Type_open] at this
      rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at this
      exact this.app (.var Δaaₜxₗᵣwf .head) |>.app <| .var Δaaₜxₗᵣwf <| .termVarExt .head xne.symm
    · let πty := Ety.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
      simp at πty
      exact πty
    · let πty := Ety.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
      simp at πty
      exact πty
  | containDecay containce _ _ ih =>
    let ⟨_, .contain μ₀ke ..⟩ := containce.to_Kinding Γᵢw Γcw Γwe
    let .contain _ ρ₀ke ρ₁ke κe := ψke
    exact ih (.contain μ₀ke ρ₀ke ρ₁ke κe) Γᵢw Γcw Γwe
  | concatDecay concatce _ _ ih =>
    let .concat _ ρ₀ke ρ₁ke ρ₂ke κe contain₀₂ke contain₁₂ke := ψke
    let ⟨A, concatke⟩ := concatce.to_Kinding Γᵢw Γcw Γwe
    let Ety := ih concatke Γᵢw Γcw Γwe
    cases concatke
    case concat κe' ρ₀ke' _ ρ₁ke' ρ₂ke' contain₀₂ke' contain₁₂ke' =>
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    cases contain₀₂ke
    case contain κe'' ρ₀ke'' _ ρ₂ke'' =>
    rcases ρ₀ke.deterministic ρ₀ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke'' with ⟨_, rfl⟩
    cases κe.deterministic κe''
    cases contain₀₂ke'
    case contain κe''' ρ₀ke''' _ ρ₂ke''' =>
    rcases ρ₀ke.deterministic ρ₀ke''' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke''' with ⟨_, rfl⟩
    cases κe.deterministic κe'''
    cases contain₁₂ke
    case contain κe'''' ρ₁ke'' _ ρ₂ke'''' =>
    rcases ρ₁ke.deterministic ρ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke'''' with ⟨_, rfl⟩
    cases κe.deterministic κe''''
    cases contain₁₂ke'
    case contain κe''''' ρ₁ke''' _ ρ₂ke''''' =>
    rcases ρ₁ke.deterministic ρ₁ke''' with ⟨κeq, rfl⟩
    cases κeq
    rcases ρ₂ke.deterministic ρ₂ke''''' with ⟨_, rfl⟩
    cases κe.deterministic κe'''''
    exact Ety
  | liftContain I containce ρ₀ke τke κ₀e κ₁e ih =>
    rename_i Γ _ _ _ _ _ _ _ A' K₀ K₁
    let .contain _ lift₀ke lift₁ke κ₁e' .. := ψke
    let .lift I' τke' κ₀e' ρ₀ke' (A := A'') := lift₀ke
    let .lift I'' τke'' κ₀e'' ρ₁ke (A := A''') := lift₁ke
    let ⟨a, anin⟩ := I ++ I' ++ I'' ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninII'I'', aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninII', aninI''⟩ := List.not_mem_append'.mp aninII'I''
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let Γawe := Γwe.typeExt aninΓ κ₀e
    rcases τke _ aninI |>.deterministic <| τke' _ aninI' with ⟨rfl, A'eqA''⟩
    cases κ₁e.deterministic κ₁e'
    cases κ₀e.deterministic κ₀e'
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨_, rfl⟩
    rcases τke _ aninI |>.deterministic <| τke'' _ aninI'' with ⟨_, A'eqA'''⟩
    cases κ₀e.deterministic κ₀e''
    let ⟨_, containke⟩ := containce.to_Kinding Γᵢw Γcw Γwe
    let Ety := ih containke Γᵢw Γcw Γwe
    cases containke
    case contain κ₀e'' ρ₀ke''' _ ρ₁ke' =>
    rcases ρ₀ke.deterministic ρ₀ke''' with ⟨κeq, rfl⟩
    cases κeq
    cases κ₀e.deterministic κ₀e''
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    let Δwf := Γwe.soundness Γcw
    apply Typing.pair
    · apply Typing.typeLam Γ.typeVarDom
      intro a' a'nin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
      let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
      let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
      rw [← Range.map_get!_eq (as := [_, _])] at Ety
      let πty := Ety.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
        |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      simp at πty
      have := πty.typeApp (B := [[λ aᵢ : K₀. a' A']]) <| by
        apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
        intro a'' a''nin
        let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
        let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
        simp [Type.TypeVar_open]
        let Γa''we := Γwe.typeExt a''ninΓ κ₀e
        let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
        exact .app (.var (.typeVarExt .head ane.symm)) <| τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
          |>.weakening Δa'a''wf (Δ'' := .typeExt .empty ..)
      simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
      let Blc := ρ₀ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
      let B'lc := ρ₁ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
      rw [Blc.TypeVar_open_id, B'lc.TypeVar_open_id]
      rw [Blc.Type_open_id, B'lc.Type_open_id] at this
      let A'lc := τke' a aninI' |>.soundness Γcw Γawe κ₁e
        |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
      let A''lc := τke'' a aninI'' |>.soundness Γcw Γawe κ₁e
        |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
      rw [τke a aninI |>.soundness Γcw Γawe κ₁e
            |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
            |>.TypeVar_open_id, A'lc.TypeVar_open_id, A''lc.TypeVar_open_id]
      apply this.equiv
      apply TypeEquivalence.arr
      · apply TypeEquivalence.prod
        apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
        · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'') _) .refl
          intro a anin
          let ⟨anina'ΔI, aninI''⟩ := List.not_mem_append'.mp anin
          let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
          simp [Type.TypeVar_open]
          rw [τke _ aninI |>.deterministic (τke'' _ aninI'') |>.right]
          apply TypeEquivalence.app .refl
          rw [Type.Type_open_var, A''lc.TypeVar_open_id]
          refine .symm <|
            .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
              .var .head
          intro a'' a''nin
          let ⟨a''ninΔI'', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
          let ⟨a''ninΔ, a''ninI''⟩ := List.not_mem_append'.mp a''ninΔI''
          apply τke'' a'' a''ninI'' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
            (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
          exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
        · apply Kinding.lam <| I'' ++ ↑a' :: Γ.typeVarDom
          intro a anin
          let ⟨aninI'', aninaΓ⟩ := List.not_mem_append'.mp anin
          specialize τke'' a aninI''
          let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
          exact τke''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
            |>.soundness Γcw Γa'awe κ₁e
      · apply TypeEquivalence.prod
        apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
        · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I') _) .refl
          intro a anin
          let ⟨anina'ΔI, aninI'⟩ := List.not_mem_append'.mp anin
          let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
          simp [Type.TypeVar_open]
          rw [τke _ aninI |>.deterministic (τke' _ aninI') |>.right]
          apply TypeEquivalence.app .refl
          rw [Type.Type_open_var, A'lc.TypeVar_open_id]
          refine .symm <|
            .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
              .var .head
          intro a'' a''nin
          let ⟨a''ninΔI', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
          let ⟨a''ninΔ, a''ninI'⟩ := List.not_mem_append'.mp a''ninΔI'
          apply τke' a'' a''ninI' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
            (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
          exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
        · apply Kinding.lam <| I' ++ ↑a' :: Γ.typeVarDom
          intro a anin
          let ⟨aninI', aninaΓ⟩ := List.not_mem_append'.mp anin
          specialize τke' a aninI'
          let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
          exact τke'.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
            |>.soundness Γcw Γa'awe κ₁e
    · apply Typing.typeLam Γ.typeVarDom
      intro a' a'nin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
      let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
      let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
      rw [← Range.map_get!_eq (as := [_, _])] at Ety
      let πty := Ety.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
        |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      simp at πty
      have := πty.typeApp (B := [[λ aᵢ : K₀. a' A']]) <| by
        apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
        intro a'' a''nin
        let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
        let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
        simp [Type.TypeVar_open]
        let Γa''we := Γwe.typeExt a''ninΓ κ₀e
        let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
        exact .app (.var (.typeVarExt .head ane.symm)) <| τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
          |>.weakening Δa'a''wf (Δ'' := .typeExt .empty ..)
      simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
      let Blc := ρ₀ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
      let B'lc := ρ₁ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
      rw [Blc.TypeVar_open_id, B'lc.TypeVar_open_id]
      rw [Blc.Type_open_id, B'lc.Type_open_id] at this
      let A'lc := τke' a aninI' |>.soundness Γcw Γawe κ₁e
        |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
      let A''lc := τke'' a aninI'' |>.soundness Γcw Γawe κ₁e
        |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
      rw [τke a aninI |>.soundness Γcw Γawe κ₁e
            |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
            |>.TypeVar_open_id, A'lc.TypeVar_open_id, A''lc.TypeVar_open_id]
      apply this.equiv
      apply TypeEquivalence.arr
      · apply TypeEquivalence.sum
        apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
        · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I') _) .refl
          intro a anin
          let ⟨anina'ΔI, aninI'⟩ := List.not_mem_append'.mp anin
          let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
          simp [Type.TypeVar_open]
          rw [τke _ aninI |>.deterministic (τke' _ aninI') |>.right]
          apply TypeEquivalence.app .refl
          rw [Type.Type_open_var, A'lc.TypeVar_open_id]
          refine .symm <|
            .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
              .var .head
          intro a'' a''nin
          let ⟨a''ninΔI', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
          let ⟨a''ninΔ, a''ninI'⟩ := List.not_mem_append'.mp a''ninΔI'
          apply τke' a'' a''ninI' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
            (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
          exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
        · apply Kinding.lam <| I' ++ ↑a' :: Γ.typeVarDom
          intro a anin
          let ⟨aninI', aninaΓ⟩ := List.not_mem_append'.mp anin
          specialize τke' a aninI'
          let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
          exact τke'.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
            |>.soundness Γcw Γa'awe κ₁e
      · apply TypeEquivalence.sum
        apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
        · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'') _) .refl
          intro a anin
          let ⟨anina'ΔI, aninI''⟩ := List.not_mem_append'.mp anin
          let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
          simp [Type.TypeVar_open]
          rw [τke _ aninI |>.deterministic (τke'' _ aninI'') |>.right]
          apply TypeEquivalence.app .refl
          rw [Type.Type_open_var, A''lc.TypeVar_open_id]
          refine .symm <|
            .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
              .var .head
          intro a'' a''nin
          let ⟨a''ninΔI'', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
          let ⟨a''ninΔ, a''ninI''⟩ := List.not_mem_append'.mp a''ninΔI''
          apply τke'' a'' a''ninI'' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
            (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
          exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
        · apply Kinding.lam <| I'' ++ ↑a' :: Γ.typeVarDom
          intro a anin
          let ⟨aninI'', aninaΓ⟩ := List.not_mem_append'.mp anin
          specialize τke'' a aninI''
          let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
          exact τke''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
            |>.soundness Γcw Γa'awe κ₁e
  | liftConcat I concatce ρ₀ke τke κ₀e κ₁e ih =>
    rename «Type» => A_
    rename Environment => Δ
    rename_i Γ _ _ _ _ _ _ _ _ A K₀ K₁
    let .concat μke lift₀ke lift₁ke lift₂ke κ₁e' contain₀₂ke contain₁₂ke := ψke
    let .lift I' τke' κ₀e' ρ₀ke' (A := A') := lift₀ke
    let .lift I'' τke'' κ₀e'' ρ₁ke (A := A'') := lift₁ke
    let .lift I''' τke''' κ₀e''' ρ₂ke (A := A''') := lift₂ke
    let .contain μke' lift₀ke' lift₂ke' κ₁e'' := contain₀₂ke
    let .contain μke'' lift₁ke' lift₂ke'' κ₁e''' := contain₁₂ke
    let .lift I'''' τke'''' κ₀e'''' ρ₀ke'' (A := A'''') := lift₀ke'
    let .lift I''''' τke''''' κ₀e''''' ρ₂ke' (A := A''''') := lift₂ke'
    let .lift I'''''' τke'''''' κ₀e'''''' ρ₁ke' (A := A'''''') := lift₁ke'
    let .lift I''''''' τke''''''' κ₀e''''''' ρ₂ke'' (A := A''''''') := lift₂ke''
    rcases μke.deterministic μke' with ⟨_, rfl⟩
    rcases μke.deterministic μke'' with ⟨_, rfl⟩
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨_, rfl⟩
    rcases ρ₀ke.deterministic ρ₀ke'' with ⟨_, rfl⟩
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨_, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke'' with ⟨_, rfl⟩
    cases κ₀e.deterministic κ₀e'
    cases κ₀e.deterministic κ₀e''
    cases κ₀e.deterministic κ₀e'''
    cases κ₀e.deterministic κ₀e''''
    cases κ₀e.deterministic κ₀e'''''
    cases κ₀e.deterministic κ₀e''''''
    cases κ₀e.deterministic κ₀e'''''''
    let ⟨a, anin⟩ := Γ.typeVarDom ++ I ++ I' ++ I'' ++ I''' ++ I'''' ++ I''''' ++ I'''''' ++
      I''''''' |>.exists_fresh
    let ⟨anin', aninI'''''''⟩ := List.not_mem_append'.mp anin
    let ⟨anin'', aninI''''''⟩ := List.not_mem_append'.mp anin'
    let ⟨anin''', aninI'''''⟩ := List.not_mem_append'.mp anin''
    let ⟨anin'''', aninI''''⟩ := List.not_mem_append'.mp anin'''
    let ⟨anin''''', aninI'''⟩ := List.not_mem_append'.mp anin''''
    let ⟨anin'''''', aninI''⟩ := List.not_mem_append'.mp anin'''''
    let ⟨anin''''''', aninI'⟩ := List.not_mem_append'.mp anin''''''
    let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin'''''''
    let Γawe := Γwe.typeExt aninΓ κ₀e
    rcases τke _ aninI |>.deterministic <| τke' _ aninI' with ⟨rfl, _⟩
    rcases τke _ aninI |>.deterministic <| τke'''' _ aninI'''' with ⟨rfl, _⟩
    rcases τke _ aninI |>.deterministic <| τke'''''' _ aninI'''''' with ⟨rfl, _⟩
    cases κ₁e.deterministic κ₁e'
    cases κ₁e.deterministic κ₁e''
    cases κ₁e.deterministic κ₁e'''
    let Ety := ih
      (.concat μke ρ₀ke ρ₁ke ρ₂ke κ₀e (.contain μke ρ₀ke ρ₂ke κ₀e) (.contain μke ρ₁ke ρ₂ke κ₀e))
      Γᵢw Γcw Γwe
    let Alc := τke a aninI |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A'lc := τke' a aninI' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A''lc := τke'' a aninI'' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A'''lc := τke''' a aninI''' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A''''lc := τke'''' a aninI'''' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A'''''lc := τke''''' a aninI''''' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A''''''lc := τke'''''' a aninI'''''' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let A'''''''lc := τke''''''' a aninI''''''' |>.soundness Γcw Γawe κ₁e
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.le.refl
    let Blc := ρ₀ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
    let B'lc := ρ₁ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
    let B''lc := ρ₂ke.soundness Γcw Γwe κ₀e.row |>.TypeVarLocallyClosed_of
    let Δwf := Γwe.soundness Γcw
    apply Typing.quadruple
    · apply Typing.typeLam Γ.typeVarDom
      intro a' a'nin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
      let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
      let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
      rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
      let πty := Ety.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩ (b := false)
        |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      simp at πty
      have := πty.typeApp (B := [[λ aᵢ : K₀. a' A]]) <| by
        apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
        intro a'' a''nin
        let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
        let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
        simp [Type.TypeVar_open]
        let Γa''we := Γwe.typeExt a''ninΓ κ₀e
        let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
        exact .app (.var (.typeVarExt .head ane.symm)) <|
          τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
          |>.weakening Δa'a''wf (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)
      simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
      rw [Blc.TypeVar_open_id, B'lc.TypeVar_open_id, B''lc.TypeVar_open_id, Alc.TypeVar_open_id,
          A'lc.TypeVar_open_id, A''lc.TypeVar_open_id, A'''lc.TypeVar_open_id]
      rw [Blc.Type_open_id, B'lc.Type_open_id, B''lc.Type_open_id] at this
      apply this.equiv
      apply TypeEquivalence.arr
      · apply TypeEquivalence.prod
        apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
        · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I') _) .refl
          intro a anin
          let ⟨anina'ΔI, aninI'⟩ := List.not_mem_append'.mp anin
          let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
          simp [Type.TypeVar_open]
          rw [τke _ aninI |>.deterministic (τke' _ aninI') |>.right]
          apply TypeEquivalence.app .refl
          rw [Type.Type_open_var, A'lc.TypeVar_open_id]
          refine .symm <|
            .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
              .var .head
          intro a'' a''nin
          let ⟨a''ninΔI', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
          let ⟨a''ninΔ, a''ninI'⟩ := List.not_mem_append'.mp a''ninΔI'
          apply τke' a'' a''ninI' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
            (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
          exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
        · apply Kinding.lam <| I' ++ ↑a' :: Γ.typeVarDom
          intro a anin
          let ⟨aninI', aninaΓ⟩ := List.not_mem_append'.mp anin
          specialize τke' a aninI'
          let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
          exact τke'.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
            |>.soundness Γcw Γa'awe κ₁e
      · apply TypeEquivalence.arr
        · apply TypeEquivalence.prod
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke'' _ aninI'') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
                .var .head
            intro a'' a''nin
            let ⟨a''ninΔI'', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI''⟩ := List.not_mem_append'.mp a''ninΔI''
            apply τke'' a'' a''ninI'' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
              (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I'' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI'', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke'' a aninI''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
              |>.soundness Γcw Γa'awe κ₁e
        · apply TypeEquivalence.prod
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI'''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke''' _ aninI''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A'''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I''' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
                .var .head
            intro a'' a''nin
            let ⟨a''ninΔI''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI'''⟩ := List.not_mem_append'.mp a''ninΔI'''
            apply τke''' a'' a''ninI''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e |>.weakening
              (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke''' a aninI'''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke'''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
              |>.soundness Γcw Γa'awe κ₁e
    · apply Typing.typeLam Γ.typeVarDom
      intro a' a'nin
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
      rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
      let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
      let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
      rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
      let πty := Ety.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩ (b := false)
        |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      simp at πty
      have := πty.typeApp (B := [[λ aᵢ : K₀. a' A]]) <| by
        apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
        intro a'' a''nin
        let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
        let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
        simp [Type.TypeVar_open]
        let Γa''we := Γwe.typeExt a''ninΓ κ₀e
        let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
        exact .app (.var (.typeVarExt .head ane.symm)) <|
          τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
          |>.weakening Δa'a''wf (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)
      simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
      rw [Blc.weaken (n := 1).TypeVar_open_id, B'lc.weaken (n := 1).TypeVar_open_id,
          B''lc.weaken (n := 1).TypeVar_open_id, Alc.TypeVar_open_id,
          A'lc.weaken (n := 1).TypeVar_open_id, A''lc.weaken (n := 1).TypeVar_open_id,
          A'''lc.weaken (n := 1).TypeVar_open_id]
      rw [Blc.weaken (n := 1).Type_open_id, B'lc.weaken (n := 1).Type_open_id,
          B''lc.weaken (n := 1).Type_open_id] at this
      apply this.equiv
      apply TypeEquivalence.scheme <| a' :: Γ.typeVarDom
      intro a'' a''nin
      simp [«F⊗⊕ω».Type.TypeVar_open]
      rw [Alc.TypeVar_open_id, A'lc.TypeVar_open_id, A''lc.TypeVar_open_id, A'''lc.TypeVar_open_id]
      apply TypeEquivalence.arr
      · apply TypeEquivalence.arr (.sum _) .refl
        apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
        · apply TypeEquivalence.listApp (.lam ((a'' :: a' :: Δ.typeVarDom) ++ ↑I ++ ↑I') _) .refl
          intro a anin
          let ⟨anina'ΔI, aninI'⟩ := List.not_mem_append'.mp anin
          let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
          simp [Type.TypeVar_open]
          rw [τke _ aninI |>.deterministic (τke' _ aninI') |>.right]
          apply TypeEquivalence.app .refl
          rw [Type.Type_open_var, A'lc.TypeVar_open_id]
          refine .symm <|
            .lamApp (.lam ((a :: a'' :: a' :: Δ.typeVarDom) ++ ↑I' ++ ↑Γ.typeVarDom) ?_)
              (K₂ := K₁) <| .var .head
          intro a''' a'''nin
          let ⟨a'''ninΔI', a'''ninΓ⟩ := List.not_mem_append'.mp a'''nin
          let ⟨a'''ninΔ, a'''ninI'⟩ := List.not_mem_append'.mp a'''ninΔI'
          apply τke' a''' a'''ninI' |>.soundness Γcw (Γwe.typeExt a'''ninΓ κ₀e) κ₁e |>.weakening
            (Δ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..) (Δ'' := .typeExt .empty ..)
          exact Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt a''nin .star |>.soundness Γcw
            |>.typeVarExt anina'Δ |>.typeVarExt a'''ninΔ
        · apply Kinding.lam <| I' ++ ↑a'' :: ↑a' :: Γ.typeVarDom
          intro a''' a'''nin
          let ⟨a'''ninI', a'''ninaΓ⟩ := List.not_mem_append'.mp a'''nin
          specialize τke' a''' a'''ninI'
          let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt a''nin .star |>.typeExt
            a'''ninaΓ κ₀e
          exact τke'.weakening Γa'awe (Γ' := .typeExt (.typeExt .empty ..) ..)
            (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
      · apply TypeEquivalence.arr
        · apply TypeEquivalence.arr (.sum _) .refl
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a'' :: a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke'' _ aninI'') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a'' :: a' :: Δ.typeVarDom) ++ ↑I'' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a''' a'''nin
            let ⟨a'''ninΔI'', a'''ninΓ⟩ := List.not_mem_append'.mp a'''nin
            let ⟨a'''ninΔ, a'''ninI''⟩ := List.not_mem_append'.mp a'''ninΔI''
            apply τke'' a''' a'''ninI'' |>.soundness Γcw (Γwe.typeExt a'''ninΓ κ₀e) κ₁e |>.weakening
              (Δ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..) (Δ'' := .typeExt .empty ..)
            exact Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt a''nin .star |>.soundness Γcw
              |>.typeVarExt anina'Δ |>.typeVarExt a'''ninΔ
          · apply Kinding.lam <| I'' ++ ↑a'' :: ↑a' :: Γ.typeVarDom
            intro a''' a'''nin
            let ⟨a'''ninI'', a'''ninaΓ⟩ := List.not_mem_append'.mp a'''nin
            specialize τke'' a''' a'''ninI''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt a''nin .star |>.typeExt
              a'''ninaΓ κ₀e
            exact τke''.weakening Γa'awe (Γ' := .typeExt (.typeExt .empty ..) ..)
              (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
        · apply TypeEquivalence.arr (.sum _) .refl
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a'' :: a' :: Δ.typeVarDom) ++ ↑I ++ ↑I''') _)
              .refl
            intro a anin
            let ⟨anina'ΔI, aninI'''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke''' _ aninI''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A'''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a'' :: a' :: Δ.typeVarDom) ++ ↑I''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a''' a'''nin
            let ⟨a'''ninΔI''', a'''ninΓ⟩ := List.not_mem_append'.mp a'''nin
            let ⟨a'''ninΔ, a'''ninI'''⟩ := List.not_mem_append'.mp a'''ninΔI'''
            apply τke''' a''' a'''ninI''' |>.soundness Γcw (Γwe.typeExt a'''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..)
                (Δ'' := .typeExt .empty ..)
            exact Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt a''nin .star |>.soundness Γcw
              |>.typeVarExt anina'Δ |>.typeVarExt a'''ninΔ
          · apply Kinding.lam <| I''' ++ ↑a'' :: ↑a' :: Γ.typeVarDom
            intro a''' a'''nin
            let ⟨a'''ninI''', a'''ninaΓ⟩ := List.not_mem_append'.mp a'''nin
            specialize τke''' a''' a'''ninI'''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt a''nin .star |>.typeExt
              a'''ninaΓ κ₀e
            exact τke'''.weakening Γa'awe (Γ' := .typeExt (.typeExt .empty ..) ..)
              (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
    · apply Typing.pair
      · apply Typing.typeLam Γ.typeVarDom
        intro a' a'nin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
        let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
        let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
        rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
        let πty := Ety.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
          (b := false)
        simp at πty
        rw [← Range.map_get!_eq (as := [_, _])] at πty
        let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp at π'ty
        have := π'ty.typeApp (B := [[λ aᵢ : K₀. a' A]]) <| by
          apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
          intro a'' a''nin
          let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
          let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
          simp [Type.TypeVar_open]
          let Γa''we := Γwe.typeExt a''ninΓ κ₀e
          let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
          exact .app (.var (.typeVarExt .head ane.symm)) <|
            τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
            |>.weakening Δa'a''wf (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)
        simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
        rw [Blc.TypeVar_open_id, B''lc.TypeVar_open_id, Alc.TypeVar_open_id,
            A''''lc.TypeVar_open_id, A'''''lc.TypeVar_open_id]
        rw [Blc.Type_open_id, B''lc.Type_open_id] at this
        apply this.equiv
        apply TypeEquivalence.arr
        · apply TypeEquivalence.prod
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I''''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI'''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke''''' _ aninI''''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A'''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I''''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a'' a''nin
            let ⟨a''ninΔI''''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI'''''⟩ := List.not_mem_append'.mp a''ninΔI'''''
            apply τke''''' a'' a''ninI''''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I''''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI''''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke''''' a aninI'''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke'''''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
              |>.soundness Γcw Γa'awe κ₁e
        · apply TypeEquivalence.prod
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke'''' _ aninI'''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'''' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
                .var .head
            intro a'' a''nin
            let ⟨a''ninΔI'''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI''''⟩ := List.not_mem_append'.mp a''ninΔI''''
            apply τke'''' a'' a''ninI'''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I'''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI'''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke'''' a aninI''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke''''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
              |>.soundness Γcw Γa'awe κ₁e
      · apply Typing.typeLam Γ.typeVarDom
        intro a' a'nin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
        let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
        let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
        rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
        let πty := Ety.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
          (b := false)
        simp at πty
        rw [← Range.map_get!_eq (as := [_, _])] at πty
        let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp at π'ty
        have := π'ty.typeApp (B := [[λ aᵢ : K₀. a' A]]) <| by
          apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
          intro a'' a''nin
          let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
          let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
          simp [Type.TypeVar_open]
          let Γa''we := Γwe.typeExt a''ninΓ κ₀e
          let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
          exact .app (.var (.typeVarExt .head ane.symm)) <|
            τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
            |>.weakening Δa'a''wf (Δ'' := .typeExt .empty ..)
        simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
        rw [Blc.TypeVar_open_id, B''lc.TypeVar_open_id, Alc.TypeVar_open_id,
            A''''lc.TypeVar_open_id, A'''''lc.TypeVar_open_id]
        rw [Blc.Type_open_id, B''lc.Type_open_id] at this
        apply this.equiv
        apply TypeEquivalence.arr
        · apply TypeEquivalence.sum
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke'''' _ aninI'''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'''' ++ ↑Γ.typeVarDom) ?_) (K₂ := K₁) <|
                .var .head
            intro a'' a''nin
            let ⟨a''ninΔI'''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI''''⟩ := List.not_mem_append'.mp a''ninΔI''''
            apply τke'''' a'' a''ninI'''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I'''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI'''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke'''' a aninI''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke''''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
              |>.soundness Γcw Γa'awe κ₁e
        · apply TypeEquivalence.sum
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I''''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI'''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke''''' _ aninI''''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A'''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I''''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a'' a''nin
            let ⟨a''ninΔI''''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI'''''⟩ := List.not_mem_append'.mp a''ninΔI'''''
            apply τke''''' a'' a''ninI''''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I''''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI''''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke''''' a aninI'''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke'''''.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
              |>.soundness Γcw Γa'awe κ₁e
    · apply Typing.pair
      · apply Typing.typeLam Γ.typeVarDom
        intro a' a'nin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
        let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
        let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
        rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
        let πty := Ety.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
          (b := false)
        simp at πty
        rw [← Range.map_get!_eq (as := [_, _])] at πty
        let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
          |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp at π'ty
        have := π'ty.typeApp (B := [[λ aᵢ : K₀. a' A]]) <| by
          apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
          intro a'' a''nin
          let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
          let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
          simp [Type.TypeVar_open]
          let Γa''we := Γwe.typeExt a''ninΓ κ₀e
          let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
          exact .app (.var (.typeVarExt .head ane.symm)) <|
            τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
            |>.weakening Δa'a''wf (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)
        simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
        rw [B'lc.TypeVar_open_id, B''lc.TypeVar_open_id]
        rw [B'lc.Type_open_id, B''lc.Type_open_id] at this
        rw [Alc.TypeVar_open_id, A''''''lc.TypeVar_open_id, A'''''''lc.TypeVar_open_id]
        apply this.equiv
        apply TypeEquivalence.arr
        · apply TypeEquivalence.prod
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I''''''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI'''''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke''''''' _ aninI''''''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A'''''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I''''''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a'' a''nin
            let ⟨a''ninΔI''''''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI'''''''⟩ := List.not_mem_append'.mp a''ninΔI'''''''
            apply τke''''''' a'' a''ninI''''''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I''''''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI''''''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke''''''' a aninI'''''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke'''''''.weakening Γa'awe (Γ' := .typeExt .empty ..)
              (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
        · apply TypeEquivalence.prod
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'''''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI''''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke'''''' _ aninI'''''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A''''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'''''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a'' a''nin
            let ⟨a''ninΔI'''''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI''''''⟩ := List.not_mem_append'.mp a''ninΔI''''''
            apply τke'''''' a'' a''ninI'''''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I'''''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI'''''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke'''''' a aninI''''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke''''''.weakening Γa'awe (Γ' := .typeExt .empty ..)
              (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
      · apply Typing.typeLam Γ.typeVarDom
        intro a' a'nin
        simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Type.TypeVar_open]
        rw [Ety.TermTypeVarLocallyClosed_of.TypeVar_open_id]
        let Γa'we := Γwe.typeExt a'nin <| .arr κ₁e .star
        let Δa'wf := Δwf.typeVarExt (Γwe.TypeVarNotInDom_preservation a'nin) (K := [[(K₁ ↦ *)]])
        rw [← Range.map_get!_eq (as := [_, _, _, _])] at Ety
        let πty := Ety.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
          (b := false)
        simp at πty
        rw [← Range.map_get!_eq (as := [_, _])] at πty
        let π'ty := πty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩ (b := false)
          |>.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        simp at π'ty
        have := π'ty.typeApp (B := [[λ aᵢ : K₀. a' A]]) <| by
          apply Kinding.lam <| I ++ ↑a' :: Γ.typeVarDom
          intro a'' a''nin
          let ⟨a''ninI, a''nina'Γ⟩ := List.not_mem_append'.mp a''nin
          let ⟨ane, a''ninΓ⟩ := List.not_mem_cons.mp a''nina'Γ
          simp [Type.TypeVar_open]
          let Γa''we := Γwe.typeExt a''ninΓ κ₀e
          let Δa'a''wf := Δa'wf.typeVarExt (Γa'we.TypeVarNotInDom_preservation a''nina'Γ) (K := K₀)
          exact .app (.var (.typeVarExt .head ane.symm)) <|
            τke _ a''ninI |>.soundness Γcw Γa''we κ₁e
            |>.weakening Δa'a''wf (Δ'' := .typeExt .empty ..)
        simp [«F⊗⊕ω».Term.Type_open, «F⊗⊕ω».Type.Type_open] at this
        rw [B'lc.TypeVar_open_id, B''lc.TypeVar_open_id]
        rw [B'lc.Type_open_id, B''lc.Type_open_id] at this
        rw [Alc.TypeVar_open_id, A''''''lc.TypeVar_open_id, A'''''''lc.TypeVar_open_id]
        apply this.equiv
        apply TypeEquivalence.arr
        · apply TypeEquivalence.sum
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I'''''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI''''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke'''''' _ aninI'''''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A''''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I'''''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a'' a''nin
            let ⟨a''ninΔI'''''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI''''''⟩ := List.not_mem_append'.mp a''ninΔI''''''
            apply τke'''''' a'' a''ninI'''''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I'''''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI'''''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke'''''' a aninI''''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke''''''.weakening Γa'awe (Γ' := .typeExt .empty ..)
              (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
        · apply TypeEquivalence.sum
          apply TypeEquivalence.trans _ <| .symm <| .listAppComp .var_free _ (K₁ := K₀) (K₂ := K₁)
          · apply TypeEquivalence.listApp (.lam ((a' :: Δ.typeVarDom) ++ ↑I ++ ↑I''''''') _) .refl
            intro a anin
            let ⟨anina'ΔI, aninI'''''''⟩ := List.not_mem_append'.mp anin
            let ⟨anina'Δ, aninI⟩ := List.not_mem_append'.mp anina'ΔI
            simp [Type.TypeVar_open]
            rw [τke _ aninI |>.deterministic (τke''''''' _ aninI''''''') |>.right]
            apply TypeEquivalence.app .refl
            rw [Type.Type_open_var, A'''''''lc.TypeVar_open_id]
            refine .symm <|
              .lamApp (.lam ((a :: a' :: Δ.typeVarDom) ++ ↑I''''''' ++ ↑Γ.typeVarDom) ?_)
                (K₂ := K₁) <| .var .head
            intro a'' a''nin
            let ⟨a''ninΔI''''''', a''ninΓ⟩ := List.not_mem_append'.mp a''nin
            let ⟨a''ninΔ, a''ninI'''''''⟩ := List.not_mem_append'.mp a''ninΔI'''''''
            apply τke''''''' a'' a''ninI''''''' |>.soundness Γcw (Γwe.typeExt a''ninΓ κ₀e) κ₁e
              |>.weakening (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
            exact Δa'wf.typeVarExt anina'Δ |>.typeVarExt a''ninΔ
          · apply Kinding.lam <| I''''''' ++ ↑a' :: Γ.typeVarDom
            intro a anin
            let ⟨aninI''''''', aninaΓ⟩ := List.not_mem_append'.mp anin
            specialize τke''''''' a aninI'''''''
            let Γa'awe := Γwe.typeExt a'nin (κ₁e.arr .star) |>.typeExt aninaΓ κ₀e
            exact τke'''''''.weakening Γa'awe (Γ' := .typeExt .empty ..)
              (Γ'' := .typeExt .empty ..) |>.soundness Γcw Γa'awe κ₁e
  | TCInst γᵢin τ'ke ψce ψopih =>
    rename_i o κ l ψ τ E n E' _ _ Γ τ' B F _
    let .tc γcin τopke (A := A') (A' := A''') := ψke
    let ⟨_, A'', _, _, _, _, B', A, _, γcin', ψke, τke, κ₁e, Ety, E'ty⟩ := Γᵢw.In_inversion Γcw γᵢin
    rcases ClassEnvironmentEntry.mk.inj <| γcin.deterministic γcin' rfl with
      ⟨TC'A''eq, _, rfl, rfl, rfl, rfl⟩
    let neq : List.length (Range.map ..) = List.length _ := by rw [TC'A''eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at neq
    cases neq
    apply Typing.prodIntro' (Γwe.soundness Γcw) _ (b := false) (.inl (by
      rw [List.length_cons]
      nofun
    )) <| by
      rw [List.length_cons, List.length_cons, List.length_map, Range.length_toList, List.length_map,
          Range.length_toList]
    let ψopke i mem : TypeScheme.KindingAndElaboration .. := by
      let ⟨a, ainj, anin⟩ := (ψ i).freeTypeVars ++
        ([:o].map (Monotype.freeTypeVars ∘ τ')).flatten ++
        ↑([:o].map (Type.freeTypeVars ∘ B)).flatten ++
        ↑(B' i).freeTypeVars ++ Γ.typeVarDom |>.exists_fresh_inj
      let aninψτ'BB' i := List.not_mem_append'.mp (anin i) |>.left
      let aninΓ i := List.not_mem_append'.mp (anin i) |>.right
      let aninψτ'B i := List.not_mem_append'.mp (aninψτ'BB' i) |>.left
      let aninB' i := List.not_mem_append'.mp (aninψτ'BB' i) |>.right
      let aninψτ' i := List.not_mem_append'.mp (aninψτ'B i) |>.left
      let aninB i := List.not_mem_append'.mp (aninψτ'B i) |>.right
      let aninψ i := List.not_mem_append'.mp (aninψτ' i) |>.left
      let aninτ' i := List.not_mem_append'.mp (aninψτ' i) |>.right
      let Γawe := Γwe.multiTypeExt aninΓ ainj κ₁e
      rw [← TypeEnvironment.append_empty (.multiTypeExt ..),
          TypeEnvironment.multiTypeExt_eq_append (Γ' := .empty),
          TypeEnvironment.append_empty, ← TypeEnvironment.empty_append (.append ..)] at Γawe
      specialize ψke i mem ⟨a, ainj⟩
      rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at ψke
      let ψke' := ψke.weakening Γawe (Γ := .empty) (Γ' := Γ) (Γ'' := .multiTypeExt .empty ..)
      rw [TypeEnvironment.empty_append, ← TypeEnvironment.append_empty (.multiTypeExt ..),
          ← TypeEnvironment.multiTypeExt_eq_append (Γ' := .empty),
          TypeEnvironment.append_empty] at ψke'
      apply ψke'.Monotype_multi_open Γcw Γwe (Γ' := .empty) _ (fun i _ => aninψ i) _
        (fun i _ => aninB' i) _ τ'ke
      · intro _ _
        rw [TypeEnvironment.append_empty]
        exact aninΓ _
      · intro i mem j lt
        apply List.not_mem_flatten.mp <| aninτ' _
        exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
      · intro i mem j lt
        apply List.not_mem_flatten.mp <| aninB _
        exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
    let ⟨a, ainj, anin⟩ := τ.freeTypeVars ++
      ([:o].map (Monotype.freeTypeVars ∘ τ')).flatten ++
      ↑A.freeTypeVars ++
      ↑A'.freeTypeVars ++
      ↑([:n].map (Type.freeTypeVars ∘ A''')).flatten ++
      ↑([:o].map (Type.freeTypeVars ∘ B)).flatten ++
      ↑([:l].map (Type.freeTypeVars ∘ B')).flatten ++
      ↑E.freeTypeVars ++
      ↑([:n].map («F⊗⊕ω».Term.freeTypeVars ∘ E')).flatten ++
      Γ.typeVarDom |>.exists_fresh_inj
    let aninττ'AA'A'''BB'EE' i := List.not_mem_append'.mp (anin i) |>.left
    let aninΓ i := List.not_mem_append'.mp (anin i) |>.right
    let aninττ'AA'A'''BB'E i := List.not_mem_append'.mp (aninττ'AA'A'''BB'EE' i) |>.left
    let aninE' i := List.not_mem_append'.mp (aninττ'AA'A'''BB'EE' i) |>.right
    let aninττ'AA'A'''BB' i := List.not_mem_append'.mp (aninττ'AA'A'''BB'E i) |>.left
    let aninE i := List.not_mem_append'.mp (aninττ'AA'A'''BB'E i) |>.right
    let aninττ'AA'A'''B i := List.not_mem_append'.mp (aninττ'AA'A'''BB' i) |>.left
    let aninB' i := List.not_mem_append'.mp (aninττ'AA'A'''BB' i) |>.right
    let aninττ'AA'A''' i := List.not_mem_append'.mp (aninττ'AA'A'''B i) |>.left
    let aninB i := List.not_mem_append'.mp (aninττ'AA'A'''B i) |>.right
    let aninττ'AA' i := List.not_mem_append'.mp (aninττ'AA'A''' i) |>.left
    let aninA''' i := List.not_mem_append'.mp (aninττ'AA'A''' i) |>.right
    let aninττ'A i := List.not_mem_append'.mp (aninττ'AA' i) |>.left
    let aninA' i := List.not_mem_append'.mp (aninττ'AA' i) |>.right
    let aninττ' i := List.not_mem_append'.mp (aninττ'A i) |>.left
    let aninA i := List.not_mem_append'.mp (aninττ'A i) |>.right
    let aninτ i := List.not_mem_append'.mp (aninττ' i) |>.left
    let aninτ' i := List.not_mem_append'.mp (aninττ' i) |>.right
    let Γawe := Γwe.multiTypeExt aninΓ ainj κ₁e
    rw [← TypeEnvironment.append_empty (.multiTypeExt ..),
        TypeEnvironment.multiTypeExt_eq_append (Γ' := .empty),
        TypeEnvironment.append_empty, ← TypeEnvironment.empty_append (.append ..)] at Γawe
    specialize τke ⟨a, ainj⟩
    rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at τke
    let τke' := τke.weakening Γawe (Γ := .empty) (Γ' := Γ) (Γ'' := .multiTypeExt .empty ..)
    let ψke' i mem := by
      have := ψke i mem ⟨a, ainj⟩
      rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at this
      exact this.weakening Γawe (Γ := .empty) (Γ' := Γ) (Γ'' := .multiTypeExt .empty ..)
    rw [TypeEnvironment.empty_append] at τke' ψke' Γawe
    rw [← TypeEnvironment.append_empty (.multiTypeExt ..),
        ← TypeEnvironment.multiTypeExt_eq_append (Γ' := .empty),
        TypeEnvironment.append_empty] at τke' ψke'
    let ψopke' i mem := ψopke i mem |>.weakening Γawe
    rw [TypeEnvironment.append_empty] at ψopke'
    rw [← TypeEnvironment.append_empty (.multiTypeExt ..),
        ← TypeEnvironment.multiTypeExt_eq_append (Γ' := .empty),
        TypeEnvironment.append_empty] at ψopke' Γawe
    let τopke' := τke'.Monotype_multi_open Γcw Γwe
      (fun i _ => by rw [TypeEnvironment.append]; exact aninΓ i) (fun i _ => aninτ i) (by
        intro i _ j lt
        apply List.not_mem_flatten.mp <| aninτ' _
        exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
      ) (fun i _ => aninA i) (by
        intro i mem j lt
        apply List.not_mem_flatten.mp <| aninB _
        exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
      ) τ'ke (Γ' := .empty)
    rcases τopke.deterministic τopke' with ⟨_, rfl⟩
    let ⟨x, xinj, xnin⟩ := ↑E.freeTermVars ++
      ↑([:n].map («F⊗⊕ω».Term.freeTermVars ∘ E')).flatten ++
      ↑([:l].map («F⊗⊕ω».Term.freeTermVars ∘ F)).flatten ++
      [[Γ,, </ a@i : κ@i // i in [:o] />]].termVarDom |>.exists_fresh_inj
    let xninEE'F i := List.not_mem_append'.mp (xnin i) |>.left
    let xninΓ i := List.not_mem_append'.mp (xnin i) |>.right
    let xninEE' i := List.not_mem_append'.mp (xninEE'F i) |>.left
    let xninF i := List.not_mem_append'.mp (xninEE'F i) |>.right
    let xninE i := List.not_mem_append'.mp (xninEE' i) |>.left
    let xninE' i := List.not_mem_append'.mp (xninEE' i) |>.right
    let xninF' : ∀ i, ∀ j ∈ [:l], x i ∉ (F j).freeTermVars := by
      intro i j mem
      exact List.not_mem_flatten.mp (xninF i) _ <| Range.mem_map_of_mem mem
    let Γaxwe := Γawe.multiConstrExt xninΓ xinj ψke'
    intro EA mem
    cases mem
    · simp only
      apply Typing.Term_multi_open (Δ' := .empty) (B := fun i => (B' i).Type_multi_open B o)
      · rw [Environment.multiTermExt_eq_append, Term.Type_multi_open_TermVar_multi_open_comm,
            Environment.multiTermExt_Type_multi_open_TypeVar_multi_subst_TypeVar_multi_open (by
                intro i _ j lt
                apply List.not_mem_flatten.mp <| aninB' _
                exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
              ) (by
                intro i _ j lt
                apply List.not_mem_flatten.mp <| aninB _
                exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
              ) ainj (by
                intro i lt
                let mem : i ∈ [:o] := ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
                exact τ'ke _ mem |>.soundness Γcw Γwe (κ₁e _ mem) |>.TypeVarLocallyClosed_of
              )]
        apply Typing.Type_open_Type_multi_open
        · specialize Ety ⟨a, ainj⟩ ⟨x, xinj⟩
          let Δaxwf := Γaxwe.soundness Γcw
          rw [← Environment.append_empty (.multiTermExt ..),
              ← Environment.append_empty (.multiTypeExt ..),
              Environment.multiTermExt_eq_append (Δ' := .empty),
              Environment.multiTypeExt_eq_append (Δ' := .empty),
              Environment.append_empty, ← Environment.empty_append (.append ..),
              ← Environment.append_assoc, ← Environment.multiTermExt_eq_append,
              Environment.append_empty] at Δaxwf
          rw [← Environment.empty_append (.multiTermExt ..)] at Ety
          let Ety' := Ety.weakening Δaxwf (Δ := .empty) (Δ' := Δ)
            (Δ'' := .multiTermExt (.multiTypeExt ..) ..)
          rw [Environment.empty_append, ← Environment.append_empty (.multiTermExt ..),
              Environment.multiTermExt_eq_append, ← Environment.multiTypeExt_eq_append,
              Environment.append_empty] at Ety'
          exact Ety'
        · intro i
          exact «F⊗⊕ω».Term.not_mem_freeTypeVars_TermVar_multi_open_intro <| aninE _
        · exact aninA'
        · exact aninA
        · intro i j mem
          apply List.not_mem_flatten.mp <| aninB _
          exact Range.mem_map_of_mem mem
        · exact ainj
        · intro i mem
          exact τ'ke i mem |>.soundness Γcw Γwe <| κ₁e i mem
      · intro i
        exact «F⊗⊕ω».Term.not_mem_freeTermVars_Type_multi_open_intro <| xninE _
      · exact xninF'
      · exact xinj
      · intro _ mem
        exact ψopih _ mem (ψopke _ mem) Γᵢw Γcw Γwe
    · case _ mem =>
      rcases Range.mem_zip_map mem with ⟨i, mem', rfl⟩
      simp only
      apply Typing.Term_multi_open (Δ' := .empty) (B := fun i => (B' i).Type_multi_open B o)
      · rw [Environment.multiTermExt_eq_append, Term.Type_multi_open_TermVar_multi_open_comm,
            Environment.multiTermExt_Type_multi_open_TypeVar_multi_subst_TypeVar_multi_open (by
                intro i _ j lt
                apply List.not_mem_flatten.mp <| aninB' _
                exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
              ) (by
                intro i _ j lt
                apply List.not_mem_flatten.mp <| aninB _
                exact Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
              ) ainj (by
                intro i lt
                let mem : i ∈ [:o] := ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
                exact τ'ke _ mem |>.soundness Γcw Γwe (κ₁e _ mem) |>.TypeVarLocallyClosed_of
              )]
        apply Typing.Type_open_Type_multi_open
        · specialize E'ty _ mem' ⟨a, ainj⟩ ⟨x, xinj⟩
          let Δaxwf := Γaxwe.soundness Γcw
          rw [← Environment.append_empty (.multiTermExt ..),
              ← Environment.append_empty (.multiTypeExt ..),
              Environment.multiTermExt_eq_append (Δ' := .empty),
              Environment.multiTypeExt_eq_append (Δ' := .empty),
              Environment.append_empty, ← Environment.empty_append (.append ..),
              ← Environment.append_assoc, ← Environment.multiTermExt_eq_append,
              Environment.append_empty] at Δaxwf
          rw [← Environment.empty_append (.multiTermExt ..)] at E'ty
          let E'ty' := E'ty.weakening Δaxwf (Δ := .empty) (Δ' := Δ)
            (Δ'' := .multiTermExt (.multiTypeExt ..) ..)
          rw [Environment.empty_append, ← Environment.append_empty (.multiTermExt ..),
              Environment.multiTermExt_eq_append, ← Environment.multiTypeExt_eq_append,
              Environment.append_empty] at E'ty'
          rw [And.right <| ClassEnvironmentEntrySuper.mk.inj <|
                Range.eq_of_mem_of_map_eq TC'A''eq _ mem']
          exact E'ty'
        · intro i
          apply «F⊗⊕ω».Term.not_mem_freeTypeVars_TermVar_multi_open_intro
          exact List.not_mem_flatten.mp (aninE' _) _ <| Range.mem_map_of_mem mem'
        · intro i
          exact List.not_mem_flatten.mp (aninA''' _) _ <| Range.mem_map_of_mem mem'
        · exact aninA
        · intro i j mem
          apply List.not_mem_flatten.mp <| aninB _
          exact Range.mem_map_of_mem mem
        · exact ainj
        · intro i mem
          exact τ'ke i mem |>.soundness Γcw Γwe <| κ₁e i mem
      · intro i
        exact «F⊗⊕ω».Term.not_mem_freeTermVars_Type_multi_open_intro <|
          List.not_mem_flatten.mp (xninE' _) _ <| Range.mem_map_of_mem mem'
      · exact xninF'
      · exact xinj
      · intro _ mem
        exact ψopih _ mem (ψopke _ mem) Γᵢw Γcw Γwe
  | TCSuper γcin _ mem ih =>
    rename_i TCₛ Aₛ κ _ _ _ _ _ Γ _ _ i _ _
    let ψke@(.tc γcₛin τke) := ψke
    let ⟨_, κe, _, _, γcₛsin, _⟩ := Γcw.In_inversion γcin
    let ⟨a, anin⟩ := ↑(Aₛ i).freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninAₛ, aninΓ⟩ := List.not_mem_append'.mp anin
    let Γawe := Γwe.typeExt aninΓ κe
    rw [← Γ.empty_append] at Γawe
    let TCₛake := γcₛsin a _ mem |>.weakening Γawe (Γ := .empty) (Γ' := Γ) (Γ'' := .typeExt .empty ..)
    rw [TypeEnvironment.empty_append] at Γawe TCₛake
    rcases TCₛake.tc_inversion with ⟨γc, _, _, TCeq, rfl, γcₛin', _, zeroke⟩
    let .mk .. := γc
    cases TCeq
    rcases zeroke.deterministic <| .var .head with ⟨rfl, rfl⟩
    rcases ClassEnvironmentEntry.mk.inj <| γcₛin.deterministic γcₛin' rfl with
      ⟨rfl, _, rfl, rfl, rfl, rfl⟩
    let Ety := ih (.tc γcin τke) Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := _ :: _)] at Ety
    let πty := Ety.prodElim (j := 1 + i) ⟨
      Nat.zero_le _,
      by
        rw [List.length_cons, List.length_map, Range.length_toList, Nat.sub_zero, Nat.add_comm]
        exact Nat.add_lt_add_right mem.upper _,
      Nat.mod_one _
    ⟩ (b := false)
    rw [Nat.add_comm, List.get!_cons_succ, Range.get!_map mem.upper, Nat.add_comm] at πty
    have : Monotype.typeClass (TCₛ i) (.var (.free a)) =
      .TypeVar_open (.typeClass (TCₛ i) (.var (.bound 0))) a := by
      simp [Monotype.TypeVar_open]
    rw [this, ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at TCₛake
    let ψke' := TCₛake.Monotype_open_preservation Γcw Γawe nofun (Γ' := .empty)
      (by simp [TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars]) aninAₛ
      τke
    simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype.Monotype_open] at ψke'
    rcases ψke.deterministic ψke' with ⟨_, Aeq⟩
    rw [Aeq]
    exact πty
  | allEmpty =>
    let .all _ ψ'ke κe emptyke := ψke
    rcases emptyke.empty_row_inversion with ⟨_, _, κe', rfl⟩
    cases κe.deterministic κe'
    rename List TypeVarId => I
    rename TypeEnvironment => Γ
    refine .equiv (.unit (Γwe.soundness Γcw)) <| .prod <| .listAppEmptyR ?_
    apply Kinding.lam <| Γ.typeVarDom ++ I
    intro a anin
    let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
    let Γawe := Γwe.typeExt aninΓ κe
    exact ψ'ke _ aninI |>.soundness Γcw Γawe .constr
  | allSingletonIntro I _ ψ'ke ξke τke ih =>
    rename_i Γ ψ' _ _ _ A' _ _
    rename TypeEnvironment => Γ
    let .all I' ψ'ke' κe ξτke (A := A'') := ψke
    rcases ξτke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke'⟩
    cases κeq
    rcases τke.deterministic τke' with ⟨_, rfl⟩
    let ⟨a, anin⟩ := I ++ I' ++ ψ'.freeTypeVars ++ ↑A'.freeTypeVars ++ ↑A''.freeTypeVars ++
      Γ.typeVarDom |>.exists_fresh
    let ⟨aninII'ψ'A'A'', aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninII'ψ'A', aninA''⟩ := List.not_mem_append'.mp aninII'ψ'A'A''
    let ⟨aninII'ψ', aninA'⟩ := List.not_mem_append'.mp aninII'ψ'A'
    let ⟨aninII', aninψ'⟩ := List.not_mem_append'.mp aninII'ψ'
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let Γawe := Γwe.typeExt aninΓ κe
    let ψ'opake := ψ'ke a aninI
    let ψ'opake' := ψ'ke' a aninI'
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at ψ'opake ψ'opake'
    let ψ'opτke :=
      ψ'opake.Monotype_open_preservation Γcw Γawe nofun aninψ' aninA' τke (Γ' := .empty)
    let ψ'opτke' :=
      ψ'opake'.Monotype_open_preservation Γcw Γawe nofun aninψ' aninA'' τke (Γ' := .empty)
    let Aopeq := ψ'opτke.deterministic ψ'opτke' |>.right
    let Ety := ih ψ'opτke Γᵢw Γcw Γwe
    apply Typing.equiv _ <| .prod <| .listAppSingletonR <| by
      apply Kinding.lam <| I' ++ Γ.typeVarDom
      intro a anin
      let ⟨aninI', aninΓ⟩ := List.not_mem_append'.mp anin
      exact ψ'ke' a aninI' |>.soundness Γcw (Γwe.typeExt aninΓ κe) .constr
    apply Typing.equiv _ <| .prod <| .listSingleton <| .symm <|
      .lamApp (.lam (I' ++ Γ.typeVarDom) (by
        intro a anin
        let ⟨aninI', aninΓ⟩ := List.not_mem_append'.mp anin
        exact ψ'ke' a aninI' |>.soundness Γcw (Γwe.typeExt aninΓ κe) .constr
      )) <| τke.soundness Γcw Γwe κe
    apply Typing.singleton
    rw [← Aopeq]
    exact Ety
  | allSingletonElim allce ih =>
    let ⟨_, allke@(.all I ψ'ke κe ξτke)⟩ := allce.to_Kinding Γᵢw Γcw Γwe
    rename_i Γ _ ψ' _ _ _ _ A _ _
    rcases ξτke.singleton_row_inversion with ⟨_, _, κeq, B, rfl, τke⟩
    cases κeq
    let Ety := ih allke Γᵢw Γcw Γwe
    let ⟨a, anin⟩ := I ++ ψ'.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninIψ'A, aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninIψ', aninA⟩ := List.not_mem_append'.mp aninIψ'A
    let ⟨aninI, aninψ'⟩ := List.not_mem_append'.mp aninIψ'
    let Γawe := Γwe.typeExt aninΓ κe
    let ψ'opake := ψ'ke a aninI
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at ψ'opake
    let ψ'opτke := ψ'opake.Monotype_open_preservation Γcw Γawe nofun aninψ' aninA τke (Γ' := .empty)
    rcases ψke.deterministic ψ'opτke with ⟨_, rfl⟩
    let Alc := ψ'opake.soundness Γcw Γawe .constr
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.zero_lt_one
    let Ety' := Ety.equiv <| .prod <| .listAppSingletonL <| by
      apply Kinding.lam <| I ++ Γ.typeVarDom
      intro a anin
      let ⟨aninI', aninΓ⟩ := List.not_mem_append'.mp anin
      exact ψ'ke a aninI' |>.soundness Γcw (Γwe.typeExt aninΓ κe) .constr
    rw [← Range.map_get!_eq (as := [_]), List.length_singleton] at Ety'
    let πty := Ety'.prodElim ⟨Nat.le.refl, Nat.le.refl, Nat.mod_one _⟩ (b := false)
    simp at πty
    refine .equiv πty <| .lamApp (.lam (I ++ Γ.typeVarDom) ?_) (K₂ := .star) <|
      τke.soundness Γcw Γwe κe
    intro a anin
    let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp anin
    exact ψ'ke a aninI |>.soundness Γcw (Γwe.typeExt aninΓ κe) .constr
  | allContain I containce _ ψ'ke κe containih allih =>
    rename_i Γ _ _ _ _ _ _ A' K _
    let .all I' ψ'ke' κe' ρ₀ke (A := A'') := ψke
    cases κe.deterministic κe'
    let ⟨_, containke@(.contain μke ρ₀ke' ρ₁ke κe'')⟩ := containce.to_Kinding Γᵢw Γcw Γwe
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe''
    apply Typing.app _ <| allih (.all I ψ'ke κe ρ₁ke) Γᵢw Γcw Γwe
    let Fty := containih containke Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩ (b := false)
    simp at πty
    have := πty.typeApp (B := [[λ a : K. A']]) <| .lam (I ++ Γ.typeVarDom) <| by
      intro a anin
      let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      let ψ'opake := ψ'ke a aninI
      exact ψ'opake.soundness Γcw Γawe .constr
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id] at this
    apply Typing.equiv _ <| .arr .refl <| .prod <| .listApp (.lam (I ++ I') (by
      intro a anin
      show [[Δ, a : K ⊢ A'^a ≡ A''^a]]
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
      let ψ'opake := ψ'ke a aninI
      let ψ'opake' := ψ'ke' a aninI'
      rcases ψ'opake.deterministic ψ'opake' with ⟨_, Aeq⟩
      rw [← Aeq]
      exact .refl
    )) .refl
    exact this
  | allConcat I concatce _ _ ψ'ke κe concatih all₀ih all₁ih =>
    rename_i Γ _ _ _ _ _ _ _ _ A' K _ _
    let .all I' ψ'ke' κe' ρ₂ke (A := A'') := ψke
    cases κe.deterministic κe'
    let ⟨_, concatke@(.concat μke ρ₀ke ρ₁ke ρ₂ke' κe'' contain₀₂ke contain₁₂ke)⟩ :=
      concatce.to_Kinding Γᵢw Γcw Γwe
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨κeq, rfl⟩
    cases κeq
    cases κe.deterministic κe''
    apply Typing.app _ <| all₁ih (.all I ψ'ke κe ρ₁ke) Γᵢw Γcw Γwe
    apply Typing.app _ <| all₀ih (.all I ψ'ke κe ρ₀ke) Γᵢw Γcw Γwe
    let Fty := concatih concatke Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩ (b := false)
    simp at πty
    have := πty.typeApp (B := [[λ a : K. A']]) <| .lam (I ++ Γ.typeVarDom) <| by
      intro a anin
      let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      let ψ'opake := ψ'ke a aninI
      exact ψ'opake.soundness Γcw Γawe .constr
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₂ke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id] at this
    apply Typing.equiv _ <| .arr .refl <| .arr .refl <| .prod <| .listApp (.lam (I ++ I') (by
      intro a anin
      show [[Δ, a : K ⊢ A'^a ≡ A''^a]]
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
      let ψ'opake := ψ'ke a aninI
      let ψ'opake' := ψ'ke' a aninI'
      rcases ψ'opake.deterministic ψ'opake' with ⟨_, Aeq⟩
      rw [← Aeq]
      exact .refl
    )) .refl
    exact this
  | ind I₀ I₁ τke κe keBₗ keBᵣ ceEᵣ ceEᵣ ihEₗ ihEᵣ =>
    rename «Type» => A_
    rename_i n _ Γ τ κ A K Bₗ ℓ b Bᵣ _ _ _ _
    let .ind I₀' I₁' ρke κe' keBₗ' keBᵣ' (κ := κ') := ψke
    rcases ρke.row_inversion with ⟨⟨_, _⟩, uni, A', _, _, rfl, κeq, κe'', h, κ'eq, τke'⟩
    cases κeq
    let κeq : κ = κ' := by
      match h with
      | .inl nne =>
        let mem : 0 ∈ [:n] := ⟨Nat.zero_le _, Nat.pos_of_ne_zero nne, Nat.mod_one _⟩
        let τ₀ke := τke 0 mem
        let τ₀ke' := τke' 0 mem
        exact τ₀ke.deterministic τ₀ke' |>.left
      | .inr beq => exact κ'eq beq
    cases κeq
    cases κe.deterministic κe'
    cases κe.deterministic κe''
    apply Typing.typeLam Γ.typeVarDom
    intro a anin
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    let Γawe := Γwe.typeExt anin <| .arr (.row κe) .star
    let Δawf := Γawe.soundness Γcw
    apply Typing.equiv (.lam Δ.termVarDom _) (.arr ?equiv .refl)
    case equiv =>
      apply TypeEquivalence.scheme <| I₀ ++ I₀' ++ Γ.typeVarDom
      intro aₗ aₗnin
      let ⟨aₗninI₀I₀', aₗninΓ⟩ := List.not_mem_append'.mp aₗnin
      let ⟨aₗninI₀, aₗninI₀'⟩ := List.not_mem_append'.mp aₗninI₀I₀'
      simp [Type.TypeVar_open]
      apply TypeEquivalence.scheme <| aₗ :: I₀ ++ aₗ :: I₀' ++ aₗ :: Γ.typeVarDom
      intro aₜ aₜnin
      let ⟨aₜninI₀I₀', aₜninΓ⟩ := List.not_mem_append'.mp aₜnin
      let ⟨aₜninI₀, aₜninI₀'⟩ := List.not_mem_append'.mp aₜninI₀I₀'
      simp [Type.TypeVar_open]
      apply TypeEquivalence.scheme <| aₜ :: aₗ :: I₀ ++ aₜ :: aₗ :: I₀' ++ aₜ :: aₗ :: Γ.typeVarDom
      intro aₚ aₚnin
      let ⟨aₚninI₀I₀', aₚninΓ⟩ := List.not_mem_append'.mp aₚnin
      let ⟨aₚninI₀, aₚninI₀'⟩ := List.not_mem_append'.mp aₚninI₀I₀'
      simp [Type.TypeVar_open]
      apply TypeEquivalence.scheme <| aₚ :: aₜ :: aₗ :: I₀ ++ aₚ :: aₜ :: aₗ :: I₀' ++ ↑I₁ ++ ↑I₁' ++
        aₚ :: aₜ :: aₗ :: Γ.typeVarDom ++ ↑Γ.typeVarDom
      intro aᵢ aᵢnin
      let ⟨aᵢninI₀I₀'I₁I₁'Γ₀, aᵢninΓ₁⟩ := List.not_mem_append'.mp aᵢnin
      let ⟨aᵢninI₀I₀'I₁I₁', aᵢninΓ₀⟩ := List.not_mem_append'.mp aᵢninI₀I₀'I₁I₁'Γ₀
      let ⟨aᵢninI₀I₀'I₁, aᵢninI₁'⟩ := List.not_mem_append'.mp aᵢninI₀I₀'I₁I₁'
      let ⟨aᵢninI₀I₀', aᵢninI₁⟩ := List.not_mem_append'.mp aᵢninI₀I₀'I₁
      let ⟨aᵢninI₀, aᵢninI₀'⟩ := List.not_mem_append'.mp aᵢninI₀I₀'
      simp [Type.TypeVar_open]
      apply TypeEquivalence.scheme <|
        aᵢ :: I₁ ++ aᵢ :: I₁' ++ aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom ++ aᵢ :: Γ.typeVarDom
      intro aₙ aₙnin
      let ⟨aₙninI₁I₁'Γ₀, aₙninΓ₁⟩ := List.not_mem_append'.mp aₙnin
      let ⟨aₙninI₁I₁', aₙninΓ₀⟩ := List.not_mem_append'.mp aₙninI₁I₁'Γ₀
      let ⟨aₙninI₁, aₙninI₁'⟩ := List.not_mem_append'.mp aₙninI₁I₁'
      simp [Type.TypeVar_open]
      let Γ₀we := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
        |>.typeExt aᵢninΓ₀ κe.row
      let Γ₁we := Γwe.typeExt aᵢninΓ₁ κe.row |>.typeExt aₙninΓ₁ κe.row
      apply TypeEquivalence.arr _ <| .arr _ .refl
      · let keBₗ := keBₗ _ aₗninI₀ _ aₜninI₀ _ aₚninI₀ _ aᵢninI₀
        rcases keBₗ.deterministic <| keBₗ' _ aₗninI₀' _ aₜninI₀' _ aₚninI₀' _ aᵢninI₀' with
          ⟨_, Bₗeq⟩
        let Bₗlc := keBₗ.soundness Γcw Γ₀we .constr |>.TypeVarLocallyClosed_of
        rw [Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5), ← Bₗeq,
            Bₗlc.TypeVar_open_id, Bₗlc.weaken (n := 5).TypeVar_open_id]
        exact .refl
        all_goals nofun
      · let keBᵣ := keBᵣ _ aᵢninI₁ _ aₙninI₁
        rcases keBᵣ.deterministic <| keBᵣ' _ aᵢninI₁' _ aₙninI₁' with ⟨_, Bᵣeq⟩
        let Bᵣlc := keBᵣ.soundness Γcw Γ₁we .constr |>.TypeVarLocallyClosed_of
        rw [Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 4),
            Type.TypeVar_open_comm (m := 4), Type.TypeVar_open_comm (m := 4),
            Type.TypeVar_open_comm (m := 4), Type.TypeVar_open_comm (m := 3),
            Type.TypeVar_open_comm (m := 3), Type.TypeVar_open_comm (m := 3),
            Type.TypeVar_open_comm (m := 2), Type.TypeVar_open_comm (m := 2),
            Bᵣlc.weaken (n := 2).TypeVar_open_id, Bᵣlc.weaken (n := 3).TypeVar_open_id,
            Bᵣlc.weaken (n := 4).TypeVar_open_id, Bᵣlc.weaken (n := 5).TypeVar_open_id,
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 5),
            Type.TypeVar_open_comm (m := 5), Type.TypeVar_open_comm (m := 4),
            Type.TypeVar_open_comm (m := 4), Type.TypeVar_open_comm (m := 4),
            Type.TypeVar_open_comm (m := 4), Type.TypeVar_open_comm (m := 3),
            Type.TypeVar_open_comm (m := 3), Type.TypeVar_open_comm (m := 3),
            Type.TypeVar_open_comm (m := 2), Type.TypeVar_open_comm (m := 2),
            ← Bᵣeq, Bᵣlc.weaken (n := 2).TypeVar_open_id, Bᵣlc.weaken (n := 3).TypeVar_open_id,
            Bᵣlc.weaken (n := 4).TypeVar_open_id, Bᵣlc.weaken (n := 5).TypeVar_open_id]
        exact .refl
        all_goals nofun
    let Bₗlc : Type.TypeVarLocallyClosed _ 5 := by
      let ⟨aₗ, aₗnin⟩ := I₀ ++ Γ.typeVarDom |>.exists_fresh
      let ⟨aₗninI, aₗninΓ⟩ := List.not_mem_append'.mp aₗnin
      let ⟨aₜ, aₜnin⟩ := aₗ :: I₀ ++ aₗ :: Γ.typeVarDom |>.exists_fresh
      let ⟨aₜninI, aₜninΓ⟩ := List.not_mem_append'.mp aₜnin
      let ⟨aₚ, aₚnin⟩ := aₜ :: aₗ :: I₀ ++ aₜ :: aₗ :: Γ.typeVarDom |>.exists_fresh
      let ⟨aₚninI, aₚninΓ⟩ := List.not_mem_append'.mp aₚnin
      let ⟨aᵢ, aᵢnin⟩ := aₚ :: aₜ :: aₗ :: I₀ ++ aₚ :: aₜ :: aₗ :: Γ.typeVarDom |>.exists_fresh
      let ⟨aᵢninI, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin
      let Γ'we := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
        |>.typeExt aᵢninΓ κe.row
      exact keBₗ _ aₗninI _ aₜninI _ aₚninI _ aᵢninI |>.soundness Γcw Γ'we .constr
        |>.TypeVarLocallyClosed_of.weaken (n := 5).TypeVar_open_drop Nat.le.refl.step.step.step
        |>.TypeVar_open_drop Nat.le.refl.step.step
        |>.TypeVar_open_drop Nat.le.refl.step
        |>.TypeVar_open_drop Nat.le.refl
    let Bᵣlc : Type.TypeVarLocallyClosed _ 5 := by
      let ⟨aᵢ, aᵢnin⟩ := I₁ ++ Γ.typeVarDom |>.exists_fresh
      let ⟨aᵢninI, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin
      let ⟨aₙ, aₙnin⟩ := aᵢ :: I₁ ++ aᵢ :: Γ.typeVarDom |>.exists_fresh
      let ⟨aₙninI, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin
      let Γ'we := Γwe.typeExt aᵢninΓ κe.row |>.typeExt aₙninΓ κe.row
      exact keBᵣ _ aᵢninI _ aₙninI |>.soundness Γcw Γ'we .constr
        |>.TypeVarLocallyClosed_of.weaken (n := 5).TypeVar_open_drop Nat.le.refl.step.step.step.step
        |>.TypeVar_open_drop Nat.le.refl.step.step.step
    rw [Bₗlc.TypeVar_open_id, Bᵣlc.TypeVar_open_id]
    intro xₛ xₛnin
    simp [«F⊗⊕ω».Term.TermVar_open]
    let Δaxₛwf := Δawf.termVarExt xₛnin <| by
      apply Kinding.ind_step Δawf .head (I₀ := ↑I₀ ++ a :: Γ.typeVarDom)
        (I₁ := ↑I₁ ++ a :: Γ.typeVarDom)
      · intro aₗ aₗnin
        let ⟨aₗninI, aₗninΓ⟩ := List.not_mem_append'.mp aₗnin
        intro aₜ aₜnin
        let ⟨aₜneaₗ, aₜnin'⟩ := List.not_mem_cons.mp aₜnin
        let ⟨aₜninI, aₜninΓ⟩ := List.not_mem_append'.mp aₜnin'
        let aₜninI := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninI⟩
        let aₜninΓ := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninΓ⟩
        intro aₚ aₚnin
        let ⟨aₚneaₜ, aₚnin'⟩ := List.not_mem_cons.mp aₚnin
        let ⟨aₚneaₗ, aₚnin''⟩ := List.not_mem_cons.mp aₚnin'
        let ⟨aₚninI, aₚninΓ⟩ := List.not_mem_append'.mp aₚnin''
        let aₚninI := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninI⟩⟩
        let aₚninΓ := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninΓ⟩⟩
        intro aᵢ aᵢnin
        let ⟨aᵢneaₚ, aᵢnin'⟩ := List.not_mem_cons.mp aᵢnin
        let ⟨aᵢneaₜ, aᵢnin''⟩ := List.not_mem_cons.mp aᵢnin'
        let ⟨aᵢneaₗ, aᵢnin'''⟩ := List.not_mem_cons.mp aᵢnin''
        let ⟨aᵢninI, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin'''
        let aᵢninI := List.not_mem_cons.mpr
          ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninI⟩⟩⟩
        let aᵢninΓ := List.not_mem_cons.mpr
          ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninΓ⟩⟩⟩
        intro aₙ aₙnin
        let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
        let ⟨aₙneaₚ, aₙnin''⟩ := List.not_mem_cons.mp aₙnin'
        let ⟨aₙneaₜ, aₙnin'''⟩ := List.not_mem_cons.mp aₙnin''
        let ⟨aₙneaₗ, aₙnin''''⟩ := List.not_mem_cons.mp aₙnin'''
        let ⟨aₙninI, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin''''
        let aₙninI := List.not_mem_cons.mpr ⟨
          aₙneaᵢ,
          List.not_mem_cons.mpr
            ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninI⟩⟩⟩
        ⟩
        let aₙninΓ := List.not_mem_cons.mpr ⟨
          aₙneaᵢ,
          List.not_mem_cons.mpr
            ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninΓ⟩⟩⟩
        ⟩
        let Γ'we := Γawe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
          |>.typeExt aᵢninΓ κe.row
        let Γ''we := Γ'we.typeExt aₙninΓ κe.row
        specialize keBₗ _ aₗninI _ aₜninI _ aₚninI _ aᵢninI
        let Bₗki := keBₗ.weakening Γ'we (Γ' := .typeExt .empty ..)
          (Γ'' := .typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
          |>.weakening Γ''we (Γ' := .typeExt .empty ..) (Γ'' := .empty)
          |>.soundness Γcw Γ''we .constr
        rw [Bₗki.TypeVarLocallyClosed_of.TypeVar_open_id]
        exact Bₗki
      · intro aᵢ aᵢnin
        let ⟨aᵢninI, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin
        intro aₙ aₙnin
        let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
        let ⟨aₙninI, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin'
        let aₙninI := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninI⟩
        let aₙninΓ := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninΓ⟩
        let Γ'we := Γawe.typeExt aᵢninΓ κe.row |>.typeExt aₙninΓ κe.row
        exact keBᵣ _ aᵢninI _ aₙninI |>.weakening Γ'we
          (Γ' := .typeExt .empty ..) (Γ'' := .typeExt (.typeExt .empty ..) ..)
          |>.soundness Γcw Γ'we .constr
    apply Typing.lam <| xₛ :: Δ.termVarDom
    intro xᵢ xᵢnin
    let xne := List.ne_of_not_mem_cons xᵢnin
    simp [«F⊗⊕ω».Term.TermVar_open]
    let Δaxₛᵢwf := Δaxₛwf.termVarExt xᵢnin <| .app (.var (.termVarExt .head)) .empty_list
    let Aki := (τke · · |>.soundness Γcw Γwe κe |>.weakening Δaxₛᵢwf
      (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty))
    let A'eqA i mem := τke' i mem |>.deterministic (τke i mem) |>.right
    let Aki' := (τke' · · |>.soundness Γcw Γwe κe |>.weakening Δaxₛᵢwf
      (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..) (Δ'' := .empty))
    rw (occs := .pos [2]) [← Range.map]
    let A'' (n : Nat) := [[(a {</ A'@i^a // i in [:n] /> </ : K // n = 0 || b />})]]
    have : [[(a {</ A'@i^a // i in [:n] /> </ : K // b />})]] = A'' n := by
      dsimp only [A'']
      congr
      match h with
      | .inl ne => rw [decide_eq_false ne, Bool.false_or]
      | .inr beq => rw [beq, Bool.or_true]
    rw [Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = [[(A'@i^a)]]
      simp
    ), this]
    apply Typing.multi_app (A := A'')
    · dsimp only [A'']
      rw [Range.map, Range.toList, if_neg nofun, List.map_nil, decide_eq_true rfl, Bool.true_or,
          Option.someIf_true]
      exact .var Δaxₛᵢwf .head
    · intro i iltn ih
      let imem : i ∈ [:n] := ⟨Nat.zero_le _, iltn, Nat.mod_one _⟩
      let row₀ᵢke :=
        TypeScheme.KindingAndElaboration.row (n := i) (fun _ _ => .label)
        (uni.of_les (Nat.zero_le _) Nat.le.refl iltn.le (Nat.zero_le _))
        (τke · ⟨Nat.zero_le _, ·.upper.trans iltn, Nat.mod_one _⟩) κe (b := i = 0 || b) <| by
          by_cases i = 0
          · case pos h =>
            right
            rw [BoolId, id, decide_eq_true h, Bool.true_or]
          · case neg h => exact .inl h
      let row₀ᵢ₁ke :=
        TypeScheme.KindingAndElaboration.row (b := b) (n := i + 1) (fun _ _ => .label)
        (uni.of_les (Nat.zero_le _) Nat.le.refl iltn (Nat.zero_le _))
        (τke · ⟨Nat.zero_le _, Nat.lt_of_lt_of_le ·.upper iltn, Nat.mod_one _⟩) κe <| .inl <|
          Nat.add_one_ne_zero _
      let singletonke := TypeScheme.KindingAndElaboration.singleton_row .label (τke i imem)
        (ξ := .label (ℓ i))
      let rowᵢ₁ₙke :=
        TypeScheme.KindingAndElaboration.row (n := n - (i + 1)) (fun _ _ => .label) (by
          rw [← Nat.sub_self (i + 1), Range.map_shift Nat.le.refl (f := fun j => Monotype.label (ℓ j))]
          exact uni.of_les (Nat.zero_le _) (Nat.zero_le _) Nat.le.refl iltn
        ) (fun j jmem => τke (j + (i + 1))
          ⟨Nat.zero_le _, Nat.add_lt_of_lt_sub jmem.upper, Nat.mod_one _⟩) κe <| .inr rfl
      rw [Option.someIf, if_pos rfl, ← Nat.sub_self (i + 1), Range.map_shift Nat.le.refl,
          Range.map_shift Nat.le.refl (f := fun l => (Monotype.label (ℓ l), τ l))] at rowᵢ₁ₙke
      rw [Range.map_eq_snoc_of_lt <| Nat.add_one_pos _, Nat.add_sub_cancel, Function.comp,
          Function.comp, Function.comp, «F⊗⊕ω».Term.multi_app_snoc_eq]
      apply Typing.app _ ih
      dsimp only [A'']
      simp [«F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TermVar_open, Type.TypeVar_open]
      apply Typing.app _ <| .unit Δaxₛᵢwf
      apply Typing.app
      · apply Typing.app
        · let xₛty := Typing.var Δaxₛᵢwf <| .termVarExt .head xne.symm
          let xₛty' := xₛty.typeApp .unit
          simp [Type.Type_open] at xₛty'
          let Aₘki := Aki i imem
          let xₛty'' := xₛty'.typeApp Aₘki
          simp [Type.Type_open] at xₛty''
          rw [Aₘki.TypeVarLocallyClosed_of.TypeVar_open_id]
          let As₀ᵢki : Kinding _ [[{</ A@j // j in [:i] /> </ : K // i = 0 || b />}]] _ :=
            .list (Aki · ⟨Nat.zero_le _, ·.upper.trans iltn, Nat.mod_one _⟩) <| by
              by_cases i = 0
              · case pos h =>
                right
                rw [BoolId, id, decide_eq_true h, Bool.true_or]
              · case neg h => exact .inl h
          let xₛty''' := xₛty''.typeApp As₀ᵢki
          simp [Type.Type_open] at xₛty'''
          let As₀ᵢ₁ki : Kinding _ [[{</ A@k // k in [:i+1] /> </ : K // b />}]] _ :=
            .list (Aki · ⟨Nat.zero_le _, Nat.lt_of_lt_of_le ·.upper iltn, Nat.mod_one _⟩) <| .inl <|
              Nat.add_one_ne_zero _
          let xₛty'''' := xₛty'''.typeApp As₀ᵢ₁ki
          rw [Type.Type_open, Type.Type_open, Type.Type_open, Type.Type_open,
              Kinding.unit (Δ := .empty).TypeVarLocallyClosed_of.weaken (n := 1).Type_open_id,
              Type.Type_open, Type.Type_open, Type.Type_open, if_neg nofun,
              As₀ᵢki.TypeVarLocallyClosed_of.weaken (n := 1).Type_open_id, Type.Type_open,
              Type.Type_open, if_neg nofun, Type.Type_open, if_pos rfl] at xₛty''''
          let xₛty''''' := xₛty''''.typeApp (B := [[{</ A@l // l in [i+1:n] /> : K}]]) <| by
            rw [← Range.map_shift (j := i + 1) <| Nat.le.refl, Nat.sub_self]
            apply Kinding.list _ <| .inr rfl
            intro l lmem
            apply Aki
            exact ⟨Nat.zero_le _, Nat.add_lt_of_lt_sub lmem.upper, Nat.mod_one _⟩
          rw [Type.Type_open, Type.Type_open, Type.Type_open, Type.Type_open,
              Kinding.unit (Δ := .empty).TypeVarLocallyClosed_of.Type_open_id, Type.Type_open,
              Type.Type_open, Type.Type_open, if_neg nofun,
              As₀ᵢki.TypeVarLocallyClosed_of.Type_open_id, Type.Type_open, if_neg nofun,
              As₀ᵢ₁ki.TypeVarLocallyClosed_of.Type_open_id] at xₛty'''''
          rw [← Range.map, ← Range.map, ← Range.map,
              Range.map_eq_of_eq_of_mem'' (f := _ ∘ _) (n := i) (by
                intro j jmem
                show _ = A j
                simp [Aki j ⟨Nat.zero_le _, jmem.upper.trans iltn, Nat.mod_one _⟩
                        |>.TypeVarLocallyClosed_of.TypeVar_open_id]
              ), Range.map_eq_of_eq_of_mem'' (f := _ ∘ _) (n := i + 1) (by
                intro k kmem
                show _ = A k
                simp [Aki k ⟨Nat.zero_le _, Nat.lt_of_lt_of_le kmem.upper iltn, Nat.mod_one _⟩
                        |>.TypeVarLocallyClosed_of.TypeVar_open_id]
              ), Range.map_eq_of_eq_of_mem'' (f := _ ∘ _) (n := n) (by
                intro l lmem
                show _ = A l
                simp [Aki l ⟨Nat.zero_le _, lmem.upper, Nat.mod_one _⟩
                        |>.TypeVarLocallyClosed_of.TypeVar_open_id]
              )]
          rw (occs := .pos [2]) [Range.map_eq_of_eq_of_mem'' (n := i) (by
                intro j jmem
                show _ = A j
                let jmem' : j ∈ [:n] := ⟨Nat.zero_le _, jmem.upper.trans iltn, Nat.mod_one _⟩
                simp [A'eqA j jmem', Aki j jmem' |>.TypeVarLocallyClosed_of.TypeVar_open_id]
              ), Range.map_eq_of_eq_of_mem'' (n := i + 1) (by
                intro k kmem
                show _ = A k
                let kmem' : k ∈ [:n] :=
                  ⟨Nat.zero_le _, Nat.lt_of_lt_of_le kmem.upper iltn, Nat.mod_one _⟩
                simp [A'eqA k kmem', Aki k kmem' |>.TypeVarLocallyClosed_of.TypeVar_open_id]
              )]
          exact xₛty'''''
        · let ⟨aₗ, aₗnin⟩ := ↑I₀ ++ ↑([:n].map (freeTypeVars ∘ τ)).flatten ++ ↑Bₗ.freeTypeVars ++
            ↑(A i).freeTypeVars ++ ↑([:i].map (Type.freeTypeVars ∘ A)).flatten ++
            ↑([:i+1].map (Type.freeTypeVars ∘ A)).flatten ++
            ↑([i+1:n].map (Type.freeTypeVars ∘ A)).flatten ++ Γ.typeVarDom
            |>.exists_fresh
          let ⟨aₗninIτBₗAA'A''A''', aₗninΓ⟩ := List.not_mem_append'.mp aₗnin
          let ⟨aₗninIτBₗAA'A'', aₗninA'''⟩ := List.not_mem_append'.mp aₗninIτBₗAA'A''A'''
          let ⟨aₗninIτBₗAA', aₗninA''⟩ := List.not_mem_append'.mp aₗninIτBₗAA'A''
          let ⟨aₗninIτBₗA, aₗninA'⟩ := List.not_mem_append'.mp aₗninIτBₗAA'
          let ⟨aₗninIτBₗ, aₗninA⟩ := List.not_mem_append'.mp aₗninIτBₗA
          let ⟨aₗninIτ, aₗninBₗ⟩ := List.not_mem_append'.mp aₗninIτBₗ
          let ⟨aₗninI, aₗninτ⟩ := List.not_mem_append'.mp aₗninIτ
          let aₗninτ' : ∀ i ∈ [:n], aₗ ∉ (τ i).freeTypeVars := by
            intro i imem
            have := List.not_mem_flatten.mp aₗninτ _ <| Range.mem_map_of_mem imem
            rw [Function.comp] at this
            exact this
          let ⟨aₜ, aₜnin⟩ := aₗ :: I₀ ++ ↑([:n].map (freeTypeVars ∘ τ)).flatten ++ ↑Bₗ.freeTypeVars ++
            ↑([:i].map (Type.freeTypeVars ∘ A)).flatten ++
            ↑([:i+1].map (Type.freeTypeVars ∘ A)).flatten ++
            ↑([i+1:n].map (Type.freeTypeVars ∘ A)).flatten ++ aₗ :: Γ.typeVarDom |>.exists_fresh
          let ⟨aₜninIτBₗAA'A'', aₜninΓ⟩ := List.not_mem_append'.mp aₜnin
          let ⟨aₜninIτBₗAA', aₜninA''⟩ := List.not_mem_append'.mp aₜninIτBₗAA'A''
          let ⟨aₜninIτBₗA, aₜninA'⟩ := List.not_mem_append'.mp aₜninIτBₗAA'
          let ⟨aₜninIτBₗ, aₜninA⟩ := List.not_mem_append'.mp aₜninIτBₗA
          let ⟨aₜninIτ, aₜninBₗ⟩ := List.not_mem_append'.mp aₜninIτBₗ
          let ⟨aₜninI, aₜninτ⟩ := List.not_mem_append'.mp aₜninIτ
          let aₜninτ' : ∀ i ∈ [:n], aₜ ∉ (τ i).freeTypeVars := by
            intro i imem
            have := List.not_mem_flatten.mp aₜninτ _ <| Range.mem_map_of_mem imem
            rw [Function.comp] at this
            exact this
          let aₜneaₗ := List.ne_of_not_mem_cons aₜninI
          let ⟨aₚ, aₚnin⟩ := aₜ :: aₗ :: I₀ ++ ↑([:n].map (freeTypeVars ∘ τ)).flatten ++
            ↑Bₗ.freeTypeVars ++ ↑([:i+1].map (Type.freeTypeVars ∘ A)).flatten ++
            ↑([i+1:n].map (Type.freeTypeVars ∘ A)).flatten ++
            aₜ :: aₗ :: Γ.typeVarDom |>.exists_fresh
          let ⟨aₚninIτBₗAA', aₚninΓ⟩ := List.not_mem_append'.mp aₚnin
          let ⟨aₚninIτBₗA, aₚninA'⟩ := List.not_mem_append'.mp aₚninIτBₗAA'
          let ⟨aₚninIτBₗ, aₚninA⟩ := List.not_mem_append'.mp aₚninIτBₗA
          let ⟨aₚninIτ, aₚninBₗ⟩ := List.not_mem_append'.mp aₚninIτBₗ
          let ⟨aₚninI, aₚninτ⟩ := List.not_mem_append'.mp aₚninIτ
          let aₚninτ' : ∀ i ∈ [:n], aₚ ∉ (τ i).freeTypeVars := by
            intro i imem
            have := List.not_mem_flatten.mp aₚninτ _ <| Range.mem_map_of_mem imem
            rw [Function.comp] at this
            exact this
          let aₚneaₜ := List.ne_of_not_mem_cons aₚninI
          let aₚneaₗ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₚninI
          let ⟨aᵢ, aᵢnin⟩ := aₚ :: aₜ :: aₗ :: I₀ ++ ↑Bₗ.freeTypeVars ++
            ↑([i+1:n].map (Type.freeTypeVars ∘ A)).flatten ++ aₚ :: aₜ :: aₗ :: Γ.typeVarDom
            |>.exists_fresh
          let ⟨aᵢninIBₗA, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin
          let ⟨aᵢninIBₗ, aᵢninA⟩ := List.not_mem_append'.mp aᵢninIBₗA
          let ⟨aᵢninI, aᵢninBₗ⟩ := List.not_mem_append'.mp aᵢninIBₗ
          let aᵢneaₚ := List.ne_of_not_mem_cons aᵢninI
          let aᵢneaₜ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aᵢninI
          let aᵢneaₗ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
            List.not_mem_of_not_mem_cons aᵢninI
          let ⟨aₙ, aₙnin⟩ := aᵢ :: aₚ :: aₜ :: aₗ :: I₀ ++ ↑Bₗ.freeTypeVars ++
            aᵢ :: aₚ :: aₜ :: aₗ :: Γ.typeVarDom |>.exists_fresh
          let ⟨aₙninIBₗ, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin
          let ⟨aₙninI, aₙninBₗ⟩ := List.not_mem_append'.mp aₙninIBₗ
          let aₙneaᵢ := List.ne_of_not_mem_cons aₙninI
          let aₙneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninI
          let aₙneaₜ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
            List.not_mem_of_not_mem_cons aₙninI
          let aₙneaₗ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
            List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninI
          let keBₗ' := keBₗ _ aₗninI _ aₜninI _ aₚninI _ aᵢninI
          let Γaₗwe := Γwe.typeExt aₗninΓ .label
          let Γaₗaₜwe := Γaₗwe.typeExt aₜninΓ κe
          let Γaₗaₜaₚwe := Γaₗaₜwe.typeExt aₚninΓ κe.row
          let Γaₗaₜaₚaᵢwe := Γaₗaₜaₚwe.typeExt aᵢninΓ κe.row
          let Γaₗaₜaₚaᵢaₙwe := Γaₗaₜaₚaᵢwe.typeExt aₙninΓ κe.row
          have : concat (.var (.free aₚ)) (.comm .non)
              (.row [(.var (.free aₗ), .var (.free aₜ))] none) (.var (.free aᵢ)) =
              TypeVar_open (TypeVar_open (TypeVar_open (TypeVar_open
                (concat (.var (.bound 2)) (.comm .non)
                  (.row [(.var (.bound 4), .var (.bound 3))] none) (.var (.bound 1))) aₗ 4) aₜ 3)
                aₚ 2) aᵢ 1 := by simp [TypeVar_open]
          rw [this, ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open,
              ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open, ← QualifiedType.TypeVar_open,
              ← TypeScheme.TypeVar_open, ← QualifiedType.TypeVar_open,
              ← TypeScheme.TypeVar_open] at keBₗ'
          let keBₗ''' := keBₗ'.Monotype_open_preservation Γcw Γaₗaₜaₚaᵢwe nofun (by
            simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open,
                  TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, TypeVar_open,
                  TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars]
            exact ⟨aᵢneaₚ, aᵢneaₗ, aᵢneaₜ⟩
          ) (Γ' := .empty) (Type.not_mem_freeTypeVars_TypeVar_open_intro
              (Type.not_mem_freeTypeVars_TypeVar_open_intro
                (Type.not_mem_freeTypeVars_TypeVar_open_intro aᵢninBₗ aᵢneaₗ) aᵢneaₜ) aᵢneaₚ) <|
            row₀ᵢ₁ke.weakening Γaₗaₜaₚwe (Γ'' := .empty)
              (Γ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..)
          rw [TypeScheme.TypeVar_open_Monotype_open_comm _ (by
            apply TypeVarLocallyClosed.row
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              exact .label
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              let .qual (.mono τlc) := τke j ⟨
                Nat.zero_le _,
                Nat.lt_of_lt_of_le mem'.upper iltn,
                Nat.mod_one _
              ⟩ |>.TypeVarLocallyClosed_of
              exact τlc.weakening (n := 2)
          ) nofun (m := 2) (n := 1),
              TypeScheme.TypeVar_open_Monotype_open_comm _ (by
            apply TypeVarLocallyClosed.row
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              exact .label
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              let .qual (.mono τlc) := τke j ⟨
                Nat.zero_le _,
                Nat.lt_of_lt_of_le mem'.upper iltn,
                Nat.mod_one _
              ⟩ |>.TypeVarLocallyClosed_of
              exact τlc.weakening (n := 3)
          ) nofun (m := 3) (n := 1),
              TypeScheme.TypeVar_open_Monotype_open_comm _ (by
            apply TypeVarLocallyClosed.row
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              exact .label
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              let .qual (.mono τlc) := τke j ⟨
                Nat.zero_le _,
                Nat.lt_of_lt_of_le mem'.upper iltn,
                Nat.mod_one _
              ⟩ |>.TypeVarLocallyClosed_of
              exact τlc.weakening (n := 4)
          ) nofun (m := 4) (n := 1),
              ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 2)
          ) nofun (m := 1) (n := 2),
              ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 3)
          ) nofun (m := 1) (n := 3),
              ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 4)
          ) nofun (m := 1) (n := 4)] at keBₗ'''
          let keBₗ'''' := keBₗ'''.Monotype_open_preservation Γcw Γaₗaₜaₚwe nofun (by
            simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open,
                  TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, TypeVar_open,
                  TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars]
            apply And.intro aₚneaₗ <| And.intro aₚneaₜ _
            intro j mem
            let mem' := Range.mem_of_mem_toList mem
            let mem'' : j ∈ [:n] := ⟨
              Nat.zero_le _,
              Nat.lt_of_lt_of_le mem'.upper iltn,
              Nat.mod_one _
            ⟩
            let .qual (.mono τlc) := τke j mem'' |>.TypeVarLocallyClosed_of
            rw [τlc.weakening (n := 4).TypeVar_open_id, τlc.weakening (n := 3).TypeVar_open_id]
            exact aₚninτ' j mem''
          ) (Γ' := .empty) (Type.not_mem_freeTypeVars_TypeVar_open_intro
              (Type.not_mem_freeTypeVars_TypeVar_open_intro
                (Type.not_mem_freeTypeVars_Type_open_intro aₚninBₗ (by
                    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map, ← Range.map]
                    exact aₚninA
                  )) aₚneaₗ) aₚneaₜ) <| row₀ᵢke.weakening Γaₗaₜwe (Γ'' := .empty)
              (Γ' := .typeExt (.typeExt .empty ..) ..)
          rw [TypeScheme.TypeVar_open_Monotype_open_comm _ (by
            apply TypeVarLocallyClosed.row
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              exact .label
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              let .qual (.mono τlc) := τke j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
                |>.TypeVarLocallyClosed_of
              exact τlc.weakening (n := 3)
          ) nofun (m := 3) (n := 2),
              TypeScheme.TypeVar_open_Monotype_open_comm _ (by
            apply TypeVarLocallyClosed.row
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              exact .label
            · intro ξτ mem
              rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
              simp only
              let .qual (.mono τlc) := τke j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
                |>.TypeVarLocallyClosed_of
              exact τlc.weakening (n := 4)
          ) nofun (m := 4) (n := 2),
              ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 3)
          ) nofun (m := 2) (n := 3),
              ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 4)
          ) nofun (m := 2) (n := 4)] at keBₗ''''
          let keBₗ''''' := keBₗ''''.Monotype_open_preservation Γcw Γaₗaₜwe nofun (by
            simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open,
                  TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, TypeVar_open,
                  TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars]
            apply And.intro _ <| And.intro aₜneaₗ _
            · intro j mem
              let mem' := Range.mem_of_mem_toList mem
              let mem'' : j ∈ [:n] := ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              let .qual (.mono τlc) := τke j mem'' |>.TypeVarLocallyClosed_of
              rw [τlc.weakening (n := 4).TypeVar_open_id]
              exact aₜninτ' j mem''
            · intro j mem
              let mem' := Range.mem_of_mem_toList mem
              let mem'' : j ∈ [:n] := ⟨
                Nat.zero_le _,
                Nat.lt_of_lt_of_le mem'.upper iltn,
                Nat.mod_one _
              ⟩
              let .qual (.mono τlc) := τke j mem'' |>.TypeVarLocallyClosed_of
              rw [τlc.weakening (n := 2).Monotype_open_id, τlc.weakening (n := 4).TypeVar_open_id]
              exact aₜninτ' j mem''
          ) (Γ' := .empty) (Type.not_mem_freeTypeVars_TypeVar_open_intro
              (Type.not_mem_freeTypeVars_Type_open_intro
                (Type.not_mem_freeTypeVars_Type_open_intro aₜninBₗ (by
                    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map, ← Range.map]
                    exact aₜninA'
                  )) (by
                    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map, ← Range.map]
                    exact aₜninA
                  )) aₜneaₗ) <| τke i imem |>.weakening Γaₗwe (Γ' := .typeExt .empty ..)
              (Γ'' := .empty)
          let .qual (.mono τlc) := τke i imem |>.TypeVarLocallyClosed_of.weakening (n := 4)
          rw [TypeScheme.TypeVar_open_Monotype_open_comm _ τlc nofun (m := 4) (n := 3),
              ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm (by
            exact Aki i imem |>.TypeVarLocallyClosed_of.weaken (n := 4)
          ) nofun (m := 3) (n := 4)] at keBₗ'''''
          let keBₗ'''''' := keBₗ'''''.Monotype_open_preservation Γcw Γaₗwe nofun (by
            simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open,
                  TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, TypeVar_open,
                  TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars]
            constructor
            · intro j mem
              let mem' := Range.mem_of_mem_toList mem
              let mem'' : j ∈ [:n] := ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              let .qual (.mono τlc) := τke j mem'' |>.TypeVarLocallyClosed_of
              rw [τlc.weakening (n := 3).Monotype_open_id]
              exact aₗninτ' j mem''
            · apply And.intro <| aₗninτ' i imem
              intro j mem
              let mem' := Range.mem_of_mem_toList mem
              let mem'' : j ∈ [:n] := ⟨
                Nat.zero_le _,
                Nat.lt_of_lt_of_le mem'.upper iltn,
                Nat.mod_one _
              ⟩
              let .qual (.mono τlc) := τke j mem'' |>.TypeVarLocallyClosed_of
              rw [τlc.weakening (n := 2).Monotype_open_id, τlc.weakening (n := 3).Monotype_open_id]
              exact aₗninτ' j mem''
          ) (Γ' := .empty) (Type.not_mem_freeTypeVars_Type_open_intro
              (Type.not_mem_freeTypeVars_Type_open_intro
                (Type.not_mem_freeTypeVars_Type_open_intro aₗninBₗ (by
                    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map, ← Range.map]
                    exact aₗninA''
                  )) (by
                    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map, ← Range.map]
                    exact aₗninA'
                  )) aₗninA) <| .label (ℓ := ℓ i)
          let .qual (.mono τlc) := τke i imem |>.TypeVarLocallyClosed_of
          let .qual (.mono row₀ᵢlc) := row₀ᵢke.TypeVarLocallyClosed_of
          let .qual (.mono row₀ᵢ₁lc) := row₀ᵢ₁ke.TypeVarLocallyClosed_of
          rw [Type.TypeVarLocallyClosed.Type_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 2)
          ) (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 1)
          ) nofun (m := 1) (n := 2),
              Type.TypeVarLocallyClosed.Type_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 3)
          ) (Aki i imem |>.TypeVarLocallyClosed_of.weaken (n := 1)) nofun (m := 1) (n := 3),
              Type.TypeVarLocallyClosed.Type_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 4)
          ) (.prod <| .list fun _ mem => List.not_mem_nil _ mem |>.elim) nofun (m := 1) (n := 4),
              Type.TypeVarLocallyClosed.Type_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 3)
          ) (Aki i imem |>.TypeVarLocallyClosed_of.weaken (n := 2)) nofun (m := 2) (n := 3),
              Type.TypeVarLocallyClosed.Type_open_comm (by
            apply Type.TypeVarLocallyClosed.list
            intro A' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            exact Aki j ⟨Nat.zero_le _, mem'.upper.trans iltn, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weaken (n := 4)
          ) (.prod <| .list fun _ mem => List.not_mem_nil _ mem |>.elim) nofun (m := 2) (n := 4),
              Type.TypeVarLocallyClosed.Type_open_comm (m := 3) (n := 4)
                (Aki i imem |>.TypeVarLocallyClosed_of.weaken (n := 4))
                (.prod <| .list fun _ mem => List.not_mem_nil _ mem |>.elim) nofun,
              TypeScheme.Monotype_open, QualifiedType.Monotype_open, TypeScheme.Monotype_open,
              QualifiedType.Monotype_open, TypeScheme.Monotype_open, QualifiedType.Monotype_open,
              TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open, Monotype_open,
              if_neg nofun, Monotype_open, if_pos rfl, Monotype_open, Monotype_open, List.mapMem_eq_map,
              List.map_singleton, Monotype_open, if_neg nofun, Monotype_open, if_neg nofun,
              Monotype_open, Monotype_open, if_pos rfl, Monotype_open,
              Monotype_open, List.mapMem_eq_map, List.map_singleton, Monotype_open, if_neg nofun,
              Monotype_open, if_neg nofun, row₀ᵢ₁lc.weakening (n := 2).Monotype_open_id,
              Monotype_open, row₀ᵢlc.weakening (n := 3).Monotype_open_id, Monotype_open,
              Monotype_open, List.mapMem_eq_map, List.map_singleton, Monotype_open, if_neg nofun,
              Monotype_open, if_pos rfl, row₀ᵢ₁lc.weakening (n := 3).Monotype_open_id, Monotype_open,
              row₀ᵢlc.weakening (n := 4).Monotype_open_id, Monotype_open, Monotype_open,
              List.mapMem_eq_map, List.map_singleton, Monotype_open, if_pos rfl,
              τlc.weakening (n := 4).Monotype_open_id, row₀ᵢ₁lc.weakening (n := 4).Monotype_open_id,
          ] at keBₗ''''''
          let Eₗty := ihEₗ i imem keBₗ'''''' Γᵢw Γcw Γwe
          let Eₗlc := Eₗty.TermVarLocallyClosed_of
          rw [Eₗty.TermTypeVarLocallyClosed_of.TypeVar_open_id, Eₗlc.weaken (n := 1).TermVar_open_id,
              Eₗlc.TermVar_open_id]
          let Eₗty' := Eₗty.weakening Δaxₛᵢwf (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..)
            (Δ'' := .empty)
          rw [Eₗty'.TypeVarLocallyClosed_of.Type_open_id]
          exact Eₗty'
      · let ⟨aᵢ, aᵢnin⟩ := I₁ ++ ([:n].map (freeTypeVars ∘ τ)).flatten ++ ↑Bᵣ.freeTypeVars ++
          ↑([i+1:n].map (Type.freeTypeVars ∘ A)).flatten ++ Γ.typeVarDom |>.exists_fresh
        let ⟨aᵢninIτBᵣA, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin
        let ⟨aᵢninIτBᵣ, aᵢninA⟩ := List.not_mem_append'.mp aᵢninIτBᵣA
        let ⟨aᵢninIτ, aᵢninBᵣ⟩ := List.not_mem_append'.mp aᵢninIτBᵣ
        let ⟨aᵢninI, aᵢninτ⟩ := List.not_mem_append'.mp aᵢninIτ
        let aᵢninτ' : ∀ i ∈ [:n], aᵢ ∉ (τ i).freeTypeVars := by
          intro i imem
          have := List.not_mem_flatten.mp aᵢninτ _ <| Range.mem_map_of_mem imem
          rw [Function.comp] at this
          exact this
        let ⟨aₙ, aₙnin⟩ := aᵢ :: I₁ ++ ↑([:n].map (freeTypeVars ∘ τ)).flatten ++ ↑Bᵣ.freeTypeVars ++
          aᵢ :: Γ.typeVarDom |>.exists_fresh
        let ⟨aₙninIτBᵣ, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin
        let ⟨aₙninIτ, aₙninBᵣ⟩ := List.not_mem_append'.mp aₙninIτBᵣ
        let ⟨aₙninI, aₙninτ⟩ := List.not_mem_append'.mp aₙninIτ
        let aₙninτ' : ∀ i ∈ [:n], aₙ ∉ (τ i).freeTypeVars := by
          intro i imem
          have := List.not_mem_flatten.mp aₙninτ _ <| Range.mem_map_of_mem imem
          rw [Function.comp] at this
          exact this
        let ane := List.ne_of_not_mem_cons aₙninI
        let keBᵣ' := keBᵣ _ aᵢninI _ aₙninI
        let Γaᵢwe := Γwe.typeExt aᵢninΓ κe.row
        let Γaᵢaₙwe := Γaᵢwe.typeExt aₙninΓ κe.row
        have : concat (.var (.free aᵢ)) (.comm .non) (.var (.free aₙ))
              (.row ([:n].map fun j => (.label (ℓ j), τ j)) (.someIf κ b)) =
            TypeVar_open (TypeVar_open (.concat (.var (.bound 1)) (.comm .non)
                (.var (.bound 0)) (.row ([:n].map fun j => (.label (ℓ j), τ j))
                  (.someIf κ b))) aᵢ 1) aₙ := by
          simp [TypeVar_open]
          intro j jmem
          let .qual (.mono τlc) := τke j (Range.mem_of_mem_toList jmem) |>.TypeVarLocallyClosed_of
          rw [τlc.weakening (n := 1).TypeVar_open_id, τlc.TypeVar_open_id]
        rw [this, ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open,
            ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at keBᵣ'
        let keBᵣ'' := keBᵣ'.Monotype_open_preservation Γcw Γaᵢaₙwe nofun (by
          simp [TypeScheme.TypeVar_open, QualifiedType.TypeVar_open, TypeVar_open,
                TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars]
          apply And.intro <| List.ne_of_not_mem_cons aₙninI
          intro j jmem
          let jmem' := Range.mem_of_mem_toList jmem
          let .qual (.mono τlc) := τke j (Range.mem_of_mem_toList jmem) |>.TypeVarLocallyClosed_of
          rw [τlc.weakening (n := 1).TypeVar_open_id]
          exact aₙninτ' _ jmem'
        ) (Type.not_mem_freeTypeVars_TypeVar_open_intro aₙninBᵣ ane) (Γ' := .empty) <|
          rowᵢ₁ₙke.weakening Γaᵢwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
        rw [TypeScheme.TypeVar_open_Monotype_open_comm _ _ Nat.one_ne_zero,
            ← Type.TypeVarLocallyClosed.Type_open_TypeVar_open_comm _ Nat.zero_ne_one] at keBᵣ''
        let keBᵣ''' := keBᵣ''.Monotype_open_preservation Γcw Γaᵢwe nofun (by
          simp [TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open,
                TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, freeTypeVars]
          constructor
          · intro j jmem
            let jmem' := Range.mem_of_mem_toList jmem
            exact aᵢninτ' _ ⟨Nat.zero_le _, jmem'.upper, Nat.mod_one _⟩
          · intro j jmem
            let jmem' := Range.mem_of_mem_toList jmem
            let .qual (.mono τlc) := τke j (Range.mem_of_mem_toList jmem) |>.TypeVarLocallyClosed_of
            rw [τlc.Monotype_open_id]
            exact aᵢninτ' _ jmem'
        ) (by
          apply Type.not_mem_freeTypeVars_Type_open_intro aᵢninBᵣ
          rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map, ← Range.map]
          exact aᵢninA
        ) row₀ᵢ₁ke (Γ' := .empty)
        let .qual (.mono rowᵢ₁ₙlc) := rowᵢ₁ₙke.TypeVarLocallyClosed_of
        let .qual (.mono ρlc) := ρke.TypeVarLocallyClosed_of
        rw [Type.TypeVarLocallyClosed.Type_open_comm _ _ Nat.zero_ne_one,
            TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open, Monotype_open,
            if_neg nofun, Monotype_open, Monotype_open, if_pos rfl, ρlc.Monotype_open_id,
            TypeScheme.Monotype_open, QualifiedType.Monotype_open, Monotype_open, Monotype_open,
            if_pos rfl, Monotype_open, rowᵢ₁ₙlc.weakening (n := 1).Monotype_open_id,
            ρlc.weakening (n := 1).Monotype_open_id] at keBᵣ'''
        let Eᵣty := ihEᵣ i imem keBᵣ''' Γᵢw Γcw Γwe
        let Eᵣlc := Eᵣty.TermVarLocallyClosed_of
        let Bᵣlc := Eᵣty.TypeVarLocallyClosed_of.weaken (n := 2).Type_open_drop Nat.le.refl.step
          |>.Type_open_drop Nat.le.refl
        rw [Eᵣty.TermTypeVarLocallyClosed_of.TypeVar_open_id, Eᵣlc.weaken (n := 1).TermVar_open_id,
            Eᵣlc.TermVar_open_id, Bᵣlc.weaken (n := 2).Type_open_id,
            Bᵣlc.weaken (n := 1).Type_open_id, Bᵣlc.Type_open_id]
        exact Eᵣty.weakening Δaxₛᵢwf (Δ' := .termExt (.termExt (.typeExt .empty ..) ..) ..)
          (Δ'' := .empty)
        · apply Type.TypeVarLocallyClosed.list
          intro A' mem
          rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
          exact Aki j ⟨Nat.zero_le _, mem'.upper, Nat.mod_one _⟩
            |>.TypeVarLocallyClosed_of.weaken (n := 1)
        · apply Type.TypeVarLocallyClosed.list
          intro A' mem
          rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
          exact Aki j ⟨Nat.zero_le _, Nat.lt_of_lt_of_le mem'.upper iltn, Nat.mod_one _⟩
            |>.TypeVarLocallyClosed_of
        · apply Type.TypeVarLocallyClosed.list
          intro A' mem
          rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
          exact Aki j ⟨Nat.zero_le _, mem'.upper, Nat.mod_one _⟩
            |>.TypeVarLocallyClosed_of.weaken (n := 1)
        · apply TypeVarLocallyClosed.row
          · intro ℓ' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            simp only
            exact .label
          · intro τ' mem
            rcases Range.mem_of_mem_map mem with ⟨j, mem', rfl⟩
            simp only
            let .qual (.mono τlc) := τke j ⟨Nat.zero_le _, mem'.upper, Nat.mod_one _⟩
              |>.TypeVarLocallyClosed_of.weakening (n := 1)
            exact τlc
  | splitEmpty I τke =>
    let .split concatke := ψke
    let .concat _ lift₀ke empty₀ke empty₁ke stare contain₀ke contain₁ke := concatke
    rcases empty₀ke.empty_row_inversion with ⟨_, κeq, stare', rfl⟩
    cases κeq
    cases stare.deterministic .star
    cases stare'.deterministic .star
    rcases empty₁ke.empty_row_inversion with ⟨_, _, stare'', rfl⟩
    cases stare''.deterministic .star
    cases lift₀ke
    case lift I' κe empty₂ke τke' =>
    rcases empty₂ke.empty_row_inversion with ⟨_, _, κe', rfl⟩
    cases κe.deterministic κe'
    let .contain _ lift₁ke empty₃ke stare''' := contain₀ke
    cases lift₁ke
    case lift I'' κe'' empty₄ke τke'' =>
    let .contain _ empty₅ke empty₆ke stare'''' := contain₁ke
    rcases empty₃ke.empty_row_inversion with ⟨_, κeq, stare''''', rfl⟩
    cases κeq
    cases stare'''.deterministic .star
    cases κe.deterministic κe''
    cases stare'''''.deterministic .star
    rcases empty₄ke.empty_row_inversion with ⟨_, _, κe''', rfl⟩
    cases κe.deterministic κe'''
    rcases empty₅ke.empty_row_inversion with ⟨_, κeq, stare'''''', rfl⟩
    cases κeq
    cases stare''''.deterministic .star
    cases stare''''''.deterministic .star
    rcases empty₆ke.empty_row_inversion with ⟨_, _, stare''''''', rfl⟩
    cases stare'''''''.deterministic .star
    rename TypeEnvironment => Γ
    let A'ki a (anin : a ∉ Γ.typeVarDom ++ I') :=
      let ⟨aninΓ, aninI'⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      τke' a aninI' |>.soundness Γcw Γawe .star
    let ⟨a, anin⟩ := Γ.typeVarDom ++ I' |>.exists_fresh
    let ⟨aninΓ, _⟩ := List.not_mem_append'.mp anin
    let Γawe := Γwe.typeExt aninΓ κe
    let A'lc :=
      A'ki _ anin |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.zero_lt_one
    let Δwf := Γwe.soundness Γcw
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
      rw [← A'lc.TypeVar_open_id (a := a)] at A'ki
      apply Typing.equiv _ <| .arr
        (.prod (.trans (.listAppEmptyR (.var .head)) (.listApp .refl (.listAppEmptyR (.lam
          (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
            intro a' a'nin
            let ⟨a'ninΔa, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
            exact A'ki a' a'ninΓI' |>.weakening (Δawf.typeVarExt a'ninΔa) (Δ' := .typeExt .empty ..)
              (Δ'' := .typeExt .empty ..))))))) .refl
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗwf := Δawf.termVarExt xₗnin .unit
      apply Typing.equiv _ <| .arr (.prod (.listAppEmptyR (.var (.termVarExt .head)))) .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗᵣwf := Δaxₗwf.termVarExt xᵣnin .unit
      apply Typing.equiv _ <| .prod <| .listAppEmptyR <| .var <| .termVarExt <| .termVarExt .head
      exact .unit Δaxₗᵣwf
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      let ane := List.ne_of_not_mem_cons aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δaaₜwf := Δawf.typeVarExt aₜnin (K := .star)
      rw [← A'lc.weaken (n := 1).TypeVar_open_id (a := a),
          ← A'lc.TypeVar_open_id (a := aₜ), Type.TypeVar_open_comm _ (Nat.ne_add_one _)] at A'ki
      apply Typing.equiv _ <|
        .arr (.arr (.sum (.trans
          (.listAppEmptyR (.var (.typeVarExt .head ane.symm)))
          (.listApp .refl (.listAppEmptyR (.lam
            (↑aₜ :: ↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
              intro a' a'nin
              let ⟨a'ninΔaaₜ, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
              exact A'ki a' a'ninΓI' |>.weakening (Δaaₜwf.typeVarExt a'ninΔaaₜ)
                (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..))))))) .refl)
          .refl
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr .never <| .var .head
      apply Typing.equiv _ <|
        .arr (.arr (.sum (.listAppEmptyR (.var (.termVarExt (.typeVarExt .head ane.symm))))) .refl)
          .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr .never <| .var <| .termVarExt .head
      apply Typing.equiv _ <|
        .arr (.sum (.listAppEmptyR (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm))))))
          .refl
      exact .var Δaaₜxₗᵣwf .head
    · let ⟨a, anin⟩ := Γ.typeVarDom ++ I'' |>.exists_fresh
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      let A''ki a (anin : a ∉ Γ.typeVarDom ++ I'') :=
        let ⟨aninΓ, aninI''⟩ := List.not_mem_append'.mp anin
        let Γawe := Γwe.typeExt aninΓ κe
        τke'' a aninI'' |>.soundness Γcw Γawe .star
      let A''lc := τke'' _ aninI |>.soundness Γcw Γawe .star
        |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.zero_lt_one
      apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.prod (.listAppEmptyR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin .unit
        rw [← A''lc.TypeVar_open_id (a := a)] at A''ki
        apply Typing.equiv _ <| .prod <| .trans (.listAppEmptyR (.var (.termVarExt .head))) <|
          .listApp .refl <| .listAppEmptyR <| .lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) (by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δaxwf.typeVarExt a'ninΔa)
                (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..))
        exact .unit Δaxwf
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        rw [← A''lc.TypeVar_open_id (a := a)] at A''ki
        apply Typing.equiv _ <| .arr
          (.sum (.trans (.listAppEmptyR (.var .head)) (.listApp .refl (.listAppEmptyR (.lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) (by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δawf.typeVarExt a'ninΔa)
                (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)))))))
          .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin .never
        apply Typing.equiv _ <| .sum <| .listAppEmptyR <| .var <| .termVarExt .head
        exact .var Δaxwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.prod (.listAppEmptyR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin .unit
        apply Typing.equiv _ <| .prod <| .listAppEmptyR <| .var <| .termVarExt .head
        exact .unit Δaxwf
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.sum (.listAppEmptyR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin .never
        apply Typing.equiv _ <| .sum <| .listAppEmptyR <| .var <| .termVarExt .head
        exact .var Δaxwf .head
  | splitSingletonMatch I τ₀ke τ₁ke ξke =>
    rename «Type» => A_
    rename_i Γ _ τ₀ A _ _ _ _
    rename TypeEnvironment => Γ
    let .split concatke := ψke
    let .concat _ liftke emptyke ξτ₀opτ₁ke starke containemptyke containξτ₀opτ₁ke := concatke
    let .lift I' τ₀ke' κe ξτ₁ke (A := A') := liftke
    let .contain _ liftke' ξτ₀opτ₁ke' starke' := containemptyke
    let .lift I'' τ₀ke'' κe' ξτ₁ke' (A := A'') := liftke'
    let .contain _ emptyke' ξτ₀opτ₁ke'' starke'' := containξτ₀opτ₁ke
    rcases ξτ₀opτ₁ke.deterministic ξτ₀opτ₁ke' with ⟨κeq, rfl⟩
    cases κeq
    rcases ξτ₀opτ₁ke.deterministic ξτ₀opτ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ξτ₁ke.deterministic ξτ₁ke' with ⟨_, rfl⟩
    rcases emptyke.deterministic emptyke' with ⟨_, rfl⟩
    rcases ξτ₀opτ₁ke.singleton_row_inversion with ⟨⟨_, ξke'⟩, _, κeq, _, rfl, τ₀opτ₁ke⟩
    cases κeq
    rcases ξτ₁ke.singleton_row_inversion with ⟨⟨_, ξke''⟩, _, κeq, _, rfl, τ₁ke'⟩
    cases κeq
    rcases emptyke.empty_row_inversion with ⟨_, κeq, starke''', rfl⟩
    cases κeq
    rcases ξke.deterministic ξke' with ⟨_, rfl⟩
    rcases ξke.deterministic ξke'' with ⟨_, rfl⟩
    rcases τ₁ke.deterministic τ₁ke' with ⟨_, rfl⟩
    cases κe.deterministic κe'
    cases starke.deterministic .star
    cases starke'.deterministic .star
    cases starke''.deterministic .star
    cases starke'''.deterministic .star
    let ⟨a, anin⟩ := I ++ I' ++ I'' ++ τ₀.freeTypeVars ++ ↑A.freeTypeVars ++ ↑A'.freeTypeVars ++
      ↑A''.freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninII'I''τ₀AA'A'', aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninII'I''τ₀AA', aninA''⟩ := List.not_mem_append'.mp aninII'I''τ₀AA'A''
    let ⟨aninII'I''τ₀A, aninA'⟩ := List.not_mem_append'.mp aninII'I''τ₀AA'
    let ⟨aninII'I''τ₀, aninA⟩ := List.not_mem_append'.mp aninII'I''τ₀A
    let ⟨aninII'I'', aninτ₀⟩ := List.not_mem_append'.mp aninII'I''τ₀
    let ⟨aninII', aninI''⟩ := List.not_mem_append'.mp aninII'I''
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let Γawe := Γwe.typeExt aninΓ κe
    let τ₀opake := τ₀ke _ aninI
    let Aki := τ₀opake.soundness Γcw Γawe .star
    let Alc := Aki.TypeVarLocallyClosed_of.weaken (n := 1) |>.TypeVar_open_drop Nat.le.refl
    let τ₀opake' := τ₀ke' _ aninI'
    let A'ki := τ₀opake'.soundness Γcw Γawe .star
    let A'lc := A'ki.TypeVarLocallyClosed_of.weaken (n := 1) |>.TypeVar_open_drop Nat.le.refl
    let τ₀opake'' := τ₀ke'' _ aninI''
    let A''ki := τ₀opake''.soundness Γcw Γawe .star
    let A''lc := A''ki.TypeVarLocallyClosed_of.weaken (n := 1) |>.TypeVar_open_drop Nat.le.refl
    let Bki := τ₁ke.soundness Γcw Γwe κe
    let Blc := Bki.TypeVarLocallyClosed_of
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at τ₀opake τ₀opake' τ₀opake''
    let τ₀opτ₁ke' :=
      τ₀opake.Monotype_open_preservation Γcw Γawe nofun aninτ₀ aninA τ₁ke (Γ' := .empty)
    let τ₀opτ₁ke'' :=
      τ₀opake'.Monotype_open_preservation Γcw Γawe nofun aninτ₀ aninA' τ₁ke (Γ' := .empty)
    let τ₀opτ₁ke''' :=
      τ₀opake''.Monotype_open_preservation Γcw Γawe nofun aninτ₀ aninA'' τ₁ke (Γ' := .empty)
    rcases τ₀opτ₁ke.deterministic τ₀opτ₁ke' with ⟨_, rfl⟩
    rcases τ₀opτ₁ke.deterministic τ₀opτ₁ke'' with ⟨_, AopeqA'op⟩
    rcases τ₀opτ₁ke.deterministic τ₀opτ₁ke''' with ⟨_, AopeqA''op⟩
    let AopBki := τ₀opτ₁ke.soundness Γcw Γwe .star
    let AopBlc := AopBki.TypeVarLocallyClosed_of
    let Δwf := Γwe.soundness Γcw
    let A'ki a (anin : a ∉ Γ.typeVarDom ++ I') :=
      let ⟨aninΓ, aninI'⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      τ₀ke' a aninI' |>.soundness Γcw Γawe .star
    let A''ki a (anin : a ∉ Γ.typeVarDom ++ I'') :=
      let ⟨aninΓ, aninI''⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      τ₀ke'' a aninI'' |>.soundness Γcw Γawe .star
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
      let Bki' := Bki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      rw [← Bki'.TypeVarLocallyClosed_of.TypeVar_open_id (a := a)] at Bki'
      rw [← A'lc.TypeVar_open_id (a := a)] at A'ki
      apply Typing.equiv _ <| .arr
        (.prod (.trans
          (.listAppSingletonR (.var .head))
          (.listApp .refl
            (.trans (.listSingleton <| .symm <| .lamApp (.lam
          (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
            intro a' a'nin
            let ⟨a'ninΔa, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
            exact A'ki a' a'ninΓI' |>.weakening (Δawf.typeVarExt a'ninΔa) (Δ' := .typeExt .empty ..)
              (Δ'' := .typeExt .empty ..))) Bki') (.listAppSingletonR (.lam
          (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
            intro a' a'nin
            let ⟨a'ninΔa, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
            exact A'ki a' a'ninΓI' |>.weakening (Δawf.typeVarExt a'ninΔa) (Δ' := .typeExt .empty ..)
              (Δ'' := .typeExt .empty ..))))))))
        .refl
      rw [A'lc.TypeVar_open_id, Blc.TypeVar_open_id, Blc.Type_open_TypeVar_open_eq, ← AopeqA'op]
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗwf := Δawf.termVarExt xₗnin <| .prod <| .singleton_list <| .app (.var .head) <|
        AopBki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      apply Typing.equiv _ <| .arr (.prod (.listAppEmptyR (.var (.termVarExt .head)))) .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xne := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗᵣwf := Δaxₗwf.termVarExt xᵣnin .unit
      apply Typing.equiv _ <| .prod <| .listAppSingletonR <| .var <| .termVarExt <|
        .termVarExt .head
      exact .var Δaxₗᵣwf <| .termVarExt .head xne.symm
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      let ane := List.ne_of_not_mem_cons aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δaaₜwf := Δawf.typeVarExt aₜnin (K := .star)
      let Bki' := Bki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty)
      rw [← Bki'.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_id (a := a),
          ← Bki'.TypeVarLocallyClosed_of.TypeVar_open_id (a := aₜ)] at Bki'
      rw [← A'lc.TypeVar_open_id (a := aₜ), ← A'lc.weaken (n := 1).TypeVar_open_id (a := a)] at A'ki
      apply Typing.equiv _ <| .arr (.arr (.sum (.trans
            (.listAppSingletonR (.var (.typeVarExt .head ane.symm)))
            (.listApp .refl
              (.trans (.listSingleton <| .symm <| .lamApp (.lam
            (↑aₜ :: ↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
              intro a' a'nin
              let ⟨a'ninΔaaₜ, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
              exact A'ki a' a'ninΓI' |>.weakening (Δaaₜwf.typeVarExt a'ninΔaaₜ)
                (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..))) Bki')
                (.listAppSingletonR (.lam
            (↑aₜ :: ↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
              intro a' a'nin
              let ⟨a'ninΔaaₜ, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
              exact A'ki a' a'ninΓI' |>.weakening (Δaaₜwf.typeVarExt a'ninΔaaₜ)
                (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..))))))))
          .refl) .refl
      rw [A'lc.weaken (n := 1).TypeVar_open_id, A'lc.TypeVar_open_id,
          Blc.weaken (n := 1).TypeVar_open_id, Blc.TypeVar_open_id,
          AopBlc.weaken (n := 1).TypeVar_open_id, AopBlc.TypeVar_open_id, ← AopeqA'op]
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr
        (.sum (.singleton_list (.app
          (.var (.typeVarExt .head ane.symm))
          (AopBki.weakening Δaaₜwf (Δ' := .typeExt (.typeExt .empty ..) ..)
            (Δ'' := .empty))))) <| .var .head
      apply Typing.equiv _ <| .arr
        (.arr (.sum (.listAppEmptyR (.var (.termVarExt (.typeVarExt .head ane.symm))))) .refl)
        .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xne := List.ne_of_not_mem_cons xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr .never <| .var <| .termVarExt .head
      apply Typing.equiv _ <| .arr
        (.sum (.listAppSingletonR (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm))))))
        .refl
      exact .var Δaaₜxₗᵣwf <| .termVarExt .head xne.symm
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.prod (.listAppSingletonR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .singleton_list <| .app (.var .head) <|
          AopBki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        let Bki' := Bki.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
        rw [← AopBki.TypeVarLocallyClosed_of.TypeVar_open_id (a := a)] at Bki' Δaxwf
        rw (occs := .pos [2]) [← Bki'.TypeVarLocallyClosed_of.TypeVar_open_id (a := a)] at Bki'
        rw [← A''lc.TypeVar_open_id (a := a)] at A''ki
        apply Typing.equiv _ <| .prod <| .trans (.listAppSingletonR (.var (.termVarExt .head))) <|
          .listApp .refl <| .trans (.listSingleton <| .symm <| .lamApp (.lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) (by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δaxwf.typeVarExt a'ninΔa)
                (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..))) Bki') <|
          .listAppSingletonR <| .lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) <| by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δaxwf.typeVarExt a'ninΔa)
                (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
        rw [A''lc.TypeVar_open_id, Blc.TypeVar_open_id, ← AopeqA''op]
        rw [AopBlc.TypeVar_open_id] at Δaxwf ⊢
        exact .var Δaxwf .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        let Bki' := Bki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        rw [← Bki'.TypeVarLocallyClosed_of.TypeVar_open_id (a := a)] at Bki'
        rw [← A''lc.TypeVar_open_id (a := a)] at A''ki
        apply Typing.equiv _ <| .arr (.sum (.trans (.listAppSingletonR (.var .head))
          (.listApp .refl (.trans (.listSingleton <| .symm <| .lamApp (.lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) (by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δawf.typeVarExt a'ninΔa)
                (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..))) Bki')
            (.listAppSingletonR (.lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) (by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δawf.typeVarExt a'ninΔa)
                (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)))))))) .refl
        rw [A''lc.TypeVar_open_id, Blc.TypeVar_open_id, AopBlc.TypeVar_open_id, ← AopeqA''op]
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .singleton_list <| .app (.var .head) <|
          AopBki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        apply Typing.equiv _ <| .sum <| .listAppSingletonR <| .var <| .termVarExt .head
        exact .var Δaxwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.prod (.listAppSingletonR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .singleton_list <| .app (.var .head) <|
          AopBki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        apply Typing.equiv _ <| .prod <| .listAppEmptyR <| .var <| .termVarExt .head
        rw [AopBlc.TypeVar_open_id]
        exact .unit Δaxwf
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.sum (.listAppEmptyR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin .never
        apply Typing.equiv _ <| .sum <| .listAppSingletonR <| .var <| .termVarExt .head
        rw [AopBlc.TypeVar_open_id]
        exact .explode (.var Δaxwf .head) <| .sum <| .singleton_list <| .app
          (.var (.termVarExt .head)) <|
          AopBki.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
  | splitSingletonRest I _ τ₀ke τ₁ke ξke =>
    let .split concatke := ψke
    let .concat _ liftke ξτ₁ke ξτ₁ke' starke containemptyke containξτ₁ke := concatke
    let .lift I' τ₀ke' κe emptyke := liftke
    let .contain _ liftke' ξτ₁ke'' starke' := containemptyke
    let .lift I'' τ₀ke'' κe' emptyke' := liftke'
    let .contain _ ξτ₁ke''' ξτ₁ke'''' starke'' := containξτ₁ke
    rcases ξτ₁ke.deterministic ξτ₁ke' with ⟨_, rfl⟩
    rcases ξτ₁ke.deterministic ξτ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    rcases ξτ₁ke.deterministic ξτ₁ke''' with ⟨κeq, rfl⟩
    cases κeq
    rcases ξτ₁ke.deterministic ξτ₁ke'''' with ⟨_, rfl⟩
    rcases emptyke.deterministic emptyke' with ⟨_, rfl⟩
    rcases ξτ₁ke.singleton_row_inversion with ⟨⟨_, ξke'⟩, _, κeq, _, rfl, τ₁ke'⟩
    cases κeq
    rcases emptyke.empty_row_inversion with ⟨_, f, κe'', rfl⟩
    rcases ξke.deterministic ξke' with ⟨_, rfl⟩
    rcases τ₁ke.deterministic τ₁ke' with ⟨rfl, rfl⟩
    cases κe.deterministic κe'
    cases κe.deterministic κe''
    cases starke.deterministic .star
    cases starke'.deterministic .star
    cases starke''.deterministic .star
    let Bki := τ₁ke.soundness Γcw Γwe .star
    let Blc := Bki.TypeVarLocallyClosed_of
    rename TypeEnvironment => Γ
    let ⟨a, anin⟩ := Γ.typeVarDom ++ I' ++ I'' |>.exists_fresh
    let ⟨aninΓI', aninI''⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓ, aninI'⟩ := List.not_mem_append'.mp aninΓI'
    let Γawe := Γwe.typeExt aninΓ κe
    let A'lc := τ₀ke' _ aninI' |>.soundness Γcw Γawe .star
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.zero_lt_one
    let A''lc := τ₀ke'' _ aninI'' |>.soundness Γcw Γawe .star
      |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.zero_lt_one
    let Δwf := Γwe.soundness Γcw
    let A'ki a (anin : a ∉ Γ.typeVarDom ++ I') :=
      let ⟨aninΓ, aninI'⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      τ₀ke' a aninI' |>.soundness Γcw Γawe .star
    let A''ki a (anin : a ∉ Γ.typeVarDom ++ I'') :=
      let ⟨aninΓ, aninI''⟩ := List.not_mem_append'.mp anin
      let Γawe := Γwe.typeExt aninΓ κe
      τ₀ke'' a aninI'' |>.soundness Γcw Γawe .star
    apply Typing.quadruple
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
      rw [← A'lc.TypeVar_open_id (a := a)] at A'ki
      apply Typing.equiv _ <| .arr
        (.prod (.trans (.listAppEmptyR (.var .head)) (.listApp .refl (.listAppEmptyR (.lam
          (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
            intro a' a'nin
            let ⟨a'ninΔa, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
            exact A'ki a' a'ninΓI' |>.weakening (Δawf.typeVarExt a'ninΔa) (Δ' := .typeExt .empty ..)
              (Δ'' := .typeExt .empty ..)))))))
        .refl
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗwf := Δawf.termVarExt xₗnin .unit
      apply Typing.equiv _ <| .arr (.prod (.listAppSingletonR (.var (.termVarExt .head)))) .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaxₗᵣwf := Δaxₗwf.termVarExt xᵣnin <| .prod <| .singleton_list <| .app
        (.var (.termVarExt .head)) <|
        Bki.weakening Δaxₗwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
      apply Typing.equiv _ <| .prod <| .listAppSingletonR <| .var <| .termVarExt <|
        .termVarExt .head
      rw [Blc.TypeVar_open_id]
      exact .var Δaxₗᵣwf .head
    · apply Typing.typeLam Δ.typeVarDom
      intro a anin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
      apply Typing.typeLam <| a :: Δ.typeVarDom
      intro aₜ aₜnin
      let ane := List.ne_of_not_mem_cons aₜnin
      simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
      let Δaaₜwf := Δawf.typeVarExt aₜnin (K := .star)
      rw [← A'lc.weaken (n := 1).TypeVar_open_id (a := a), ← A'lc.TypeVar_open_id (a := aₜ),
          Type.TypeVar_open_comm _ (Nat.ne_add_one _)] at A'ki
      apply Typing.equiv _ <| .arr
        (.arr (.sum (.trans (.listAppEmptyR (.var (.typeVarExt .head ane.symm)))
          (.listApp .refl (.listAppEmptyR (.lam
            (↑aₜ :: ↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I')) (by
              intro a' a'nin
              let ⟨a'ninΔaaₜ, a'ninΓI'⟩ := List.not_mem_append'.mp a'nin
              exact A'ki a' a'ninΓI' |>.weakening (Δaaₜwf.typeVarExt a'ninΔaaₜ)
                (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)))))))
          .refl) .refl
      apply Typing.lam Δ.termVarDom
      intro xₗ xₗnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗwf := Δaaₜwf.termVarExt xₗnin <| .arr .never <| .var .head
      apply Typing.equiv _ <| .arr (.arr
        (.sum (.listAppSingletonR (.var (.termVarExt (.typeVarExt .head ane.symm)))))
        .refl) .refl
      apply Typing.lam <| xₗ :: Δ.termVarDom
      intro xᵣ xᵣnin
      simp [«F⊗⊕ω».Term.TermVar_open]
      let Δaaₜxₗᵣwf := Δaaₜxₗwf.termVarExt xᵣnin <| .arr
        (.sum (.singleton_list (.app
          (.var (.termVarExt (.typeVarExt .head ane.symm)))
          (Bki.weakening Δaaₜxₗwf (Δ' := .termExt (.typeExt (.typeExt .empty ..) ..) ..)
            (Δ'' := .empty))))) <| .var <| .termVarExt <| .head
      apply Typing.equiv _ <| .arr
        (.sum (.listAppSingletonR (.var (.termVarExt (.termVarExt (.typeVarExt .head ane.symm))))))
        .refl
      rw [Blc.weaken (n := 1).TypeVar_open_id, Blc.TypeVar_open_id]
      exact .var Δaaₜxₗᵣwf .head
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.prod (.listAppSingletonR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .singleton_list <| .app (.var .head) <|
          Bki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        rw [← A''lc.TypeVar_open_id (a := a)] at A''ki
        apply Typing.equiv _ <| .prod <| .trans (.listAppEmptyR (.var (.termVarExt .head))) <|
          .listApp .refl <| .listAppEmptyR <| .lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) <| by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              rw [Blc.TypeVar_open_id]
              exact A''ki a' a'ninΓI'' |>.weakening (Δaxwf.typeVarExt a'ninΔa)
                (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .typeExt .empty ..)
        rw [Blc.TypeVar_open_id]
        exact .unit Δaxwf
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        rw [← A''lc.TypeVar_open_id (a := a)] at A''ki
        apply Typing.equiv _ <| .arr
          (.sum (.trans (.listAppEmptyR (.var .head)) (.listApp .refl (.listAppEmptyR (.lam
            (↑a :: Δ.typeVarDom ++ (↑Γ.typeVarDom ++ ↑I'')) (by
              intro a' a'nin
              let ⟨a'ninΔa, a'ninΓI''⟩ := List.not_mem_append'.mp a'nin
              exact A''ki a' a'ninΓI'' |>.weakening (Δawf.typeVarExt a'ninΔa)
                (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)))))))
          .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin .never
        apply Typing.equiv _ <| .sum <| .listAppSingletonR <| .var <| .termVarExt .head
        rw [Blc.TypeVar_open_id]
        exact .explode (.var Δaxwf .head) <| .sum <| .singleton_list <| .app
          (.var (.termVarExt .head)) <|
          Bki.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
    · apply Typing.pair
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.prod (.listAppSingletonR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin <| .prod <| .singleton_list <| .app (.var .head) <|
          Bki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        apply Typing.equiv _ <| .prod <| .listAppSingletonR <| .var <| .termVarExt .head
        rw [Blc.TypeVar_open_id]
        exact .var Δaxwf .head
      · apply Typing.typeLam Δ.typeVarDom
        intro a anin
        simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
        let Δawf := Δwf.typeVarExt anin (K := [[(* ↦ *)]])
        apply Typing.equiv _ <| .arr (.sum (.listAppSingletonR (.var .head))) .refl
        apply Typing.lam Δ.termVarDom
        intro x xnin
        simp [«F⊗⊕ω».Term.TermVar_open]
        let Δaxwf := Δawf.termVarExt xnin <| .sum <| .singleton_list <| .app (.var .head) <|
          Bki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        apply Typing.equiv _ <| .sum <| .listAppSingletonR <| .var <| .termVarExt .head
        rw [Blc.TypeVar_open_id]
        exact .var Δaxwf .head
  | splitPiecewise _ _ _ _ _ _ _ _ _ _ _ ih =>
    let .split concatke := ψke
    exact ih concatke Γᵢw Γcw Γwe
  | splitConcat splitce splitih => exact splitih (.split ψke) Γᵢw Γcw Γwe

end Monotype.ConstraintSolvingAndElaboration

end TabularTypes
