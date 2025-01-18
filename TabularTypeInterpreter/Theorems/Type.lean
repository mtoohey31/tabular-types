import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.Lemmas.ClassEnvironment
import TabularTypeInterpreter.Lemmas.Type
import TabularTypeInterpreter.Lemmas.TypeEnvironment
import TabularTypeInterpreter.Semantics.Type
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

mutual

theorem TypeScheme.KindingAndElaboration.soundness (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (κe : [[⊢ κ ⇝ K]]) : [[Δ ⊢ A : K]] := open TypeScheme in match σ, σke with
  | .qual (.mono (.var _)), .var aκinΓ => .var <| Γwe.TypeVarIn_preservation aκinΓ κe
  | .qual (.mono (.app φ τ)), .app φke τke (κ₀ := κ₀) =>
    let ⟨K₀, κ₀e⟩ := κ₀.Elaboration_total
    .app (φke.soundness Γwe (.arr κ₀e κe)) (τke.soundness Γwe κ₀e)
  | .qual (.mono (.arr τ₀ τ₁)), .arr τ₀ke τ₁ke =>
    let .star := κe
    .arr (τ₀ke.soundness Γwe .star) (τ₁ke.soundness Γwe .star)
  | .quant κ' σ', .scheme I σ'ke κ'e =>
    .scheme (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      σ'ke a aninI |>.soundness (Γwe.typeExt aninΓ κ'e) κe
  | .qual (.qual ψ γ), .qual φke γke κe' => by
    cases κe.deterministic κe'
    exact .arr (φke.soundness Γwe .constr) (γke.soundness Γwe κe')
  | .qual (.mono (.label _)), .label => let .label := κe; .unit
  | .qual (.mono (.floor _)), .floor _ => let .star := κe; .unit
  | .qual (.mono (.comm _)), .comm => let .comm := κe; .unit
  | .qual (.mono (.row ..)), .row _ _ τke =>
    let .row κ'e := κe
    .list fun i imem => τke i imem |>.soundness Γwe κ'e
  | .qual (.mono (.prod μ ρ)), .prod μke ρke =>
    let .star := κe
    .prod <| ρke.soundness Γwe <| .row .star
  | .qual (.mono (.sum μ ρ)), .sum μke ρke =>
    let .star := κe
    .sum <| ρke.soundness Γwe <| .row .star
  | .qual (.mono (.lift (.mk κ' τ) ρ)), σke =>
    let .row κ₁e := κe
    let .lift I τke κ₀e ρke := σke
    let Aopki : «F⊗⊕ω».Kinding .. := .lam (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      τke a aninI |>.soundness (Γwe.typeExt aninΓ κ₀e) κ₁e
    .listApp Aopki (ρke.soundness Γwe κ₀e.row)
  | .qual (.mono (.contain ρ₀ μ ρ₁)), .contain _ ρ₀ke ρ₁ke κ'e (K := K') (A₀ := A₀) (A₁ := A₁) => by
    let .constr := κe
    apply Kinding.prod
    let A i : «Type» := match i with
      | 0 => [[∀ a : K' ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧)]]
      | 1 => [[∀ a : K' ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)]]
      | _ => .list []
    let Δwf := Γwe.soundness
    let A₀k := ρ₀ke.soundness Γwe κ'e.row
    let A₁k := ρ₁ke.soundness Γwe κ'e.row
    have := Kinding.list (Δ := Δ) (A := A) (K := .star) (n := 2)
      fun | 0, _ => .prj_evidence Δwf A₀k A₁k | 1, _ => .inj_evidence Δwf A₀k A₁k
    simp [Range.map, Range.toList, A] at this
    exact this
  | .qual (.mono (.concat ρ₀ μ ρ₁ ρ₂)), .concat _ ρ₀ke ρ₁ke ρ₂ke κ'e containl containr (K := K')
      (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (Bₗ := Bₗ) (Bᵣ := Bᵣ) => by
    let .constr := κe
    apply Kinding.prod
    let A i : «Type» := match i with
      | 0 => [[∀ a : K' ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧)]]
      | 1 => [[∀ a : K' ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0]]
      | 2 => Bₗ
      | 3 => Bᵣ
      | _ => .list []
    let Δwf := Γwe.soundness
    let A₀k := ρ₀ke.soundness Γwe κ'e.row
    let A₁k := ρ₁ke.soundness Γwe κ'e.row
    let A₂k := ρ₂ke.soundness Γwe κ'e.row
    have := Kinding.list (Δ := Δ) (A := A) (K := .star) (n := 4)
      fun
        | 0, _ => .concat_evidence Δwf A₀k A₁k A₂k
        | 1, _ => .elim_evidence Δwf A₀k A₁k A₂k
        | 2, _ => containl.soundness Γwe .constr
        | 3, _ => containr.soundness Γwe .constr
    simp [Range.map, Range.toList, A] at this
    exact this
  | .qual (.mono (.typeClass _ τ)),
    .tc Γcw inΓc τke (κ := κ') (A := A') (Aₛ := Aₛ) (B := B) (n := n) => by
    let .constr := κe
    apply Kinding.prod
    let A'' i := if i = 0 then A'.Type_open B else (Aₛ (i - 1)).Type_open B
    have := Kinding.list (Δ := Δ) (n := n + 1) (A := A'') (K := .star) ?h
    rw [List.map_singleton_flatten] at *
    rw [Range.toList, if_neg (nomatch ·), if_pos (Nat.zero_lt_succ _), List.map] at this
    simp only at this
    dsimp only [A''] at this
    rw [if_pos rfl, ← Range.map_shift (Nat.le_refl 1), Nat.sub_self, Nat.add_sub_cancel] at this
    exact this
    intro i ⟨_, iltnsucc⟩
    dsimp only [A'']
    let ⟨K', κ'e⟩ := κ'.Elaboration_total
    let Bk := τke.soundness Γwe κ'e
    split
    · case isTrue h =>
      let ⟨a, anin⟩ := Γ.typeVarDom ++ ↑A'.freeTypeVars |>.exists_fresh
      let ⟨aninΓ, aninA'⟩ := List.not_mem_append'.mp anin
      let ⟨A'k, _⟩ := Γcw.KindingAndElaboration_of_ClassEnvironment_in inΓc κ'e a
      exact A'k.weakening (Γwe.soundness.typeVarExt <| Γwe.TypeVarNotInDom_preservation aninΓ)
        (Δ'' := .empty) |>.Type_open_preservation (Δ' := .empty) aninA' Bk
    · case isFalse h =>
      let ⟨a, anin⟩ := Γ.typeVarDom ++ ↑(Aₛ (i - 1)).freeTypeVars |>.exists_fresh
      let ⟨aninΓ, aninAₛ⟩ := List.not_mem_append'.mp anin
      let ⟨_, Aₛke⟩ := Γcw.KindingAndElaboration_of_ClassEnvironment_in inΓc κ'e a
      rw [Nat.add_comm] at iltnsucc
      have : i - 1 < n := Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h) iltnsucc
      exact Aₛke (i - 1) ⟨Nat.zero_le _, this⟩
        |>.weakening (Γwe.soundness.typeVarExt <| Γwe.TypeVarNotInDom_preservation aninΓ)
          (Δ'' := .empty) |>.Type_open_preservation (Δ' := .empty) aninAₛ Bk
  | .qual (.mono (.all (.mk κ ψ) ρ)), .all I ψke κe' ρke =>
    let .constr := κe
    let Aopki : «F⊗⊕ω».Kinding .. := .lam (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      ψke a aninI |>.soundness (Γwe.typeExt aninΓ κe') .constr
    .prod <| .listApp Aopki <| ρke.soundness Γwe κe'.row
  | .qual (.mono (.ind ρ)), .ind I₀ I₁ ρke κ'e Bᵣke Bₗke =>
    let .constr := κe
    let ⟨aₗ, aₗnin⟩ := Γ.typeVarDom ++ I₀ |>.exists_fresh
    let ⟨aₗninΓ, aₗnin₀⟩ := List.not_mem_append'.mp aₗnin
    let Γₗ := Γ.typeExt aₗ _
    let I₀ₗ : List TypeVarId := aₗ :: I₀
    let ⟨aₜ, aₜnin⟩ := Γₗ.typeVarDom ++ I₀ₗ |>.exists_fresh
    let ⟨aₜninΓ, aₜnin₀⟩ := List.not_mem_append'.mp aₜnin
    let Γₗₜ := Γₗ.typeExt aₜ _
    let I₀ₗₜ : List TypeVarId := aₜ :: I₀ₗ
    let ⟨aₚ, aₚnin⟩ := Γₗₜ.typeVarDom ++ I₀ₗₜ |>.exists_fresh
    let ⟨aₚninΓ, aₚnin₀⟩ := List.not_mem_append'.mp aₚnin
    let Γₗₜₚ := Γₗₜ.typeExt aₚ _
    let I₀ₗₜₚ : List TypeVarId := aₚ :: I₀ₗₜ
    let ⟨aᵢ, aᵢnin⟩ := Γₗₜₚ.typeVarDom ++ I₀ₗₜₚ ++ I₁ |>.exists_fresh
    let ⟨aᵢninΓₗₜₚ₀, aᵢnin₁⟩ := List.not_mem_append'.mp aᵢnin
    let ⟨aᵢninΓₗₜₚ, aᵢnin₀⟩ := List.not_mem_append'.mp aᵢninΓₗₜₚ₀
    let aᵢninΓ := List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons
      <| List.not_mem_of_not_mem_cons <| aᵢninΓₗₜₚ
    let Γₗₜₚᵢ := Γₗₜₚ.typeExt aᵢ _
    let I₀ₗₜₚᵢ : List TypeVarId := aᵢ :: I₀ₗₜₚ
    let I₁ᵢ : List TypeVarId := aᵢ :: I₁
    let ⟨aₙ, aₙnin⟩ := Γₗₜₚᵢ.typeVarDom ++ I₀ₗₜₚᵢ ++ I₁ᵢ |>.exists_fresh
    let ⟨aₙninΓₗₜₚᵢ₀, aₙnin₁⟩ := List.not_mem_append'.mp aₙnin
    let ⟨aₙninΓₗₜₚᵢ, aₙnin₀⟩ := List.not_mem_append'.mp aₙninΓₗₜₚᵢ₀
    let ⟨aₙneaᵢ, aₙninΓₗₜₚ⟩ := List.ne_and_not_mem_of_not_mem_cons aₙninΓₗₜₚᵢ
    let aₙninΓ := List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons
      <| List.not_mem_of_not_mem_cons <| aₙninΓₗₜₚ
    let aₙninΓᵢ := List.not_mem_cons_of_ne_of_not_mem aₙneaᵢ aₙninΓ
    let Γₗₜₚᵢₙwe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κ'e |>.typeExt aₚninΓ κ'e.row
      |>.typeExt aᵢninΓₗₜₚ κ'e.row |>.typeExt aₙninΓₗₜₚᵢ κ'e.row
    let Γᵢₙwe := Γwe.typeExt aᵢninΓ κ'e.row |>.typeExt aₙninΓᵢ κ'e.row
    .ind_evidence Γwe.soundness
      (Bᵣke aₗ aₗnin₀ aₜ aₜnin₀ aₚ aₚnin₀ aᵢ aᵢnin₀ aₙ aₙnin₀ |>.soundness Γₗₜₚᵢₙwe .constr)
      (Bₗke aᵢ aᵢnin₁ aₙ aₙnin₁ |>.soundness Γᵢₙwe .constr)
  | .qual (.mono (.split «λτ» ρ₀ ρ₁ ρ₂)), σke =>
    let .split concatke := σke
    concatke.soundness Γwe κe
termination_by Γ.sizeOf' + σ.sizeOf'
decreasing_by
  all_goals simp_arith [List.mapMem]
  · case _ ξ _ τ _ _ _ _ _ _ =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply List.le_sum_of_mem'
    rw [Std.Range.map_eq_of_eq_of_mem (by
          intro _ _
          simp only [Function.comp]
          rw [List.map_singleton]
        ), List.map_singleton_flatten]
    exact Range.mem_map_of_mem imem
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _

theorem TypeEnvironment.WellFormednessAndElaboration.soundness (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : [[⊢ Δ]] :=
  match Γwe with
  | .empty => .empty
  | .typeExt Γ'we anin κe => Γ'we.soundness.typeVarExt <| Γ'we.TypeVarNotInDom_preservation anin
  | .termExt Γ'we xnin σke =>
    Γ'we.soundness.termVarExt (Γ'we.TermVarNotInDom_preservation xnin) (σke.soundness Γ'we .star)
  | .constrExt Γ'we xnin ψke =>
    Γ'we.soundness.termVarExt (Γ'we.TermVarNotInDom_preservation xnin) (ψke.soundness Γ'we .constr)
termination_by Γ.sizeOf'

end

end TabularTypeInterpreter
