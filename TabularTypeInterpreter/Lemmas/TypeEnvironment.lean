import Aesop
import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter.TypeEnvironment

theorem append_empty (Γ : TypeEnvironment) : Γ.append empty = Γ := rfl

theorem empty_append (Γ : TypeEnvironment) : append empty Γ = Γ := by
  match Γ with
  | empty => rfl
  | typeExt Γ' .. | termExt Γ' .. | constrExt Γ' .. => rw [append, Γ'.empty_append]

theorem typeVarDom_append : (append Γ Γ').typeVarDom = Γ'.typeVarDom ++ Γ.typeVarDom := by
  match Γ' with
  | empty => rw [append, typeVarDom, List.nil_append]
  | typeExt .. => rw [append, typeVarDom, typeVarDom_append, typeVarDom, List.cons_append]
  | termExt .. | constrExt .. => rw [append, typeVarDom, typeVarDom_append, typeVarDom]

namespace WellFormednessAndElaboration

theorem TypeVarIn_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  (aκinΓ : [[a : κ ∈ Γ]]) (κe : [[⊢ κ ⇝ K]]) : [[a : K ∈ Δ]] :=
  match Γwe, aκinΓ with
  | .typeExt _ _ κe' (K := K'), .head => let .refl _ := κe.deterministic κe'; .head
  | .typeExt Γ'we _ _ (a := a') , .typeExt anea'' aκinΓ' =>
    Γ'we.TypeVarIn_preservation aκinΓ' κe |>.typeVarExt anea''
  | .termExt Γ'we .., .termExt aκinΓ' => Γ'we.TypeVarIn_preservation aκinΓ' κe |>.termVarExt
  | .constrExt Γ'we .., .constrExt aκinΓ' => Γ'we.TypeVarIn_preservation aκinΓ' κe |>.termVarExt

theorem TypeVarNotInDom_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (anin : [[a ∉ dom(Γ)]])
  : [[a ∉ dom(Δ)]] := fun ainΔ => match Γwe with
  | .empty => nomatch ainΔ
  | .typeExt Γ'we .. => match List.mem_cons.mp ainΔ with
    | .inl (.refl _) => anin <| .head _
    | .inr ainΔ' => Γ'we.TypeVarNotInDom_preservation (List.not_mem_of_not_mem_cons anin) ainΔ'
  | .termExt Γ'we .. | .constrExt Γ'we .. => Γ'we.TypeVarNotInDom_preservation anin ainΔ

theorem TermVarNotInDom_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (xnin : [[x ∉ dom'(Γ)]])
  : [[x ∉ dom(Δ)]] := fun xinΔ => match Γwe with
  | .empty => nomatch xinΔ
  | .typeExt Γ'we .. => Γ'we.TermVarNotInDom_preservation xnin xinΔ
  | .termExt Γ'we .. | .constrExt Γ'we .. => match List.mem_cons.mp xinΔ with
    | .inl (.refl _) => xnin <| .head _
    | .inr xinΔ' => Γ'we.TermVarNotInDom_preservation (List.not_mem_of_not_mem_cons xnin) xinΔ'

theorem append_left_elim (ΓΓ'we : [[Γc ⊢ Γ, Γ' ⇝ Δ]]) : ∃ Δ', [[Γc ⊢ Γ ⇝ Δ']] := match Γ' with
  | .empty => ⟨_, ΓΓ'we⟩
  | .termExt .. => let .termExt ΓΓ''we .. := ΓΓ'we; ΓΓ''we.append_left_elim
  | .typeExt .. => let .typeExt ΓΓ''we .. := ΓΓ'we; ΓΓ''we.append_left_elim
  | .constrExt .. => let .constrExt ΓΓ''we .. := ΓΓ'we; ΓΓ''we.append_left_elim

end WellFormednessAndElaboration

namespace TypeVarIn

theorem append_elim (aκin : [[a : κ ∈ Γ, Γ']])
  : ([[a : κ ∈ Γ]] ∧ [[a ∉ dom(Γ')]]) ∨ [[a : κ ∈ Γ']] := match Γ' with
  | .empty => .inl ⟨aκin, (nomatch ·)⟩
  | .typeExt .. => match aκin with
    | head => .inr head
    | typeExt ne aκin' => match aκin'.append_elim with
      | .inl ⟨aκinΓ, aκninΓ''⟩ =>
        .inl <| ⟨aκinΓ, fun | .head _ => nomatch ne | .tail _ mem => aκninΓ'' mem⟩
      | .inr aκinΓ'' => .inr <| aκinΓ''.typeExt ne
  | .termExt .. => let .termExt aκin' .. := aκin; aκin'.append_elim.imp_right termExt
  | .constrExt .. => let .constrExt aκin' .. := aκin; aκin'.append_elim.imp_right constrExt

theorem append_inl (aκin : [[a : κ ∈ Γ]]) (anin : [[a ∉ dom(Γ')]]) : [[a : κ ∈ Γ, Γ']] := by
  match Γ' with
  | .empty => exact aκin
  | .typeExt .. =>
    let ⟨ne, anin'⟩ := List.not_mem_cons.mp anin
    exact aκin.append_inl anin' |>.typeExt ne
  | .termExt .. =>
    rw [TypeVarNotInDom, typeVarDom] at anin
    exact aκin.append_inl anin |>.termExt
  | .constrExt .. =>
    rw [TypeVarNotInDom, typeVarDom] at anin
    exact aκin.append_inl anin |>.constrExt

theorem append_inr : [[a : κ ∈ Γ]] → [[a : κ ∈ Γ', Γ]]
  | head => .head
  | typeExt ne aκin' => aκin'.append_inr.typeExt ne
  | termExt aκin' => aκin'.append_inr.termExt
  | constrExt aκin' => aκin'.append_inr.constrExt

theorem not_of_NotInDom (anin : [[a ∉ dom(Γ)]]) (aκin : [[a : κ ∈ Γ]]) : False := by match Γ with
  | .empty => nomatch aκin
  | .typeExt .. => match aκin with
    | .head => nomatch List.ne_of_not_mem_cons anin
    | .typeExt ne aκin' => exact aκin'.not_of_NotInDom <| List.not_mem_of_not_mem_cons anin
  | .termExt .. =>
    let .termExt aκin' := aκin
    rw [TypeVarNotInDom, typeVarDom] at anin
    exact aκin'.not_of_NotInDom anin
  | .constrExt .. =>
    let .constrExt aκin' := aκin
    rw [TypeVarNotInDom, typeVarDom] at anin
    exact aκin'.not_of_NotInDom anin

theorem append_elim_left (aκin : [[a : κ ∈ Γ, Γ']]) (anin : [[a ∉ dom(Γ')]]) : [[a : κ ∈ Γ]] :=
  match aκin.append_elim with
  | .inl ⟨aκinΓ, _⟩ => aκinΓ
  | .inr aκinΓ' => nomatch aκinΓ'.not_of_NotInDom anin

theorem deterministic (aκ₀in : [[a : κ₀ ∈ Γ]]) (aκ₁in : [[a : κ₁ ∈ Γ]])
  : κ₀ = κ₁ := match Γ with
  | .empty => nomatch aκ₀in
  | .typeExt .. => by
    cases aκ₀in
    · case head =>
      cases aκ₁in
      · case head => rfl
      · case typeExt => contradiction
    · case typeExt aκ₀in' _ =>
      cases aκ₁in
      · case head => contradiction
      · case typeExt aκ₁in' _ => exact aκ₀in'.deterministic aκ₁in'
  | .termExt .. =>
    let .termExt aκ₀in' := aκ₀in
    let .termExt aκ₁in' := aκ₁in
    aκ₀in'.deterministic aκ₁in'
  | .constrExt .. =>
    let .constrExt aκ₀in' := aκ₀in
    let .constrExt aκ₁in' := aκ₁in
    aκ₀in'.deterministic aκ₁in'

theorem TypeVar_subst_preservation : [[a : κ ∈ Γ]] → [[a : κ ∈ Γ [τ / a'] ]]
  | .head => .head
  | .typeExt ne aκin' => aκin'.TypeVar_subst_preservation.typeExt ne
  | .termExt aκin' => aκin'.TypeVar_subst_preservation.termExt
  | .constrExt aκin' => aκin'.TypeVar_subst_preservation.constrExt

end TypeVarIn

theorem TypeVarNotInDom.TypeVar_subst_preservation : [[a ∉ dom(Γ)]] → [[a ∉ dom(Γ [τ / a'])]] := by
  induction Γ <;> aesop (add simp [TypeVarNotInDom, typeVarDom])

end TabularTypeInterpreter.TypeEnvironment
