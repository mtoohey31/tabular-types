import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter.TypeEnvironment

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

end WellFormednessAndElaboration

theorem TypeVarIn.deterministic (aκ₀in : [[a : κ₀ ∈ Γ]]) (aκ₁in : [[a : κ₁ ∈ Γ]])
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

end TabularTypeInterpreter.TypeEnvironment
