import TabularTypeInterpreter.Lemmas.Type

namespace TabularTypeInterpreter.TypeEnvironment.WellFormednessAndElaboration

theorem KindingAndElaboration_of_TermVarIn (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (xσinΓ : [[x : σ ∈ Γ]])
  : ∃ A, [[Γc; Γ ⊢ σ : * ⇝ A]] :=
  match Γwe, xσinΓ with
  | Γwe@(.typeExt Γ'we ..), .typeExt xσinΓ' =>
    let ⟨_, σke'⟩ := Γ'we.KindingAndElaboration_of_TermVarIn xσinΓ'
    ⟨_, σke'.weakening Γwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)⟩
  | Γwe@(.termExt _ _ σke), .head =>
    ⟨_, σke.weakening Γwe (Γ' := .termExt .empty ..) (Γ'' := .empty)⟩
  | Γwe@(.termExt Γ'we ..), .termExt _ xσinΓ' =>
    let ⟨_, σke'⟩ := Γ'we.KindingAndElaboration_of_TermVarIn xσinΓ'
    ⟨_, σke'.weakening Γwe (Γ' := .termExt .empty ..) (Γ'' := .empty)⟩
  | Γwe@(.constrExt Γ'we ..), .constrExt _ xσinΓ' =>
    let ⟨_, σke'⟩ := Γ'we.KindingAndElaboration_of_TermVarIn xσinΓ'
    ⟨_, σke'.weakening Γwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)⟩

theorem TermVarIn_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  (xσinΓ : [[x : σ ∈ Γ]]) (σke : [[Γc; Γ ⊢ σ : * ⇝ A]]) : [[x : A ∈ Δ]] := by
  match Γwe, xσinΓ with
  | Γwe@(.typeExt Γ'we ..), .typeExt xσinΓ' =>
    let ⟨_, σke'⟩ := Γ'we.KindingAndElaboration_of_TermVarIn xσinΓ'
    rcases σke.deterministic <| σke'.weakening Γwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact Γ'we.TermVarIn_preservation xσinΓ' σke' |>.typeVarExt
  | Γwe@(.termExt _ _ σke'), .head =>
    rcases σke.deterministic <| σke'.weakening Γwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact .head
  | Γwe@(.termExt Γ'we ..), .termExt xnex' xσinΓ' =>
    let ⟨_, σke'⟩ := Γ'we.KindingAndElaboration_of_TermVarIn xσinΓ'
    rcases σke.deterministic <| σke'.weakening Γwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact Γ'we.TermVarIn_preservation xσinΓ' σke' |>.termVarExt xnex'
  | Γwe@(.constrExt Γ'we ..), .constrExt xnex' xσinΓ' =>
    let ⟨_, σke'⟩ := Γ'we.KindingAndElaboration_of_TermVarIn xσinΓ'
    rcases σke.deterministic <| σke'.weakening Γwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact Γ'we.TermVarIn_preservation xσinΓ' σke' |>.termVarExt xnex'

end TabularTypeInterpreter.TypeEnvironment.WellFormednessAndElaboration
