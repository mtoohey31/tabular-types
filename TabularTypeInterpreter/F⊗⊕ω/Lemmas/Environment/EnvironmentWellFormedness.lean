import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment

theorem TabularTypeInterpreter.«F⊗⊕ω».EnvironmentWellFormedness.to_Kinding_of_TermVarIn
  (Δwf : [[⊢ Δ]]) (xAinΔ : [[x : A ∈ Δ]]) : [[Δ ⊢ A : *]] := match Δwf with
  | .empty => nomatch xAinΔ
  | .typeVarExt Δ'wf aninΔ' (Δ := Δ') =>
    let .typeVarExt xAinΔ' := xAinΔ
    Δ'wf.to_Kinding_of_TermVarIn xAinΔ' |>.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) <|
      Δ'wf.typeVarExt aninΔ'
  | .termVarExt Δ'wf x'ninΔ' A'ki (Δ := Δ') => match xAinΔ with
    | .head =>
      A'ki.weakening (Δ' := .termExt .empty ..) (Δ'' := .empty) <| Δ'wf.termVarExt x'ninΔ' A'ki
    | .termVarExt xAinΔ' _ =>
      Δ'wf.to_Kinding_of_TermVarIn xAinΔ' |>.weakening (Δ' := .termExt .empty ..) (Δ'' := .empty) <|
        Δ'wf.termVarExt x'ninΔ' A'ki
