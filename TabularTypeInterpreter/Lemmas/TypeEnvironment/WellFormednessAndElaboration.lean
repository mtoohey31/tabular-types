import TabularTypeInterpreter.Lemmas.Type.Basic
import TabularTypeInterpreter.Lemmas.Type.ToKinding

namespace TabularTypeInterpreter.TypeEnvironment.WellFormednessAndElaboration

open «F⊗⊕ω»
open Std

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

theorem KindingAndElaboration_of_ConstrIn (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (ψxinΓ : [[ψ ⇝ x ∈ Γ]])
  : ∃ A, [[Γc; Γ ⊢ ψ : C ⇝ A]] :=
  match Γwe, ψxinΓ with
  | Γwe@(.typeExt Γ'we ..), .typeExt ψxinΓ' =>
    let ⟨_, ψke'⟩ := Γ'we.KindingAndElaboration_of_ConstrIn ψxinΓ'
    ⟨_, ψke'.weakening Γwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)⟩
  | Γwe@(.constrExt _ _ ψke), .head =>
    ⟨_, ψke.weakening Γwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)⟩
  | Γwe@(.termExt Γ'we ..), .termExt _ ψxinΓ' =>
    let ⟨_, ψke'⟩ := Γ'we.KindingAndElaboration_of_ConstrIn ψxinΓ'
    ⟨_, ψke'.weakening Γwe (Γ' := .termExt .empty ..) (Γ'' := .empty)⟩
  | Γwe@(.constrExt Γ'we ..), .constrExt _ ψxinΓ' =>
    let ⟨_, ψke'⟩ := Γ'we.KindingAndElaboration_of_ConstrIn ψxinΓ'
    ⟨_, ψke'.weakening Γwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)⟩

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

theorem ConstrIn_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  (ψxinΓ : [[ψ ⇝ x ∈ Γ]]) (ψke : [[Γc; Γ ⊢ ψ : C ⇝ A]]) : [[x : A ∈ Δ]] := by
  match Γwe, ψxinΓ with
  | Γwe@(.typeExt Γ'we ..), .typeExt ψxinΓ' =>
    let ⟨_, ψke'⟩ := Γ'we.KindingAndElaboration_of_ConstrIn ψxinΓ'
    rcases ψke.deterministic <| ψke'.weakening Γwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact Γ'we.ConstrIn_preservation ψxinΓ' ψke' |>.typeVarExt
  | Γwe@(.termExt Γ'we ..), .termExt xnex' ψxinΓ' =>
    let ⟨_, ψke'⟩ := Γ'we.KindingAndElaboration_of_ConstrIn ψxinΓ'
    rcases ψke.deterministic <| ψke'.weakening Γwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact Γ'we.ConstrIn_preservation ψxinΓ' ψke' |>.termVarExt xnex'
  | Γwe@(.constrExt _ _ ψke'), .head =>
    rcases ψke.deterministic <| ψke'.weakening Γwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact .head
  | Γwe@(.constrExt Γ'we ..), .constrExt xnex' ψxinΓ' =>
    let ⟨_, ψke'⟩ := Γ'we.KindingAndElaboration_of_ConstrIn ψxinΓ'
    rcases ψke.deterministic <| ψke'.weakening Γwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
      with ⟨_, rfl⟩
    exact Γ'we.ConstrIn_preservation ψxinΓ' ψke' |>.termVarExt xnex'

theorem append_typeExt (ΓΓ'we : [[Γc ⊢ Γ, Γ' ⇝ Δ]]) (aninΓΓ' : [[a ∉ dom(Γ, Γ')]])
  (κe : [[⊢ κ ⇝ K]]) : ∃ Δ', [[Γc ⊢ Γ, a : κ, Γ' ⇝ Δ']] := by
  match Γ' with
  | .empty => exact ⟨_, ΓΓ'we.typeExt aninΓΓ' κe⟩
  | .typeExt Γ'' a' κ' =>
    let .typeExt ΓΓ''we a'ninΓΓ'' κ'e := ΓΓ'we
    rw [append, TypeVarNotInDom, typeVarDom] at aninΓΓ'
    let ⟨ane, aninΓΓ''⟩ := List.not_mem_cons.mp aninΓΓ'
    let ⟨_, ΓaΓ''we⟩ := ΓΓ''we.append_typeExt aninΓΓ'' κe
    rw [TypeVarNotInDom, typeVarDom_append] at a'ninΓΓ''
    let ⟨a'ninΓ'', a'ninΓ⟩ := List.not_mem_append'.mp a'ninΓΓ''
    let a'ninΓaΓ'' : [[a' ∉ dom(Γ, a : κ, Γ'')]] := by
      rw [TypeVarNotInDom, typeVarDom_append, typeVarDom]
      exact List.not_mem_append'.mpr ⟨
        a'ninΓ'',
        List.not_mem_cons.mpr ⟨ane.symm, a'ninΓ⟩,
      ⟩
    rw [append]
    exact ⟨_, ΓaΓ''we.typeExt a'ninΓaΓ'' κ'e⟩
  | .termExt Γ'' x σ =>
    let .termExt ΓΓ''we xninΓΓ'' σke := ΓΓ'we
    rw [append, TypeVarNotInDom, typeVarDom] at aninΓΓ'
    let ⟨_, ΓaΓ''we⟩ := ΓΓ''we.append_typeExt aninΓΓ' κe
    rw [append]
    rw [TermVarNotInDom, termVarDom_append] at xninΓΓ''
    let ⟨xninΓ, xninΓ''⟩ := List.not_mem_append'.mp xninΓΓ''
    let xninΓaΓ'' : [[x ∉ dom'(Γ, a : κ, Γ'')]] := by
      rw [TermVarNotInDom, termVarDom_append, termVarDom]
      exact List.not_mem_append'.mpr ⟨xninΓ, xninΓ''⟩
    rw [TypeEnvironment.typeExt_append_assoc] at ΓaΓ''we xninΓaΓ'' ⊢
    exact ⟨_, ΓaΓ''we.termExt xninΓaΓ'' <| σke.weakening ΓaΓ''we (Γ' := .typeExt .empty ..)⟩
  | .constrExt Γ'' ψ x =>
    let .constrExt ΓΓ''we xninΓΓ'' σke := ΓΓ'we
    rw [append, TypeVarNotInDom, typeVarDom] at aninΓΓ'
    let ⟨_, ΓaΓ''we⟩ := ΓΓ''we.append_typeExt aninΓΓ' κe
    rw [append]
    rw [TermVarNotInDom, termVarDom_append] at xninΓΓ''
    let ⟨xninΓ, xninΓ''⟩ := List.not_mem_append'.mp xninΓΓ''
    let xninΓaΓ'' : [[x ∉ dom'(Γ, a : κ, Γ'')]] := by
      rw [TermVarNotInDom, termVarDom_append, termVarDom]
      exact List.not_mem_append'.mpr ⟨xninΓ, xninΓ''⟩
    rw [TypeEnvironment.typeExt_append_assoc] at ΓaΓ''we xninΓaΓ'' ⊢
    exact ⟨_, ΓaΓ''we.constrExt xninΓaΓ'' <| σke.weakening ΓaΓ''we (Γ' := .typeExt .empty ..)⟩

theorem TypeVar_subst_id_of_NotInDom (Γwe : [[Γc ⊢ Γ, Γ' ⇝ Δ]]) (aninΓΓ' : [[a ∉ dom(Γ, Γ')]])
  : [[Γ, (Γ' [τ / a])]] = [[(Γ, Γ')]] := by
  match Γ' with
  | .empty => rw [TypeVar_subst]
  | .typeExt Γ' a' κ =>
    let .typeExt Γ'we .. := Γwe
    rw [TypeVarNotInDom, typeVarDom_append, typeVarDom, List.cons_append,
        ← typeVarDom_append] at aninΓΓ'
    let aninΓΓ'' := List.not_mem_of_not_mem_cons aninΓΓ'
    rw [TypeVar_subst, append, Γ'we.TypeVar_subst_id_of_NotInDom aninΓΓ'', append]
  | .termExt Γ' x σ =>
    let .termExt Γ'we _ σke := Γwe
    rw [TypeVarNotInDom, typeVarDom_append, typeVarDom, ← typeVarDom_append] at aninΓΓ'
    let aninσ := σke.not_in_freeTypeVars_of aninΓΓ'
    rw [TypeVar_subst, TypeScheme.TypeVar_subst_id_of_not_mem_freeTypeVars aninσ, append,
        Γ'we.TypeVar_subst_id_of_NotInDom aninΓΓ', append]
  | .constrExt Γ' ψ x =>
    let .constrExt Γ'we _ ψke := Γwe
    rw [TypeVarNotInDom, typeVarDom_append, typeVarDom, ← typeVarDom_append] at aninΓΓ'
    let aninψ := ψke.not_in_freeTypeVars_of aninΓΓ'
    rw [TypeVar_subst, Monotype.TypeVar_subst_id_of_not_mem_freeTypeVars aninψ, append,
        Γ'we.TypeVar_subst_id_of_NotInDom aninΓΓ', append]

theorem multiConstrExt (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (xninΓ : ∀ i, [[x@i ∉ dom'(Γ)]]) (xinj : x.Injective')
  (ψke : ∀ i ∈ [:n], [[Γc; Γ ⊢ ψ@i : C ⇝ A@i]])
  : [[Γc ⊢ Γ,,, </ ψ@i ⇝ x@i // i in [:n] /> ⇝ Δ,,, </ x@i : A@i // i in [:n] />]] := by
  match n with
  | 0 => rwa [Range.map_same_eq_nil, Range.map_same_eq_nil, TypeEnvironment.multiConstrExt,
              Environment.multiTermExt]
  | n' + 1 =>
    rw [Range.map_eq_cons_of_lt (Nat.zero_lt_succ _), Range.map_eq_cons_of_lt (Nat.zero_lt_succ _),
        TypeEnvironment.multiConstrExt, Environment.multiTermExt,
        ← Range.map_shift Nat.le.refl (j := 1), Nat.sub_self, Nat.succ_sub_one,
        ← Range.map_shift Nat.le.refl (j := 1), Nat.sub_self, Nat.succ_sub_one]
    let Γψ₀we := Γwe.constrExt (xninΓ 0) <| ψke 0 ⟨Nat.zero_le _, Nat.zero_lt_succ _, Nat.mod_one _⟩
    apply Γψ₀we.multiConstrExt _
      (fun _ _ eq => Nat.add_left_inj.mp <| xinj _ _ eq)
      (fun i mem => ψke (i + 1) ⟨Nat.zero_le _, Nat.add_lt_add_right mem.upper _, Nat.mod_one _⟩
        |>.weakening Γψ₀we (Γ' := .constrExt .empty ..) (Γ'' := .empty))
    intro i
    rw [TermVarNotInDom, termVarDom]
    exact List.not_mem_cons.mpr ⟨(Nat.succ_ne_zero _ <| xinj _ _ ·), xninΓ (i + 1)⟩

end TabularTypeInterpreter.TypeEnvironment.WellFormednessAndElaboration
