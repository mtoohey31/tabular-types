import TabularTypeInterpreter.Lemmas.TypeEnvironment

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

theorem TypeScheme.KindingAndElaboration.Monotype_multi_open
  {a : { a : Nat → TypeVarId // a.Injective' }} (Γcw : [[⊢c Γc]]) (ΓΓ'we : [[Γc ⊢ Γ, Γ' ⇝ Δ]])
  (aninΓΓ' : ∀ i ∈ [:n], [[a@i ∉ dom(Γ, Γ')]])
  (aninτ : ∀ i ∈ [:n], a i ∉ τ.freeTypeVars)
  (aninτ' : ∀ i ∈ [:n], ∀ j < n, a i ∉ (τ' j).freeTypeVars)
  (aninA : ∀ i ∈ [:n], a i ∉ A.freeTypeVars)
  (aninB : ∀ i ∈ [:n], ∀ j < n, a i ∉ (B j).freeTypeVars)
  (τke : [[Γc; Γ,, </ a@i : κ'@i // i in [:n] />, Γ' ⊢ τ^^^a#n : κ ⇝ A^^^a#n]])
  (τ'ke : ∀ i ∈ [:n], [[Γc; Γ ⊢ τ'@i : κ'@i ⇝ B@i]])
  : [[Γc; Γ, Γ' ⊢ τ^^^^τ'@@i#n/a : κ ⇝ A^^^^B@@i#n/a]] := by
  match n with
  | 0 =>
    rw [Range.map_same_eq_nil, TypeEnvironment.multiTypeExt, Monotype.TypeVar_multi_open,
        Type.TypeVar_multi_open] at τke
    rw [Monotype.Monotype_multi_open, Type.Type_multi_open]
    exact τke
  | n' + 1 =>
    let mem : n' ∈ [:n'+1] := ⟨Nat.zero_le _, Nat.le.refl, Nat.mod_one _⟩
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), TypeEnvironment.multiTypeExt_snoc,
        Nat.succ_sub_one, TypeEnvironment.typeExt_append_assoc, Monotype.TypeVar_multi_open,
        Type.TypeVar_multi_open] at τke
    let ⟨_, κ'n'e⟩ := κ' n' |>.Elaboration_total
    let ⟨_, ΓaΓ'we⟩ := ΓΓ'we.append_typeExt (aninΓΓ' n' mem) κ'n'e
    rw [TypeEnvironment.typeExt_append_assoc] at ΓaΓ'we
    let aninΓan'Γ' : ∀ i ∈ [:n'], [[a@i ∉ dom(Γ, ε, a@n' : κ'@n', Γ')]] := by
      intro i mem
      let aᵢninΓΓ' := aninΓΓ' i ⟨Nat.zero_le _, Nat.lt_add_right _ mem.upper, Nat.mod_one _⟩
      rw [TypeEnvironment.TypeVarNotInDom, TypeEnvironment.typeVarDom_append] at aᵢninΓΓ' ⊢
      rw [TypeEnvironment.typeVarDom_append, TypeEnvironment.typeVarDom, TypeEnvironment.typeVarDom]
      let ⟨aᵢninΓ', aᵢninΓ⟩ := List.not_mem_append'.mp aᵢninΓΓ'
      let ane : a i ≠ a n' := by
        intro aeq
        rw [a.property _ _ aeq] at mem
        exact Nat.not_le.mpr mem.upper <| Nat.le_refl _
      exact List.not_mem_append'.mpr
        ⟨List.not_mem_append'.mpr ⟨aᵢninΓ', List.not_mem_singleton.mpr ane⟩, aᵢninΓ⟩
    have := Monotype_multi_open Γcw ΓaΓ'we aninΓan'Γ' (n := n')
      (fun _ mem => Monotype.not_mem_freeTypeVars_TypeVar_open_intro
        (aninτ _ ⟨Nat.zero_le _, Nat.lt_add_right _ mem.upper, Nat.mod_one _⟩)
        (fun eq => Nat.ne_of_lt mem.upper <| a.property _ _ eq))
      (aninτ' · ⟨Nat.zero_le _, Nat.lt_add_right _ ·.upper, Nat.mod_one _⟩ · <|
        Nat.lt_add_right _ ·)
      (fun _ mem => Type.not_mem_freeTypeVars_TypeVar_open_intro
        (aninA _ ⟨Nat.zero_le _, Nat.lt_add_right _ mem.upper, Nat.mod_one _⟩)
        (fun eq => Nat.ne_of_lt mem.upper <| a.property _ _ eq))
      (aninB · ⟨Nat.zero_le _, Nat.lt_add_right _ ·.upper, Nat.mod_one _⟩ · <|
        Nat.lt_add_right _ ·) τke <| by
      intro i mem
      exact τ'ke i ⟨Nat.zero_le _, mem.upper.trans Nat.le.refl, Nat.mod_one _⟩
    let τ'lc : ∀ i ≤ n', (τ' i).TypeVarLocallyClosed n' := by
      intro i ilen'
      let .qual (.mono τ'lc) := τ'ke i ⟨Nat.zero_le _, Nat.lt_succ_of_le ilen', Nat.mod_one _⟩
        |>.TypeVarLocallyClosed_of.weakening (n := n')
      rw [Nat.zero_add] at τ'lc
      exact τ'lc
    let .qual (.mono τ'ₙ'lc) := τ'ke n' mem
      |>.TypeVarLocallyClosed_of
    let ⟨_, Γwe⟩ := ΓΓ'we.append_left_elim
    let Blc : ∀ i ≤ n', (B i).TypeVarLocallyClosed n' := by
      intro i ilen'
      let ⟨_, κ'ᵢe⟩ := κ' i |>.Elaboration_total
      have := τ'ke i ⟨Nat.zero_le _, Nat.lt_succ_of_le ilen', Nat.mod_one _⟩
        |>.soundness Γcw Γwe κ'ᵢe |>.TypeVarLocallyClosed_of.weaken (n := n')
      rw [Nat.zero_add] at this
      exact this
    let ⟨_, κₙ'e⟩ := κ' n' |>.Elaboration_total
    let Bₙ'lc := τ'ke n' mem |>.soundness Γcw Γwe κₙ'e |>.TypeVarLocallyClosed_of
    rw [Monotype.TypeVar_open_Monotype_multi_open_comm Nat.le.refl τ'lc,
        Type.TypeVarLocallyClosed.TypeVar_open_Type_multi_open_comm Nat.le.refl Blc,
        ← TypeEnvironment.typeExt_append_assoc, ← QualifiedType.TypeVar_open,
        ← TypeScheme.TypeVar_open] at this
    rw [← TypeEnvironment.typeExt_append_assoc] at ΓaΓ'we
    rw [Monotype.Monotype_multi_open, Type.Type_multi_open]
    let aninΓΓ'' := aninΓΓ' n' mem
    rw [TypeEnvironment.TypeVarNotInDom, TypeEnvironment.typeVarDom_append] at aninΓΓ''
    let ⟨aninΓ', _⟩ := List.not_mem_append'.mp aninΓΓ''
    have := this.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
      (Monotype.not_mem_freeTypeVars_Monotype_multi_open_intro (aninτ _ mem)
        (aninτ' _ mem · <| Nat.lt_add_right _ ·))
      (Type.not_mem_freeTypeVars_Type_multi_open_intro (aninA _ mem)
        (aninB _ mem · <| Nat.lt_add_right _ ·)) <| τ'ke n' mem
    rw [TypeScheme.Monotype_open, QualifiedType.Monotype_open,
        ← Monotype.Monotype_open_Monotype_multi_open_comm Nat.le.refl τ'ₙ'lc τ'lc,
        ← Type.TypeVarLocallyClosed.Type_open_Type_multi_open_comm Nat.le.refl Bₙ'lc Blc,
        ΓΓ'we.TypeVar_subst_id_of_NotInDom <| aninΓΓ' n' mem] at this
    exact this

end TabularTypeInterpreter
