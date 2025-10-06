import TabularTypes.Lemmas.ClassEnvironment
import TabularTypes.Semantics.InstanceEnvironment

namespace TabularTypes

open Std

namespace InstanceEnvironment.WellFormedness

theorem weakening (Γᵢw : [[Γc ⊢ Γᵢ]]) (ΓcΓc'w : [[⊢c Γc, Γc']]) : [[Γc, Γc' ⊢ Γᵢ]] := match Γᵢw with
  | .empty => .empty
  | .ext Γᵢ'w γcin ψke τke κ'e Ety E'ty => Γᵢ'w.weakening ΓcΓc'w |>.ext (ΓcΓc'w.In_append_inl γcin)
      (ψke · · · |>.class_weakening ΓcΓc'w) (τke · |>.class_weakening ΓcΓc'w) κ'e Ety E'ty

theorem In_inversion {TC} (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]])
  (γᵢin : [[(∀ </ a@k : κ'@k // k in [:o] notex />. </ ψ@j ⇝ x@j // j in [:l] notex /> ⇒ TC τ) ⇝ E; </ E'@i // i in [:n] notex /> ∈ Γᵢ]])
  : ∃ TC' A' κ m σ A B B' K',
    [[(</ TC'@i a ⇝ A'@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc]] ∧
    (∀ j ∈ [:l], ∀ a : { a : Nat → TypeVarId // a.Injective' }, [[Γc; ε,, </ a@k : κ'@k // k in [:o] notex /> ⊢ ψ@j^^^a#o : C ⇝ B@j^^^a#o]]) ∧
    (∀ a : { a : Nat → TypeVarId // a.Injective' }, [[Γc; ε,, </ a@k : κ'@k // k in [:o] notex /> ⊢ τ^^^a#o : κ ⇝ B'^^^a#o]]) ∧
    (∀ k ∈ [:o], [[⊢ κ'@k ⇝ K'@k]]) ∧
    (∀ a : { a : Nat → «F⊗⊕ω».TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, [[ε,, </ a@k : K'@k // k in [:o] notex />,,, </ x@j : B@j^^^a#o // j in [:l] notex /> ⊢ E^^^x#l^^^a#o : A^^(B'^^^a#o)/a]]) ∧
    (∀ i ∈ [:n], ∀ a : { a : Nat → «F⊗⊕ω».TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, [[ε,, </ a@k : K'@k // k in [:o] notex />,,, </ x@j : B@j^^^a#o // j in [:l] notex /> ⊢ E'@i^^^x#l^^^a#o : A'@i^^(B'^^^a#o)/a]]) := by
  generalize γᵢeq : InstanceEnvironmentEntry.mk .. = γᵢ at γᵢin
  match γᵢin with
  | .head =>
    let .ext _ γcin ψke τke κ'e Ety E'ty (κ' := κ'') := Γᵢw
    rcases InstanceEnvironmentEntry.mk.inj γᵢeq with ⟨κ'eq, ψeq, rfl, rfl, rfl, E'eq⟩
    let κ'eq' := InstanceEnvironmentEntryTypeVars.mk.inj κ'eq
    let oeq : List.length (Range.map ..) = List.length _ := by rw [κ'eq']
    rw [Range.map, Range.map, List.length_map, List.length_map, Range.length_toList,
        Range.length_toList] at oeq
    cases oeq
    let ψeq' := InstanceEnvironmentEntryConstrs.mk.inj ψeq
    let leq : List.length (Range.map ..) = List.length _ := by rw [ψeq']
    rw [Range.map, Range.map, List.length_map, List.length_map, Range.length_toList,
        Range.length_toList] at leq
    cases leq
    let neq : List.length (Range.map ..) = List.length _ := by rw [E'eq]
    rw [Range.map, Range.map, List.length_map, List.length_map, Range.length_toList,
        Range.length_toList] at neq
    cases neq
    rw [Range.map, Range.map] at κ'eq
    exact ⟨
      _, _, _, _, _, _, _, _, _, γcin,
      by
        intro j mem a
        rw [InstanceEnvironmentEntryConstr.mk.inj <| Range.eq_of_mem_of_map_eq ψeq' j mem,
            Range.map_eq_of_eq_of_mem'' (by
              intro k mem
              show _ = (↑(a k), κ'' k)
              rw [Range.eq_of_mem_of_map_eq κ'eq' k mem]
            )]
        exact ψke j mem a,
      by
        intro a
        rw [Range.map_eq_of_eq_of_mem'' (by
          intro k mem
          show _ = (↑(a k), κ'' k)
          rw [Range.eq_of_mem_of_map_eq κ'eq' k mem]
        )]
        exact τke a,
      by
        intro k mem
        rw [Range.eq_of_mem_of_map_eq κ'eq' k mem]
        exact κ'e k mem,
      Ety,
      by
        intro i mem a x
        rw [Range.eq_of_mem_of_map_eq E'eq i mem]
        exact E'ty i mem a x
    ⟩
  | .ext γᵢin' =>
    let .ext Γᵢ'w .. := Γᵢw
    cases γᵢeq
    exact Γᵢ'w.In_inversion Γcw γᵢin'

end InstanceEnvironment.WellFormedness

end TabularTypes
