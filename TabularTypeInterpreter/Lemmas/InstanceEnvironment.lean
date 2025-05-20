import TabularTypeInterpreter.Lemmas.ClassEnvironment
import TabularTypeInterpreter.Semantics.InstanceEnvironment

namespace TabularTypeInterpreter

open Std

namespace InstanceEnvironment.WellFormedness

theorem weakening (Γᵢw : [[Γc ⊢ Γᵢ]]) (ΓcΓc'w : [[⊢c Γc, Γc']]) : [[Γc, Γc' ⊢ Γᵢ]] := match Γᵢw with
  | .empty => .empty
  | .ext Γᵢ'w γcin ψke τke κ₁e Ety Eₛty => Γᵢ'w.weakening ΓcΓc'w |>.ext (ΓcΓc'w.In_append_inl γcin)
      (ψke · · · |>.class_weakening ΓcΓc'w) (τke · |>.class_weakening ΓcΓc'w) κ₁e Ety Eₛty

theorem In_inversion {TC} (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]])
  (γᵢin : [[(∀ </ a@k : κ₁@k // k in [:o] notex />. </ ψ@j ⇝ x@j // j in [:l] notex /> ⇒ TC τ) ⇝ E; </ Eₛ@i // i in [:n] notex /> ∈ Γᵢ]])
  : ∃ TCₛ Aₛ κ₀ m σ A B B' K₁,
    [[(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ₀) ↦ m : σ ⇝ A ∈ Γc]] ∧
    (∀ j ∈ [:l], ∀ a : { a : Nat → TypeVarId // a.Injective' }, [[Γc; ε,, </ a@k : κ₁@k // k in [:o] notex /> ⊢ ψ@j^^^a#o : C ⇝ B@j^^^a#o]]) ∧
    (∀ a : { a : Nat → TypeVarId // a.Injective' }, [[Γc; ε,, </ a@k : κ₁@k // k in [:o] notex /> ⊢ τ^^^a#o : κ₀ ⇝ B'^^^a#o]]) ∧
    (∀ k ∈ [:o], [[⊢ κ₁@k ⇝ K₁@k]]) ∧
    (∀ a : { a : Nat → «F⊗⊕ω».TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, [[ε,, </ a@k : K₁@k // k in [:o] notex />,,, </ x@j : B@j^^^a#o // j in [:l] notex /> ⊢ E^^^x#l^^^a#o : A^^(B'^^^a#o)/a]]) ∧
    (∀ i ∈ [:n], ∀ a : { a : Nat → «F⊗⊕ω».TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, [[ε,, </ a@k : K₁@k // k in [:o] notex />,,, </ x@j : B@j^^^a#o // j in [:l] notex /> ⊢ Eₛ@i^^^x#l^^^a#o : Aₛ@i^^(B'^^^a#o)/a]]) := by
  generalize γᵢeq : InstanceEnvironmentEntry.mk .. = γᵢ at γᵢin
  match γᵢin with
  | .head =>
    let .ext _ γcin ψke τke κ₁e Ety Eₛty (κ₁ := κ₁') := Γᵢw
    rcases InstanceEnvironmentEntry.mk.inj γᵢeq with ⟨κ₁eq, ψeq, rfl, rfl, rfl, Eₛeq⟩
    let κ₁eq' := InstanceEnvironmentEntryTypeVars.mk.inj κ₁eq
    let oeq : List.length (Range.map ..) = List.length _ := by rw [κ₁eq']
    rw [Range.map, Range.map, List.length_map, List.length_map, Range.length_toList,
        Range.length_toList] at oeq
    cases oeq
    let ψeq' := InstanceEnvironmentEntryConstrs.mk.inj ψeq
    let leq : List.length (Range.map ..) = List.length _ := by rw [ψeq']
    rw [Range.map, Range.map, List.length_map, List.length_map, Range.length_toList,
        Range.length_toList] at leq
    cases leq
    let neq : List.length (Range.map ..) = List.length _ := by rw [Eₛeq]
    rw [Range.map, Range.map, List.length_map, List.length_map, Range.length_toList,
        Range.length_toList] at neq
    cases neq
    rw [Range.map, Range.map] at κ₁eq
    exact ⟨
      _, _, _, _, _, _, _, _, _, γcin,
      by
        intro j mem a
        rw [InstanceEnvironmentEntryConstr.mk.inj <| Range.eq_of_mem_of_map_eq ψeq' j mem,
            Range.map_eq_of_eq_of_mem'' (by
              intro k mem
              show _ = (↑(a k), κ₁' k)
              rw [Range.eq_of_mem_of_map_eq κ₁eq' k mem]
            )]
        exact ψke j mem a,
      by
        intro a
        rw [Range.map_eq_of_eq_of_mem'' (by
          intro k mem
          show _ = (↑(a k), κ₁' k)
          rw [Range.eq_of_mem_of_map_eq κ₁eq' k mem]
        )]
        exact τke a,
      by
        intro k mem
        rw [Range.eq_of_mem_of_map_eq κ₁eq' k mem]
        exact κ₁e k mem,
      Ety,
      by
        intro i mem a x
        rw [Range.eq_of_mem_of_map_eq Eₛeq i mem]
        exact Eₛty i mem a x
    ⟩
  | .ext γᵢin' =>
    let .ext Γᵢ'w .. := Γᵢw
    cases γᵢeq
    exact Γᵢ'w.In_inversion Γcw γᵢin'

end InstanceEnvironment.WellFormedness

end TabularTypeInterpreter
