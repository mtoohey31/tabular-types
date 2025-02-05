import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter

open Std

theorem TypeScheme.KindingAndElaboration.class_weakening
  : [[Γc; Γ ⊢ σ : κ ⇝ A]] → [[⊢c Γc, Γc']] → [[Γc, Γc'; Γ ⊢ σ : κ ⇝ A]] := sorry

namespace ClassEnvironment

namespace WellFormedness

theorem ext_eliml (Γcγcw : [[⊢c Γc, γc]]) : [[⊢c Γc]] :=
  let .ext Γcw .. := Γcγcw
  Γcw

theorem of_ClassEnvironment_in {TC} (Γcw : [[⊢c Γc]])
  (TCin : [[(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc]])
  : ∃ K, [[⊢ κ ⇝ K]] ∧ (∀ a, [[Γc; ε, a : κ ⊢ σ^a : * ⇝ A^a]]) ∧ (∀ a, [[ε, a : K ⊢ A^a : *]]) ∧
    (∀ a, ∀ i ∈ [:n], [[Γc; ε, a : κ ⊢ TCₛ@i a : C ⇝ Aₛ@i^a]]) ∧
    (∀ a, ∀ i ∈ [:n], [[ε, a : K ⊢ Aₛ@i^a : *]]) := by
  generalize γceq : ClassEnvironmentEntry.mk .. = γc at TCin
  match TCin with
  | .head =>
    let Γcw@(ext _ _ _ κe σke Ake TCₛke Aₛki) := Γcw
    injection γceq with TCₛAₛeq TCeq κeq meq σeq Aeq
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at TCₛAₛeq
    let length_eq : List.length (List.map ..) = List.length _ := by rw [TCₛAₛeq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at length_eq
    cases length_eq
    cases κeq
    cases σeq
    cases Aeq
    apply Exists.intro _
    constructor
    · exact κe
    · constructor
      · exact (σke · |>.class_weakening Γcw (Γc' := .ext .empty _))
      · constructor
        · exact Ake
        · constructor
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := Prod.mk.inj <| Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [TCₛeq, Aₛeq]
            exact TCₛke i mem a |>.class_weakening Γcw (Γc' := .ext .empty _)
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := Prod.mk.inj <| Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [Aₛeq]
            exact Aₛki i mem a
  | .ext TCin' TCneTC' mnem' (TC' := TC') =>
    generalize ClassEnvironmentEntry.mk _ TC' .. = γc at *
    let Γcw@(ext Γcw' ..) := Γcw
    let ⟨_, κe, σke, Aki, TCₛke, Aₛki⟩ := Γcw'.of_ClassEnvironment_in TCin'
    injection γceq with TCₛAₛeq TCeq κeq meq σeq Aeq
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at TCₛAₛeq
    let length_eq : List.length (List.map ..) = List.length _ := by rw [TCₛAₛeq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at length_eq
    cases length_eq
    cases κeq
    cases σeq
    cases Aeq
    apply Exists.intro _
    constructor
    · exact κe
    · constructor
      · exact (σke · |>.class_weakening Γcw (Γc' := .ext .empty _))
      · constructor
        · exact Aki
        · constructor
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := Prod.mk.inj <| Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [TCₛeq, Aₛeq]
            exact TCₛke a i mem |>.class_weakening Γcw (Γc' := .ext .empty _)
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := Prod.mk.inj <| Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [Aₛeq]
            exact Aₛki a i mem

end WellFormedness

theorem In.deterministic (γc₀in : [[γc₀ ∈ Γc]]) (γc₁in : [[γc₁ ∈ Γc]]) (eq : γc₀.2 = γc₁.2)
  : γc₀ = γc₁ := by
  cases γc₀in
  · case head =>
    cases γc₁in
    · case head => rfl
    · case ext ne _ _ =>
      cases eq
      nomatch ne
  · case ext TC' _ _ _ _ _ _ _ γc₀in' ne _ =>
    generalize γceq : ClassEnvironmentEntry.mk _ TC' .. = γc at *
    cases γc₁in
    · case head =>
      cases eq
      cases γceq
      nomatch ne
    · case ext γc₁in' =>
      exact γc₀in'.deterministic γc₁in' eq

end ClassEnvironment

end TabularTypeInterpreter
