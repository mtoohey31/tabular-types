import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter.ClassEnvironment.WellFormedness

theorem ext_eliml (Γcγcw : [[⊢c Γc, γc]]) : [[⊢c Γc]] :=
  let .ext Γcw .. := Γcγcw
  Γcw

theorem KindingAndElaboration_of_ClassEnvironment_in {TC} (Γcw : [[⊢c Γc]])
  (TCin : [[(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc]]) (κe : [[⊢ κ ⇝ K]])
  : ∀ a, [[ε, a : K ⊢ A^a : *]] ∧ ∀ i ∈ [:n], [[ε, a : K ⊢ Aₛ@i^a : *]] := by
  intro a
  generalize γceq : ClassEnvironmentEntry.mk
    (List.map (fun i => [(TCₛ i, Aₛ i)]) (Coe.coe [:n])).flatten TC κ m σ A = γc at TCin
  match TCin with
  | .head =>
    let .ext _ κ'e _ Aopki _ Aₛopki := Γcw
    let ⟨TCₛAₛeq, _, κeqκ', _, _, AeqA'⟩ := ClassEnvironmentEntry.mk.inj γceq
    cases κeqκ'
    cases AeqA'
    cases κe.deterministic κ'e
    exact ⟨
      Aopki a,
      fun i inin => by
        rw [List.map_singleton_flatten, List.map_singleton_flatten] at TCₛAₛeq
        let length_eq : List.length (List.map _ _) = List.length _ := by rw [TCₛAₛeq]
        dsimp [Coe.coe] at length_eq
        rw [List.length_map, List.length_map, Std.Range.length_toList, Std.Range.length_toList,
            Nat.sub_zero, Nat.sub_zero] at length_eq
        cases length_eq
        rw [And.right <| Prod.mk.inj <| Std.Range.eq_of_mem_of_map_eq' TCₛAₛeq i inin]
        exact Aₛopki i inin a
    ⟩
  | .ext TCin' .. =>
    let ⟨TCₛAₛeq, _, κeqκ', _, _, AeqA'⟩ := ClassEnvironmentEntry.mk.inj γceq
    cases κeqκ'
    cases AeqA'
    let ⟨Aopki, Aₛopki⟩ :=
      Γcw.ext_eliml.KindingAndElaboration_of_ClassEnvironment_in TCin' κe a
    exact ⟨
      Aopki,
      fun i inin => by
        rw [List.map_singleton_flatten, List.map_singleton_flatten] at TCₛAₛeq
        let length_eq : List.length (List.map _ _) = List.length _ := by rw [TCₛAₛeq]
        dsimp [Coe.coe] at length_eq
        rw [List.length_map, List.length_map, Std.Range.length_toList, Std.Range.length_toList,
            Nat.sub_zero, Nat.sub_zero] at length_eq
        cases length_eq
        rw [And.right <| Prod.mk.inj <| Std.Range.eq_of_mem_of_map_eq' TCₛAₛeq i inin]
        exact Aₛopki i inin
    ⟩

end TabularTypeInterpreter.ClassEnvironment.WellFormedness
