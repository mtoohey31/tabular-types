import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace Environment

theorem append_empty (Δ : Environment) : Δ.append empty = Δ := rfl

theorem empty_append (Δ : Environment) : append empty Δ = Δ := by
  match Δ with
  | empty => rfl
  | typeExt Δ' .. | termExt Δ' .. => rw [append, Δ'.empty_append]

theorem typeVarDom_append : (append Δ Δ').typeVarDom = Δ'.typeVarDom ++ Δ.typeVarDom := by
  match Δ' with
  | empty => rw [append, typeVarDom, List.nil_append]
  | typeExt .. => rw [append, typeVarDom, typeVarDom_append, typeVarDom, List.cons_append]
  | termExt .. => rw [append, typeVarDom, typeVarDom_append, typeVarDom]

end Environment

namespace TypeVarInEnvironment

theorem eq_of (aKinΔ : [[a : K ∈ Δ]]) : ∃ Δ' Δ'', Δ = [[(Δ', a : K, Δ'')]] := by
  match aKinΔ with
  | .head => exact ⟨_, .empty, rfl⟩
  | .typeVarExt aKinΔ' _ =>
    rcases aKinΔ'.eq_of with ⟨_, _, rfl⟩
    rw [← Environment.append]
    exact ⟨_, _, rfl⟩
  | .termVarExt aKinΔ' =>
    rcases aKinΔ'.eq_of with ⟨_, _, rfl⟩
    rw [← Environment.append]
    exact ⟨_, _, rfl⟩

theorem TypeVarInDom_of (aKinΔ : [[a : K ∈ Δ]]) : [[a ∈ dom(Δ)]] :=
  match aKinΔ with
  | .head => .head _
  | .typeVarExt aKinΔ' anea' => .tail _ aKinΔ'.TypeVarInDom_of
  | .termVarExt aKinΔ' => aKinΔ'.TypeVarInDom_of

end TypeVarInEnvironment

end TabularTypeInterpreter.«F⊗⊕ω»
