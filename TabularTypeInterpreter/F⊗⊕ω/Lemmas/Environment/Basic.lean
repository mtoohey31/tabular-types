import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment

namespace TabularTypeInterpreter.«F⊗⊕ω».Environment

theorem append_empty (Δ : Environment) : Δ.append empty = Δ := rfl

theorem empty_append (Δ : Environment) : append empty Δ = Δ := by
  match Δ with
  | empty => rfl
  | typeExt Δ' .. | termExt Δ' .. => rw [append, Δ'.empty_append]

end TabularTypeInterpreter.«F⊗⊕ω».Environment
