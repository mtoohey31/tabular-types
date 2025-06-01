import Mathlib.Data.List.Basic
import TabularTypeInterpreter.Data.Range

namespace List

def combinations {α : Type} (l : List α) :  List (List α)  :=
  l.foldl (fun acc a => acc ++ acc.map (fun l => a :: l)) [nil]

def append_eq_append {α : Type} {l₀ l₁ l₀' l₁' : List α} (eql: l₀ = l₁) (eqr: l₀' = l₁') :
  l₀ ++ l₀' = l₁ ++ l₁' := List.append_eq_append_iff.mpr (.inl ⟨[], by simp_all, eqr⟩)

end List
