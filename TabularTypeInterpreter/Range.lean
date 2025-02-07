import Lott.Data.Range

namespace Std.Range

private
theorem mem_of_mem_toList {m n i: Nat} (mem: i ∈ [m:n].toList): i ∈ [m:n] := by
  have H := @mem_of_mem_map (f:=id)
  simp_all

private
theorem mem_toList_of_mem {m n i: Nat} (mem: i ∈ [m:n]): i ∈ [m:n].toList := by
  have H := @mem_map_of_mem (f:=id)
  simp_all

theorem mem_toList_le {m} n {h: m <= n} : ∀i ∈ [m:n].toList, i < n := by
  intros i In
  induction n
  . case zero => simp_all [Std.Range.toList]
  . case succ n ih =>
    rw [<- Std.Range.toList_append (m := n) (by
      cases h
      . case refl =>
        simp [Std.Range.toList] at In
      . case step => simp_all
    ) (by
      cases h
      . case refl =>
        simp [Std.Range.toList] at In
      . case step => simp_all
    )] at In
    simp_all
    cases In
    .case inl In =>
      cases h
      . case refl =>
        exfalso
        unfold Std.Range.toList at In
        simp at In
        cases In; case intro h _ =>
        exact Nat.lt_irrefl _ (Nat.lt_of_add_right_lt h)
      . case step =>
        simp_all [Nat.lt_add_right]
    . case inr h =>
      simp [Std.Range.toList] at h
      simp_all

end Std.Range
