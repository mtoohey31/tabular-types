import Lott.Data.Range

namespace Std.Range

def get!InverseOn (p p' : List Nat) (n : Nat) :=
  (∀ i ∈ [:n], p'.get! (p.get! i) = i) ∧ ∀ i ∈ [:n], p.get! (p'.get! i) = i

def mem_toList_of_mem {m n i: Nat} (mem: i ∈ [m:n]): i ∈ [m:n].toList := by
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

theorem map_f_get!_eq [Inhabited α] [Inhabited β] {as : List α} {f : α → β} : [:as.length].map (fun i => f <| as.get! i) = as.map f := by
  match as with
  | [] =>
    rw [List.length_nil, map, toList, if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map_nil, List.map_nil]
  | a :: as' =>
    rw [List.length_cons, map, toList, if_pos (Nat.succ_pos _), List.map_cons, List.get!_cons_zero,
        ←map, ← map_shift (Nat.le_add_left ..), Nat.add_sub_cancel, Nat.add_sub_cancel,
        map_eq_of_eq_of_mem'' fun _ _ => congrArg f <| List.get!_cons_succ .., map_f_get!_eq, List.map_cons]

end Std.Range
