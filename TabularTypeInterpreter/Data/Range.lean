import Lott.Data.Range

namespace Std.Range

theorem length_eq_of_mem_eq {f g : Nat → α}
  (h : List.map (fun i => f i) [m:n] = List.map (fun i => g i) [m':n']) : n - m = n' - m' := by
  have := congrArg List.length h
  rw [List.length_map, length_toList, List.length_map, length_toList] at this
  exact this

def get!InverseOn (p p' : List Nat) (n : Nat) :=
  (∀ i ∈ [:n], p'.get! (p.get! i) = i) ∧ ∀ i ∈ [:n], p.get! (p'.get! i) = i

def mem_toList_of_mem {m n i: Nat} (mem: i ∈ [m:n]): i ∈ [m:n].toList := by
  have H := @mem_map_of_mem (f:=id)
  simp_all

theorem map_f_get!_eq [Inhabited α] [Inhabited β] {as : List α} {f : α → β} : [:as.length].map (fun i => f <| as.get! i) = as.map f := by
  match as with
  | [] =>
    rw [List.length_nil, map, toList, if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map_nil, List.map_nil]
  | a :: as' =>
    rw [List.length_cons, map, toList, if_pos (Nat.succ_pos _), List.map_cons, List.get!_cons_zero,
        ←map, ← map_shift (Nat.le_add_left ..), Nat.add_sub_cancel, Nat.add_sub_cancel,
        map_eq_of_eq_of_mem'' fun _ _ => congrArg f <| List.get!_cons_succ .., map_f_get!_eq, List.map_cons]

theorem map_append' {f g : Nat → α} (h₁ : l ≤ m) (h₂ : m ≤ n)
  : List.map f [l:m] ++ List.map g [m:n] = List.map (λi => (if i < m then f else g) i) [l:n] := by
  have eqfmap : List.map f [l:m] = List.map (λi => (if i < m then f else g) i) [l:m] := by
    refine List.map_eq_map_iff.mpr (λ i iin => ?_)
    split
    . case isTrue => rfl
    . case isFalse contra =>
      have := mem_of_mem_toList iin
      simp [Membership.mem] at this
      simp_all
  have eqgmap : List.map g [m:n] = List.map (λi => (if i < m then f else g) i) [m:n] := by
    refine List.map_eq_map_iff.mpr (λ i iin => ?_)
    split
    . case isTrue contra =>
      have := mem_of_mem_toList iin
      simp [Membership.mem] at this
      have := Nat.not_le_of_lt contra
      simp_all
    . case isFalse => rfl
  rw [eqfmap, eqgmap, ← List.map_append, toList_append h₁ h₂]

end Std.Range
