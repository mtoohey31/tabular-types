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

theorem mem_zip_map_append {f g : Nat → α} {h : Nat → β} (h₀ : l ≤ m) (h₁ : m ≤ n)
  (mem : x ∈ ([l:m].map f ++ [m:n].map g).zip ([l:n].map h))
  : (∃ i ∈ [l:m], x = (f i, h i)) ∨ ∃ i ∈ [m:n], x = (g i, h i) := by
  rw [map, map, map, toList] at mem
  split at mem
  · case isTrue h =>
    rw [List.map_cons, toList.eq_def [l:n], if_pos <| Nat.lt_of_lt_of_le h h₁, List.map_cons,
        List.cons_append, List.zip_cons_cons] at mem
    cases mem with
    | head => exact .inl ⟨l, ⟨Nat.le.refl, h, Nat.mod_one _⟩, rfl⟩
    | tail _ mem' => match mem_zip_map_append h h₁ mem' with
      | .inl ⟨i, imem, eq⟩ => exact .inl ⟨i, ⟨Nat.le_trans Nat.le.refl.step imem.lower, imem.upper, Nat.mod_one _⟩, eq⟩
      | .inr ⟨i, imem, eq⟩ => exact .inr ⟨i, imem, eq⟩
  · case isFalse h =>
    rw [List.map_nil, List.nil_append] at mem
    cases Nat.eq_iff_le_and_ge.mpr ⟨h₀, Nat.ge_of_not_lt h⟩
    exact .inr <| mem_zip_map mem
termination_by m - l
decreasing_by
  all_goals simp_arith
  apply Nat.sub_succ_lt_self
  assumption

theorem mem_zip_map_append_cons {f g : Nat → α}
  (mem : xy ∈ (([k:l].map f) ++ x :: [m:n].map g).zip (([k:l].map f) ++ y :: [m:n].map g))
  : (∃ j ∈ [k:l], xy.fst = f j ∧ xy.snd = f j) ∨ (xy.fst = x ∧ xy.snd = y) ∨
    (∃ j ∈ [m:n], xy.fst = g j ∧ xy.snd = g j) := by
  rw [map, toList] at mem
  split at mem
  · case isTrue h =>
    rw [List.map_cons, List.cons_append, List.cons_append, List.zip_cons_cons] at mem
    cases mem with
    | head => exact .inl ⟨k, ⟨Nat.le.refl, h, Nat.mod_one _⟩, rfl, rfl⟩
    | tail _ mem' =>
      rw [← map] at mem'
      simp only at mem'
      match mem_zip_map_append_cons mem' with
      | .inl ⟨j, mem, eq⟩ =>
        exact .inl ⟨j, ⟨Nat.le_of_succ_le mem.lower, mem.upper, Nat.mod_one _⟩, eq⟩
      | .inr (.inl eq) => exact .inr <| .inl eq
      | .inr (.inr h') => exact .inr <| .inr h'
  · case isFalse h =>
    rw [List.map_nil, List.nil_append, List.nil_append, List.zip_cons_cons] at mem
    cases mem with
    | head => simp
    | tail _ mem' =>
      let ⟨j, mem, eq⟩ := mem_zip_map mem'
      exact .inr <| .inr ⟨j, mem, Prod.mk.inj eq⟩
termination_by l - k
decreasing_by
  all_goals simp_arith
  apply Nat.sub_succ_lt_self
  assumption

end Std.Range
