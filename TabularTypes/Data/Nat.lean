namespace Nat

theorem max_eq_or (a b : Nat) : max a b = a ∨ max a b = b := by
  rw [Max.max, instMax, maxOfLe]
  simp
  by_cases a ≤ b
  · case pos le =>
    right
    intro lt
    nomatch Nat.not_le_of_lt lt le
  · case neg lt =>
    left
    intro le
    nomatch lt le

theorem max_le_iff (a b c : Nat) : max b c ≤ a ↔ b ≤ a ∧ c ≤ a where
  mp maxle := by
    rw [Max.max, instMax, maxOfLe] at maxle
    simp at maxle
    split at maxle
    · case isTrue blec => exact ⟨trans blec maxle, maxle⟩
    · case isFalse cltb =>
      exact ⟨maxle, Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_not_le cltb) maxle)⟩
  mpr
    | ⟨blea, clea⟩ => by
      rw [Max.max, instMax, maxOfLe]
      simp
      split
      · case isTrue _ => exact clea
      · case isFalse _ => exact blea

end Nat
