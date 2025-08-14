import Lott.Data.List
import Mathlib.Data.Rel

-- Like Thesis.finitely_branching but we know exactly how many reducts there are.
def EnumerablyBranching {α} (r : α → α → Prop) := ∀ a, ∃ (s : List α), ∀ b, b ∈ s ↔ r a b

inductive AccIn {α : Sort u} (r : α → α → Prop) : Nat → α → Prop where
  | intro (x : α) (h : ∀ y m, r y x → m < n → AccIn r m y) : AccIn r n x

theorem AccIn.weakening : AccIn r m x → n ≤ m → AccIn r n x := by
  intro h le
  induction h generalizing n with
  | intro _ _ ih =>
    constructor
    intro _ _ r lt
    exact ih _ _ r (Nat.lt_of_lt_of_le lt le) Nat.le.refl

theorem Acc.to_In_of_EnumerablyBranching
  : Acc r x → EnumerablyBranching (Rel.inv r) → ∃ n, AccIn r n x := by
  intro h eb
  induction h with
  | intro x _ ih =>
    let ⟨m, ih'⟩ := Classical.skolem.mp (Classical.skolem.mp <| ih ·)
    let ⟨s, h⟩ := eb x
    let m' := s.mapMem (m · <| h _ |>.mp ·) |>.min?.getD 0
    refine ⟨m', .intro _ ?_⟩
    intro y m'' r lt
    apply ih' y r .. |>.weakening
    dsimp [m'] at lt
    exact Nat.le_of_lt <| Nat.lt_of_lt_of_le lt <| List.min?_getD_le_of_mem <|
      List.mem_mapMem.mpr ⟨_, h _ |>.mpr r, h _ |>.mpr r, rfl⟩

theorem AccIn.to_Acc : AccIn r n x → Acc r x := by
  intro h
  induction h with
  | intro _ _ ih =>
    constructor
    intro _ r
    apply ih _ _ r sorry
