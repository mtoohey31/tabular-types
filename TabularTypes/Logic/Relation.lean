import Mathlib.Logic.Relation

namespace Relation

inductive IndexedReflTransGen (r : α → α → Prop) : Nat → α → α → Prop where
  | refl : IndexedReflTransGen r 0 a a
  | tail {b c} : IndexedReflTransGen r n a b → r b c → IndexedReflTransGen r (n + 1) a c

attribute [refl] IndexedReflTransGen.refl

namespace IndexedReflTransGen

@[trans]
theorem trans (hab : IndexedReflTransGen r m a b) (hbc : IndexedReflTransGen r n b c)
  : IndexedReflTransGen r (m + n) a c := by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac hab |>.tail hcd

instance
  : Trans (IndexedReflTransGen r m) (IndexedReflTransGen r n) (IndexedReflTransGen r (m + n)) where
  trans := trans

theorem single (hab : r a b) : IndexedReflTransGen r 1 a b := refl.tail hab

theorem head (hab : r a b) (hbc : IndexedReflTransGen r n b c)
  : IndexedReflTransGen r (n + 1) a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac hab |>.tail hcd

@[elab_as_elim]
theorem head_induction_on {P : ∀ n : Nat, ∀ a : α, IndexedReflTransGen r n a b → Prop} {a : α}
  (h : IndexedReflTransGen r n a b) (refl : P 0 b refl)
  (head : ∀ {n a c} (h' : r a c) (h : IndexedReflTransGen r n c b), P n c h → P (n + 1) a (h.head h'))
  : P n a h := by
  induction h with
  | refl => exact refl
  | @tail n b c _ _ hbc ih =>
    apply ih
    · exact head hbc _ refl
    · exact fun h1 h2 ↦ head h1 (h2.tail hbc)

theorem cases_head (h : IndexedReflTransGen r n a b)
  : (n = 0 ∧ a = b) ∨ ∃ m c, n = m + 1 ∧ r a c ∧ IndexedReflTransGen r m c b := by
  induction h using Relation.IndexedReflTransGen.head_induction_on
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨_, _, rfl, by assumption, by assumption⟩

theorem map {r : α → α → Prop} {f : _ → _} (map_rel : ∀ {a b}, r a b → r (f a) (f b))
  (h : IndexedReflTransGen r n a b) : IndexedReflTransGen r n (f a) (f b) := by
  induction h with
  | refl => rfl
  | tail _ b'c' ih =>
    exact ih.trans <| .single <| map_rel b'c'

theorem map₂ {r : α → α → Prop} {f : _ → _ → _} (map_rel₀ : ∀ {a b c}, r a c → r (f a b) (f c b))
  (map_rel₁ : ∀ {a b d}, r b d → r (f a b) (f a d)) (ac : IndexedReflTransGen r m a c)
  (bd : IndexedReflTransGen r n b d) : IndexedReflTransGen r (m + n) (f a b) (f c d) := by
  calc
    IndexedReflTransGen r m (f a b) (f c b) := map map_rel₀ ac
    IndexedReflTransGen r n (f c b) (f c d) := map map_rel₁ bd

end IndexedReflTransGen

namespace ReflTransGen

theorem map {r : α → α → Prop} {f : _ → _} (map_rel : ∀ {a b}, r a b → r (f a) (f b))
  (h : ReflTransGen r a b) : ReflTransGen r (f a) (f b) := by
  induction h with
  | refl => rfl
  | tail _ b'c' ih => exact ih.trans <| .single <| map_rel b'c'

theorem map₂ {r : α → α → Prop} {f : _ → _ → _} (map_rel₀ : ∀ {a b c}, r a c → r (f a b) (f c b))
  (map_rel₁ : ∀ {a b d}, r b d → r (f a b) (f a d)) (ac : ReflTransGen r a c)
  (bd : ReflTransGen r b d) : ReflTransGen r (f a b) (f c d) := by
  calc
    ReflTransGen r (f a b) (f c b) := map map_rel₀ ac
    ReflTransGen r (f c b) (f c d) := map map_rel₁ bd

theorem to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h with
  | refl => exact .refl _
  | tail _ bc ab => exact ab.trans _ _ _ <| .rel _ _ bc

end ReflTransGen

namespace EqvGen

attribute [refl] EqvGen.refl

instance : Trans (EqvGen r) (EqvGen r) (EqvGen r) where
  trans := trans _ _ _

theorem map {r : α → α → Prop} {f : _ → _} (map_rel : ∀ {a b}, r a b → r (f a) (f b))
  (h : EqvGen r a b) : EqvGen r (f a) (f b) := by
  induction h with
  | rel _ _ xy => exact rel _ _ <| map_rel xy
  | refl => rfl
  | symm _ _ _ ih => exact symm _ _ ih
  | trans _ _ _ _ _ ih₀ ih₁ => exact trans _ _ _ ih₀ ih₁

theorem map₂ {r : α → α → Prop} {f : _ → _ → _} (map_rel₀ : ∀ {a b c}, r a c → r (f a b) (f c b))
  (map_rel₁ : ∀ {a b d}, r b d → r (f a b) (f a d)) (ac : EqvGen r a c)
  (bd : EqvGen r b d) : EqvGen r (f a b) (f c d) := by
  calc
    EqvGen r (f a b) (f c b) := map map_rel₀ ac
    EqvGen r (f c b) (f c d) := map map_rel₁ bd

end EqvGen

end Relation
