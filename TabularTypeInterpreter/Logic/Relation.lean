import Mathlib.Logic.Relation

namespace Relation

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
