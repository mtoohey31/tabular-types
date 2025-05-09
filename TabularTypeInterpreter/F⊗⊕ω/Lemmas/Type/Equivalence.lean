import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.ParallelReduction

namespace TabularTypeInterpreter.«F⊗⊕ω»

theorem EqParallelReduction.TypeEquivalence_of (eAB: [[ Δ ⊢ A <≡>* B]]) : [[ Δ ⊢ A ≡ B]] := sorry

namespace TypeEquivalence

theorem EqParallelReduction_of (eq: [[Δ ⊢ A ≡ B]]) : [[Δ ⊢ A <≡>* B]] := sorry

def symm : [[Δ ⊢ A ≡ B]] → [[Δ ⊢ B ≡ A]]
  | refl => refl
  | lamAppL => lamAppR
  | lamAppR => lamAppL
  | listAppL => listAppR
  | listAppR => listAppL
  | listAppIdL => listAppIdR
  | listAppIdR => listAppIdL
  | listAppCompL => listAppCompR
  | listAppCompR => listAppCompL
  | lam I h => lam I fun a mem => (h a mem).symm
  | app h₁ h₂ => app h₁.symm h₂.symm
  | scheme I h => scheme I fun a mem => (h a mem).symm
  | arr h₁ h₂ => arr h₁.symm h₂.symm
  | list h => list fun i mem => (h i mem).symm
  | listApp h₁ h₂ => listApp h₁.symm h₂.symm
  | prod h => prod h.symm
  | sum h => sum h.symm

def trans : [[Δ ⊢ A₀ ≡ A₁]] → [[Δ ⊢ A₁ ≡ A₂]] → [[Δ ⊢ A₀ ≡ A₂]] := sorry

theorem weakening (equiv: [[ Δ, Δ'' ⊢ A ≡ B ]]) (wfτ: [[ ⊢τ Δ, Δ', Δ'' ]]) : [[ Δ, Δ', Δ'' ⊢ A ≡ B ]] :=
  equiv.EqParallelReduction_of |>.weakening wfτ |>.TypeEquivalence_of

theorem subst' {A T T' : «Type»} (equiv : [[ Δ, a: K, Δ' ⊢ T ≡ T' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡ T'[A/a] ]] :=
  equiv.EqParallelReduction_of |>.subst_out' wf kindA |>.TypeEquivalence_of

-- TODO this is not dt so properties on typing apparently have nothing to do with terms in env
theorem TermVar_drop (equiv: [[ Δ, x: T, Δ'' ⊢ A ≡ B ]]): [[ Δ, Δ'' ⊢ A ≡ B ]] := sorry

local instance : Inhabited «Type» where
  default := .list []

theorem listAppEmptyL : [[Δ ⊢ A ⟦{ }⟧ ≡ { }]] := by
  let B (i : Nat) := [[{ }]]
  rw [← Std.Range.map_get!_eq (as := []), List.length_nil]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B i
    nomatch mem
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B@i]]
    nomatch mem
  )]
  exact listAppL

theorem listAppEmptyR : [[Δ ⊢ { } ≡ A ⟦{ }⟧]] := by
  let B (i : Nat) := [[{ }]]
  rw [← Std.Range.map_get!_eq (as := []), List.length_nil]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B@i]]
    nomatch mem
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B i
    nomatch mem
  )]
  exact listAppR

theorem listAppSingletonL : [[Δ ⊢ A ⟦{B}⟧ ≡ {A B}]] := by
  let B' (i : Nat) := B
  rw [← Std.Range.map_get!_eq (as := [_]), ← Std.Range.map_get!_eq (as := [ [[A B]]])]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B' i
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B'@i]]
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  exact listAppL

theorem listAppSingletonR : [[Δ ⊢ {A B} ≡ A ⟦{B}⟧]] := by
  let B' (i : Nat) := B
  rw [← Std.Range.map_get!_eq (as := [_]), ← Std.Range.map_get!_eq (as := [B])]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B'@i]]
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B' i
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  exact listAppR

theorem listSingleton (AequB : [[Δ ⊢ A ≡ B]]) : [[Δ ⊢ {A} ≡ {B}]] := by
  let A' (i : Nat) := A
  let B' (i : Nat) := B
  rw [← Std.Range.map_get!_eq (as := [_]), List.length_singleton,
      Std.Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = A' i
      cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
      dsimp [A']
      rw [List.get!_cons_zero]
  ), ← Std.Range.map_get!_eq (as := [_]), List.length_singleton]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = B' i
      cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
      dsimp [B']
      rw [List.get!_cons_zero]
  )]
  apply list
  intro i mem
  cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
  dsimp [A', B']
  exact AequB

end TypeEquivalence
namespace TypeInequivalence

private
def symm : [[Δ ⊢ A ≢ B]] → [[Δ ⊢ B ≢ A]] := (· ·.symm)

private
theorem arr_forall : [[Δ ⊢ A → B ≢ ∀ a : K. A']] := fun equ => by
  generalize A₁eq : [[(A → B)]] = A₁, A₂eq : [[∀ a : K. A']] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem arr_prod : [[Δ ⊢ A → B ≢ ⊗ A']] := fun equ => by
  generalize A₁eq : [[(A → B)]] = A₁, A₂eq : [[⊗ A']] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem arr_sum : [[Δ ⊢ A → B ≢ ⊕ A']] := fun equ => by
  generalize A₁eq : [[(A → B)]] = A₁, A₂eq : [[⊕ A']] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem forall_prod : [[Δ ⊢ ∀ a : K. A ≢ ⊗ B]] := fun equ => by
  generalize A₁eq : [[∀ a : K. A]] = A₁, A₂eq : [[⊗ B]] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem forall_sum : [[Δ ⊢ ∀ a : K. A ≢ ⊕ B]] := fun equ => by
  generalize A₁eq : [[∀ a : K. A]] = A₁, A₂eq : [[⊕ B]] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem prod_sum : [[Δ ⊢ ⊗ A ≢ ⊕ B]] := fun equ => by
  generalize A₁eq : [[⊗ A]] = A₁, A₂eq : [[⊕ B]] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

end TypeInequivalence

end TabularTypeInterpreter.«F⊗⊕ω»
