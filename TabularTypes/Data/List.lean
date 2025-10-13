import Mathlib.Data.List.Basic
import TabularTypes.Data.Nat
import TabularTypes.Data.Range

namespace List

def combinations {α : Type} (l : List α) :  List (List α)  :=
  l.foldl (fun acc a => acc ++ acc.map (fun l => a :: l)) [nil]

def append_eq_append {α : Type} {l₀ l₁ l₀' l₁' : List α} (eql: l₀ = l₁) (eqr: l₀' = l₁') :
  l₀ ++ l₀' = l₁ ++ l₁' := append_eq_append_iff.mpr (.inl ⟨[], by simp_all, eqr⟩)

def of_length_eq_of_append_eq_append {l₀ l₁ l₀' l₁' : List α} (length_eq : l₀.length = l₁.length)
  (eq : l₀ ++ l₀' = l₁ ++ l₁') : l₀ = l₁ ∧ l₀' = l₁' := by
  match l₀ with
  | [] =>
    rw [length_nil] at length_eq
    cases length_eq_zero.mp length_eq.symm
    rw [nil_append, nil_append] at eq
    exact ⟨rfl, eq⟩
  | _ :: _ =>
    rw [length_cons] at length_eq
    rcases exists_of_length_succ _ length_eq.symm with ⟨_, _, rfl⟩
    rcases cons.inj eq with ⟨rfl, eq'⟩
    rcases of_length_eq_of_append_eq_append (Nat.add_one_inj.mp length_eq) eq' with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

def of_length_lt_of_append_eq_append {l₀ l₁ l₀' l₁' : List α} (length_lt : l₀.length < l₁.length)
  (eq : l₀ ++ l₀' = l₁ ++ l₁') : ∃ h l₂, l₁ = l₀ ++ h :: l₂ ∧ l₀' = h :: l₂ ++ l₁' := by
  match append_eq_append_iff.mp eq with
  | .inl h =>
    rcases h with ⟨l₂, eq₀, eq₁⟩
    match l₂ with
    | [] =>
      rw [append_nil] at eq₀
      rw [eq₀] at length_lt
      nomatch Nat.lt_irrefl _ length_lt
    | _ :: _ => exact ⟨_, _, eq₀, eq₁⟩
  | .inr h =>
    rcases h with ⟨_, eq₀, eq₁⟩
    let length_eq := congrArg length eq₀
    rw [length_append] at length_eq
    nomatch Nat.not_le_of_lt length_lt <| Nat.le_of_add_right_le <| Nat.le_of_eq length_eq.symm

inductive Unique : List α → Prop where
  | nil : Unique nil
  | cons : x ∉ xs → Unique xs → Unique (cons x xs)

def max?_eq_of_subset {l₀ l₁ : List Nat} (sub₀₁ : l₀ ⊆ l₁) (sub₁₀ : l₁ ⊆ l₀)
  : max? l₀ = max? l₁ := by
  by_cases max? l₀ = none
  · case pos h =>
    rw [max?_eq_none_iff.mp h] at sub₁₀
    rw [h, subset_nil.mp sub₁₀, max?]
  · case neg h =>
    replace ⟨_, h⟩ := Or.resolve_left (Option.eq_none_or_eq_some _) h
    rw [h]
    let ⟨mem, le⟩ := max?_eq_some_iff Nat.le_refl Nat.max_eq_or Nat.max_le_iff |>.mp h
    symm
    apply max?_eq_some_iff Nat.le_refl Nat.max_eq_or Nat.max_le_iff |>.mpr
    exact ⟨sub₀₁ mem, fun _ mem => le _ <| sub₁₀ mem⟩

end List
