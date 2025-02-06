import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Value
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

open Std

private
theorem _root_.Membership.mem.inc {r : Range} (h : i ∈ r) : i ∈ { r with stop := r.stop + 1 } :=
  ⟨h.lower, Nat.lt_add_right _ h.upper⟩

private
theorem progress.sandwich {f : Nat → α} (h : i < n) : (List.map (fun j => [f j]) [0:n]).flatten =
  (List.map (fun j => [f j]) [0:i]).flatten ++
    f i :: (List.map (fun j => [f (j + (i + 1))]) [(i + 1) - (i + 1):n - (i + 1)]).flatten := by
  simp only [List.map_singleton_flatten]
  congr
  rw [← List.singleton_append, Range.map_shift (Nat.le_refl _)]
  have : [f i] = List.map (fun j => f j) [i:i + 1] := by
    rw [Range.toList, if_neg Nat.one_ne_zero, if_pos (Nat.lt_succ_self _), Range.toList,
        if_neg Nat.one_ne_zero, if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map, List.map]
  rw [this]
  rw [Range.map_append (Nat.le_succ _) (Nat.succ_le_of_lt h),
      Range.map_append (Nat.zero_le _) (Nat.le_of_lt h)]

private
theorem progress.fold {E : Nat → Term} (EtyA : ∀ i ∈ [0:n], [[ε ⊢ E@i : A@i]])
  (h : ∀ i ∈ [0:n], (∃ E', [[E@i -> E']]) ∨ (E i).IsValue) :
  (∃ i ∈ [0:n], (∀ j ∈ [0:i], (E j).IsValue) ∧ ∃ E', [[E@i -> E']]) ∨
    (∀ i ∈ [0:n], (E i).IsValue) := by
  induction n
  · case zero =>
    right
    intro _ ⟨_, lt_zero⟩
    contradiction
  · case succ j ih' => match ih' (fun j mem => EtyA j mem.inc) (fun j mem => h j mem.inc) with
    | .inl ⟨i, mem, ⟨E'', toE''⟩⟩ => exact .inl ⟨i, mem.inc, ⟨E'', toE''⟩⟩
    | .inr IsValue =>
      have jmem : j ∈ [0:j + 1] := ⟨Nat.zero_le _, Nat.lt_succ_self _⟩
      match h j jmem with
      | .inl ⟨E'', toE''⟩ => exact .inl ⟨j, jmem, ⟨IsValue, ⟨E'', toE''⟩⟩⟩
      | .inr jIsValue =>
        right
        intro i mem
        by_cases i = j
        · case pos h =>
          rw [h]
          exact jIsValue
        · case neg h =>
          exact IsValue i ⟨Nat.zero_le _, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ mem.upper) h⟩

local instance : Inhabited Value where
  default := ⟨.prodIntro [], .prodIntro fun _ => (nomatch ·)⟩
in
theorem progress (EtyA : [[ε ⊢ E : A]]) : (∃ E', [[E -> E']]) ∨ E.IsValue := by
  generalize Δeq : Environment.empty = Δ at EtyA
  induction EtyA <;> cases Δeq
  · case var xinε => cases xinε
  · case lam => exact .inr .lam
  · case app E' A' B F E'tyA'arrB _ ih₁ ih₂ => match ih₁ rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .appL E'toE''
    | .inr E'IsValue => match ih₂ rfl with
      | .inl ⟨F', FtoF'⟩ => exact .inl <| .intro _ <| .appR (V := ⟨E', E'IsValue⟩) FtoF'
      | .inr FIsValue =>
        let VE' : Value := ⟨E', E'IsValue⟩
        have : E' = VE'.1 := rfl
        have ⟨_, _, VE'eq⟩ := VE'.eq_lam_of_ty_arr E'tyA'arrB
        rw [this, VE'eq]
        exact .inl <| .intro _ <| .lamApp (V := ⟨F, FIsValue⟩)
  · case typeLam => exact .inr .typeLam
  · case typeApp E' K _ _ E'ty _ ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .typeApp E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, _, Veq⟩ := V.eq_typeApp_of_ty_forall E'ty
      rw [this, Veq]
      exact .inl <| .intro _ <| .typeLamApp
  · case prodIntro n E' A E'ty ih => match progress.fold E'ty (fun i mem => ih i mem rfl) with
    | .inl ⟨i, ⟨_, iltn⟩, IsValue, E'', toE''⟩ =>
      let V j : Value := if h' : j < i then ⟨E' j, IsValue j ⟨Nat.zero_le _, h'⟩⟩ else default
      rw [progress.sandwich iltn, Range.map_eq_of_eq_of_mem (fun j jmem => by
          show [E' j] = [(V j).val]
          dsimp only [V]
          rw [dif_pos jmem.upper]
      ), Nat.sub_self]
      exact .inl <| .intro _ <| .prodIntro toE''
    | .inr IsValue =>
      exact .inr <| .prodIntro fun E Emem => by
        rw [List.map_singleton_flatten] at Emem
        have ⟨i, imem, Eeq⟩ := Range.mem_of_mem_map Emem
        rw [Eeq]
        exact IsValue i imem
  · case prodElim E' n _ i mem E'ty ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .prodElim E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, Veq⟩ := V.eq_prodIntro_of_ty_prod E'ty
      rw [this, Veq]
      exact .inl <| .intro _ <| .prodElimIntro mem
  · case sumIntro ih => match ih rfl with
    | .inl ⟨E', toE'⟩ => exact .inl <| .intro _ <| .sumIntro toE'
    | .inr E'IsValue => exact .inr <| .sumIntro E'IsValue
  · case sumElim E' n As F _ E'ty Fty ih₁ ih₂ => match ih₁ rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .sumElimL E'toE''
    | .inr E'IsValue =>
      let VE' : Value := ⟨E', E'IsValue⟩
      have ⟨n', mem, VE'', VE'_eq⟩ := VE'.eq_sumIntro_of_ty_sum E'ty
      cases VE'_eq
      match progress.fold Fty (fun i mem => ih₂ i mem rfl) with
      | .inl ⟨j, ⟨_, jltn⟩, IsValue, F', toF'⟩ =>
        let VF k : Value := if h' : k < j then ⟨F k, IsValue k ⟨Nat.zero_le _, h'⟩⟩ else default
        rw [progress.sandwich jltn, Range.map_eq_of_eq_of_mem (fun j jmem => by
          show [F j] = [(VF j).val]
          dsimp only [VF]
          rw [dif_pos jmem.upper]
        ), Nat.sub_self]
        exact .inl <| .intro _ <| .sumElimR (V := VE') toF'
      | .inr FIsValue =>
        let VF j : Value := if h : j < n then ⟨F j, FIsValue j ⟨Nat.zero_le _, h⟩⟩ else default
        rw [List.map_singleton_flatten, Range.map_eq_of_eq_of_mem (fun i mem => by
          show F i = (VF i).val
          dsimp only [VF]
          rw [dif_pos mem.upper]
        ), ← List.map_singleton_flatten]
        exact .inl <| .intro _ <| .sumElimIntro mem
  · case equiv ih => exact ih rfl

theorem preservation : [[ε ⊢ E : A]] → [[E -> E']] → [[ε ⊢ E' : A]] := sorry

end TabularTypeInterpreter.«F⊗⊕ω»
