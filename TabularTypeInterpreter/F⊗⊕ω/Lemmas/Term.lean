import Aesop
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace Term

@[elab_as_elim]
def rec_uniform {motive : Term → Prop} (var : ∀ x : TermVar, motive (var x))
  (lam : ∀ A E, motive E → motive (lam A E)) (app : ∀ E F, motive E → motive F → motive (app E F))
  (typeLam : ∀ A E, motive E → motive (typeLam A E))
  (typeApp : ∀ E A, motive E → motive (typeApp E A))
  (prodIntro : ∀ Es, (∀ E ∈ Es, motive E) → motive (prodIntro Es))
  (prodElim : ∀ n E, motive E → motive (prodElim n E))
  (sumIntro : ∀ n E, motive E → motive (sumIntro n E))
  (sumElim : ∀ E Fs, motive E → (∀ F ∈ Fs, motive F) → motive (sumElim E Fs)) (E : Term)
  : motive E :=
  rec (motive_1 := motive) var lam app typeLam typeApp prodIntro prodElim sumIntro sumElim
    (fun _ => (nomatch ·))
    (fun _ _ ih₀ ih₁ _ mem => match mem with | .head _ => ih₀ | .tail _ mem' => ih₁ _ mem') E

@[simp]
theorem TypeVar_open_sizeOf : sizeOf (TypeVar_open E x n) = sizeOf E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, safe apply List.sizeOf_map_eq_of_eq_id_of_mem)

@[simp]
theorem TermVar_open_sizeOf : sizeOf (TermVar_open E x n) = sizeOf E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TermVar_open, safe apply List.sizeOf_map_eq_of_eq_id_of_mem)

namespace TypeVarLocallyClosed

theorem TypeVar_open_eq : TypeVarLocallyClosed E n → E.TypeVar_open a n = E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, 40% cases TypeVarLocallyClosed,
      safe apply [Type.TypeVarLocallyClosed.TypeVar_open_eq, List.map_eq_id_of_eq_id_of_mem])

theorem TermVar_open_drop
  : (TermVar_open E x m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TermVar_open, safe cases TypeVarLocallyClosed,
      safe constructors TypeVarLocallyClosed)

theorem TypeVar_open_drop
  : m < n → (TypeVar_open E a m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed,
      safe constructors TypeVarLocallyClosed, 20% apply Type.TypeVarLocallyClosed.TypeVar_open_drop)

theorem weaken (Elc : TypeVarLocallyClosed E m) : E.TypeVarLocallyClosed (m + n) := by
  induction Elc <;> aesop (simp_config := { arith := true })
    (add safe constructors TypeVarLocallyClosed, 20% [Type.TypeVarLocallyClosed.weaken, of_eq])
where
  of_eq {E m n} (Elc : TypeVarLocallyClosed E m) (eq : m = n) : E.TypeVarLocallyClosed n := by
    rwa [eq] at Elc

theorem prod_id (Alc : A.TypeVarLocallyClosed)
  : [[Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0]].TypeVarLocallyClosed :=
  typeLam <| lam (.prod (.listApp (.var_bound Nat.one_pos) Alc.weaken)) var

theorem sum_id (Alc : A.TypeVarLocallyClosed)
  : [[Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0]].TypeVarLocallyClosed :=
  typeLam <| lam (.sum (.listApp (.var_bound Nat.one_pos) Alc.weaken)) var

end TypeVarLocallyClosed

namespace TermVarLocallyClosed

theorem TermVar_open_eq
  : TermVarLocallyClosed E n → E.TermVar_open a n = E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TermVar_open, 40% cases TermVarLocallyClosed,
      safe apply List.map_eq_id_of_eq_id_of_mem)

theorem TypeVar_open_drop
  : (TypeVar_open E x m).TermVarLocallyClosed n → E.TermVarLocallyClosed n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TermVarLocallyClosed,
      safe constructors TermVarLocallyClosed)

theorem TermVar_open_drop
  : m < n → (TermVar_open E x m).TermVarLocallyClosed n → E.TermVarLocallyClosed n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TermVar_open, safe cases TermVarLocallyClosed,
      safe constructors TermVarLocallyClosed)

theorem weaken (Elc : TermVarLocallyClosed E m) : E.TermVarLocallyClosed (m + n) := by
  induction Elc <;> aesop (simp_config := { arith := true })
    (add safe constructors TermVarLocallyClosed, 20% [of_eq, Nat.lt_add_right])
where
  of_eq {E m n} (Elc : TermVarLocallyClosed E m) (eq : m = n) : E.TermVarLocallyClosed n := by
    rwa [eq] at Elc

end TermVarLocallyClosed

end Term

namespace Typing

theorem prod_id (Δwf : [[⊢ Δ]]) (Aki : [[Δ ⊢ A : L K]])
  : [[Δ ⊢ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0 : ∀ a : K ↦ *. (⊗ (a$0 ⟦A⟧)) → ⊗ (a$0 ⟦A⟧)]] :=
  .typeLam (I := Δ.typeVarDom) fun a anin => by
    simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
    exact .lam (I := Δ.termVarDom) fun x xnin => by
      simp only [Term.TermVar_open]
      apply Typing.var (Δwf.typeVarExt anin |>.termVarExt xnin _) .head
      apply Kinding.prod
      apply Kinding.listApp (.var .head)
      rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← (Δ.typeExt ..).empty_append]
      apply Aki.weakening _ (Δ' := .empty) (Δ'' := .typeExt .empty ..)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin

theorem sum_id (Δwf : [[⊢ Δ]]) (Aki : [[Δ ⊢ A : L K]])
  : [[Δ ⊢ Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0 : ∀ a : K ↦ *. (⊕ (a$0 ⟦A⟧)) → ⊕ (a$0 ⟦A⟧)]] :=
  .typeLam (I := Δ.typeVarDom) fun a anin => by
    simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
    exact .lam (I := Δ.termVarDom) fun x xnin => by
      simp only [Term.TermVar_open]
      apply Typing.var (Δwf.typeVarExt anin |>.termVarExt xnin _) .head
      apply Kinding.sum
      apply Kinding.listApp (.var .head)
      rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← (Δ.typeExt ..).empty_append]
      apply Aki.weakening _ (Δ' := .empty) (Δ'' := .typeExt .empty ..)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin

theorem TermVarLocallyClosed_of (EtyA : [[Δ ⊢ E : A]]) : E.TermVarLocallyClosed 0 := by
  induction EtyA with
  | var _ _ => exact .var_free
  | lam I _ ih =>
    let ⟨x, xnin⟩ := I.exists_fresh
    exact .lam <| ih x xnin |>.weaken.TermVar_open_drop Nat.one_pos
  | app _ _ ih₀ ih₁ => exact .app ih₀ ih₁
  | typeLam I _ ih =>
    let ⟨x, xnin⟩ := I.exists_fresh
    exact .typeLam <| ih x xnin |>.TypeVar_open_drop
  | typeApp _ _ ih => exact .typeApp ih
  | prodIntro _ ih =>
    exact .prodIntro fun E mem => by
      rw [List.map_singleton_flatten] at mem
      let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
      cases eq
      exact ih i mem'
  | prodElim _ _ ih => exact .prodElim ih
  | sumIntro _ _ ih => exact .sumIntro ih
  | sumElim _ _ ih₀ ih₁ =>
    exact .sumElim ih₀ fun i mem => by
      rw [List.map_singleton_flatten] at mem
      let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
      cases eq
      exact ih₁ i mem'
  | equiv Ety' _ ih => exact ih

theorem weakening : [[Δ ⊢ E : A]] → [[⊢ Δ', Δ, Δ'']] → [[Δ', Δ, Δ'' ⊢ E : A]] := sorry

end Typing

end TabularTypeInterpreter.«F⊗⊕ω»
