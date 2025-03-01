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
  rec (motive_1 := motive) var lam app typeLam typeApp prodIntro prodElim sumIntro sumElim nofun
    (fun _ _ ih₀ ih₁ _ mem => match mem with | .head _ => ih₀ | .tail _ mem' => ih₁ _ mem') E

@[simp]
theorem TypeVar_open_sizeOf : sizeOf (TypeVar_open E x n) = sizeOf E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, safe List.sizeOf_map_eq_of_eq_id_of_mem)

@[simp]
theorem TermVar_open_sizeOf : sizeOf (TermVar_open E x n) = sizeOf E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TermVar_open, safe List.sizeOf_map_eq_of_eq_id_of_mem)

namespace TypeVarLocallyClosed

theorem TypeVar_open_id : TypeVarLocallyClosed E n → E.TypeVar_open a n = E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, 40% cases TypeVarLocallyClosed,
      safe [Type.TypeVarLocallyClosed.TypeVar_open_id, List.map_eq_id_of_eq_id_of_mem])

theorem Type_open_id : TypeVarLocallyClosed E n → E.Type_open F n = E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp Type_open, 40% cases TypeVarLocallyClosed,
      safe [Type.TypeVarLocallyClosed.Type_open_id, List.map_eq_id_of_eq_id_of_mem])

theorem TermVar_open_drop
  : (TermVar_open E x m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TermVar_open, safe cases TypeVarLocallyClosed,
      safe constructors TypeVarLocallyClosed)

theorem TypeVar_open_drop
  : m < n → (TypeVar_open E a m).TypeVarLocallyClosed n → E.TypeVarLocallyClosed n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed,
      safe constructors TypeVarLocallyClosed, 20% Type.TypeVarLocallyClosed.TypeVar_open_drop)

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

theorem TermVar_open_id
  : TermVarLocallyClosed E n → E.TermVar_open a n = E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TermVar_open, 40% cases TermVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)

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

theorem TypeVar_open_TermVar_open_comm
  : (TermVar_open E x n).TypeVar_open a m = (E.TypeVar_open a m).TermVar_open x n := by
  induction E using rec_uniform generalizing m n <;> aesop (add simp [TermVar_open, TypeVar_open])

end Term

namespace Typing

local instance : Inhabited Term where
  default := .prodIntro []
in
local instance : Inhabited «Type» where
  default := .list []
in
theorem prodIntro' (wf: [[ ⊢ Δ ]]) (EstyAs : ∀ EA ∈ List.zip Es As, let (E, A) := EA; [[Δ ⊢ E : A]])
  (length_eq : Es.length = As.length) : Typing Δ (.prodIntro Es) (.prod (.list As)) := by
  rw [← Std.Range.map_get!_eq (as := Es), ← Std.Range.map_get!_eq (as := As), ← length_eq]
  apply Typing.prodIntro wf
  intro i mem
  have := EstyAs ((List.zip Es As).get! i) <| List.get!_mem <| by
    rw [List.length_zip, ← length_eq, Nat.min_self]
    exact mem.upper
  rw [List.get!_zip length_eq mem.upper] at this
  exact this

local instance : Inhabited Term where
  default := .prodIntro []
in
local instance : Inhabited «Type» where
  default := .list []
in
theorem sumElim' (EtyA : Typing Δ E (.sum (.list As)))
  (FstyAsarrB : ∀ FA ∈ List.zip Fs As, let (F, A) := FA; [[Δ ⊢ F : A → B]])
  (Bki : [[Δ ⊢ B : *]])
  (length_eq : Fs.length = As.length) : Typing Δ (.sumElim E Fs) B := by
  rw [← Std.Range.map_get!_eq (as := Fs)]
  apply Typing.sumElim (A := As.get!)
  · rw [length_eq, Std.Range.map_get!_eq]
    exact EtyA
  · intro i mem
    have := FstyAsarrB ((List.zip Fs As).get! i) <| List.get!_mem <| by
      rw [List.length_zip, ← length_eq, Nat.min_self]
      exact mem.upper
    rw [List.get!_zip length_eq mem.upper] at this
    exact this
  . exact Bki

theorem prod_id (Δwf : [[⊢ Δ]]) (Aki : [[Δ ⊢ A : L K]])
  : [[Δ ⊢ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0 : ∀ a : K ↦ *. (⊗ (a$0 ⟦A⟧)) → ⊗ (a$0 ⟦A⟧)]] :=
  .typeLam (I := Δ.typeVarDom) fun a anin => by
    simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
    exact .lam (I := Δ.termVarDom) fun x xnin => by
      simp only [Term.TermVar_open]
      apply Typing.var (Δwf.typeVarExt anin |>.termVarExt xnin _) .head
      apply Kinding.prod
      apply Kinding.listApp (.var .head)
      rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact Aki.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem sum_id (Δwf : [[⊢ Δ]]) (Aki : [[Δ ⊢ A : L K]])
  : [[Δ ⊢ Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0 : ∀ a : K ↦ *. (⊕ (a$0 ⟦A⟧)) → ⊕ (a$0 ⟦A⟧)]] :=
  .typeLam (I := Δ.typeVarDom) fun a anin => by
    simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
    exact .lam (I := Δ.termVarDom) fun x xnin => by
      simp only [Term.TermVar_open]
      apply Typing.var (Δwf.typeVarExt anin |>.termVarExt xnin _) .head
      apply Kinding.sum
      apply Kinding.listApp (.var .head)
      rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact Aki.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem id (Δwf : [[⊢ Δ]]) (Aki : [[Δ ⊢ A : *]]) : [[Δ ⊢ λ x : A. x$0 : A → A]] := by
  apply Typing.lam Δ.termVarDom
  intro x xnin
  rw [Term.TermVar_open, if_pos rfl]
  exact Typing.var (Δwf.termVarExt xnin Aki) .head

theorem WellFormedness_of (EtyA : [[Δ ⊢ E : A]]) : [[ ⊢ Δ ]] := by
  induction EtyA <;> try simp_all
  . case lam Δ T E A I EtyA ih =>
    have ⟨x, notIn⟩ := I.exists_fresh
    specialize ih x notIn
    cases ih; assumption
  . case typeLam Δ K E A I EtyA ih =>
    have ⟨a, notIn⟩ := I.exists_fresh
    specialize ih a notIn
    cases ih; assumption

-- TODO naming
theorem Δext_TypeVarLocallyClosed_of' (EtyA : [[Δ, x: T, Δ' ⊢ E : A]]) : T.TypeVarLocallyClosed := by
  have wf := EtyA.WellFormedness_of; clear EtyA
  have fresh := wf.append_termVar_fresh_r x (by simp [Environment.termVarDom])
  induction Δ'
  . case empty =>
    cases wf; case termVarExt wf notIn Tki => exact Tki.TypeVarLocallyClosed_of
  . case typeExt Δ' x' K ih => exact ih (by cases wf; assumption) fresh
  . case termExt Δ' x' T' ih =>
    exact ih (by cases wf; assumption) (by intro contra; exact fresh (by simp_all [Environment.termVarDom]))

theorem Δext_TypeVarLocallyClosed_of (EtyA : [[Δ, x: T ⊢ E : A]]) : T.TypeVarLocallyClosed :=
  EtyA.Δext_TypeVarLocallyClosed_of' (Δ' := .empty)

theorem TypeVarLocallyClosed_of (EtyA : [[Δ ⊢ E : A]]) : A.TypeVarLocallyClosed 0 := by
  induction EtyA
  . case var Δ x A wf In =>
    induction In <;> (try cases wf; simp_all)
    match wf with | .termVarExt _ _ k => exact k.TypeVarLocallyClosed_of
  . case lam Δ T E A I EtyA ih =>
    let ⟨x, xnin⟩ := I.exists_fresh
    constructor
    specialize EtyA x xnin
    . exact EtyA.Δext_TypeVarLocallyClosed_of
    . exact ih x xnin
  . case app _ _ _ _ _ _ _ ih1 ih2 => cases ih1; assumption
  . case typeLam Δ K E A I EtyA ih =>
    let ⟨a, anin⟩ := (I ++ A.freeTypeVars).exists_fresh
    constructor
    specialize ih a (by simp_all)
    have := ih.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at this
    exact this
  . case typeApp Δ E K A B EtyA BkiK ih => cases ih; case «forall» Alc =>
    exact Alc.Type_open_dec BkiK.TypeVarLocallyClosed_of
  . case prodIntro n Δ E A EtyA ih =>
    constructor
    constructor
    intro A_ In
    simp [List.map_singleton_flatten] at In
    have ⟨i, In, A_eq⟩ := In
    subst A_eq
    exact ih i (by simp_all [Std.Range.mem_of_mem_toList])
  . case prodElim Δ E n As i EtyAs In ih =>
    simp [List.map_singleton_flatten] at ih
    cases ih; case prod ih => cases ih; case list ih =>
    exact ih (As i) (Std.Range.mem_map_of_mem In)
  . case sumIntro i n Δ E As In EtyA Aki ih =>
    constructor
    constructor
    intro A AInAs
    simp [List.map_singleton_flatten] at AInAs
    obtain ⟨j, AInAs, A_eq⟩ := AInAs
    subst A_eq
    exact Aki j (by simp_all [Std.Range.mem_of_mem_toList]) |>.TypeVarLocallyClosed_of
  . case sumElim Δ E n As Fs B EtyA FtyAB Bki ih1 ih2 =>
    exact Bki.TypeVarLocallyClosed_of
  . case equiv Δ E A B EtyA eqAB ih => sorry -- TODO by equiv -> equiv closure of pred -> equiv pred preserves lc


theorem TermVarLocallyClosed_of (EtyA : [[Δ ⊢ E : A]]) : E.TermVarLocallyClosed := by
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
  | prodIntro _ _ ih =>
    exact .prodIntro fun E mem => by
      let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
      cases eq
      exact ih i mem'
  | prodElim _ _ ih => exact .prodElim ih
  | sumIntro _ _ _ ih => exact .sumIntro ih
  | sumElim _ _ _ ih₀ ih₁ =>
    exact .sumElim ih₀ fun i mem => by
      let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
      cases eq
      exact ih₁ i mem'
  | equiv Ety' _ ih => exact ih

theorem weakening : [[Δ, Δ'' ⊢ E : A]] → [[⊢ Δ, Δ', Δ'']] → [[Δ, Δ', Δ'' ⊢ E : A]] := sorry

end Typing

end TabularTypeInterpreter.«F⊗⊕ω»
