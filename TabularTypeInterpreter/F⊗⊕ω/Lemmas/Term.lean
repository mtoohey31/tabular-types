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

theorem TypeVar_open_TermVar_open_comm
  : (TermVar_open E x n).TypeVar_open a m = (E.TypeVar_open a m).TermVar_open x n := by
  induction E using rec_uniform generalizing m n <;> aesop (add simp [TermVar_open, TypeVar_open])

theorem TypeVar_open_TermVar_subst_comm {E: Term} : (E.TermVar_open y n).TypeVar_subst x A = (E.TypeVar_subst x A).TermVar_open y n := by
  induction E using rec_uniform generalizing n <;> simp_all [TermVar_open, TypeVar_subst]

theorem TermVar_subst_intro_of_not_mem_freeTermVars {A: Term}: a ∉ A.freeTermVars → (A.TermVar_open a n).TermVar_subst a B = A.Term_open B n := by
  induction A using rec_uniform generalizing B n <;>
    aesop (add simp [TermVar_subst, TermVar_open, Term_open, freeTermVars, TermVar_open])

theorem TypeVar_subst_intro_of_not_mem_freeTypeVars {A: Term}: a ∉ A.freeTypeVars → (A.TypeVar_open a n).TypeVar_subst a B = A.Type_open B n := by
  induction A using rec_uniform generalizing B n <;>
    simp_all [TypeVar_subst, TypeVar_open, Type_open, freeTypeVars, TypeVar_open, Type.TypeVar_subst_intro_of_not_mem_freeTypeVars]

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

theorem TermVar_open_TypeVar_subst_comm {E: Term} (lc: F.TypeVarLocallyClosed n) : (E.TypeVar_open y n).TermVar_subst x F = (E.TermVar_subst x F).TypeVar_open y n := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, TermVar_subst], 40% forward TypeVar_open_id, 40% weaken)

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

theorem Term_open_id : TermVarLocallyClosed A n → A.Term_open B n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [Term_open], safe cases TermVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)

private
theorem Term_open_id' : TermVarLocallyClosed A n → A = A.Term_open B n := (Term_open_id · |>.symm)

theorem TermVar_open_TermVar_subst_comm {E F : Term} (lc : F.TermVarLocallyClosed n) (neq : x ≠ y) : (E.TermVar_open y n).TermVar_subst x F = (E.TermVar_subst x F).TermVar_open y n := by
  set_option aesop.dev.statefulForward false in
  induction E using rec_uniform generalizing n <;> aesop
    (add simp [TermVar_open, TermVar_subst], 40% Term_open_id', 40% forward TermVar_open_id, 40% weaken)

end TermVarLocallyClosed

end Term

namespace Type.TypeVarLocallyClosed

private
theorem Type_open_id' : Term.TypeVarLocallyClosed A n → A = A.Type_open B n := (Term.TypeVarLocallyClosed.Type_open_id · |>.symm)

theorem Term_TypeVar_open_TypeVar_subst_comm {E : Term} (lc : F.TypeVarLocallyClosed n) (neq : x ≠ y) : (E.TypeVar_open y n).TypeVar_subst x F = (E.TypeVar_subst x F).TypeVar_open y n := by
  set_option aesop.dev.statefulForward false in
  induction E using Term.rec_uniform generalizing n <;> aesop
    (add simp [Term.TypeVar_open, Term.TypeVar_subst], 40% Type_open_id', 40% forward Term.TypeVarLocallyClosed.TypeVar_open_id, 40% Term.TypeVarLocallyClosed.weaken, 40% Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm, 40% Type.TypeVarLocallyClosed.weaken)

end Type.TypeVarLocallyClosed

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

theorem Type_TypeVarLocallyClosed_of (EtyA : [[Δ ⊢ E : A]]) : A.TypeVarLocallyClosed 0 := by
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
  . case equiv Δ E A B EtyA eqAB ih =>
    exact eqAB.preserve_lc.1 ih

theorem TypeVarLocallyClosed_of (EtyA : [[Δ ⊢ E : A]]) : E.TypeVarLocallyClosed := by
  induction EtyA with
  | var _ _ => exact .var
  | lam I ihTy ihLc =>
    let ⟨x, xnin⟩ := I.exists_fresh
    exact .lam
      (ihTy x xnin |>.Δext_TypeVarLocallyClosed_of)
      (ihLc x xnin |>.TermVar_open_drop)
  | app _ _ ih₀ ih₁ => exact .app ih₀ ih₁
  | typeLam I _ ih =>
    let ⟨x, xnin⟩ := I.exists_fresh
    exact .typeLam <| ih x xnin |>.weaken.TypeVar_open_drop Nat.one_pos
  | typeApp _ BkiK ih =>
    refine .typeApp ih BkiK.TypeVarLocallyClosed_of
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

open Environment in
theorem inv_arr' (Ety: [[Δ ⊢ λ x? : T. E : C ]]) (eqC: [[ Δ ⊢ C ≡ A → B ]]): [[ Δ ⊢ T ≡ A ]] ∧ (∃(I: List _), ∀x ∉ I, [[ Δ, x: T ⊢ E^x : B ]]) := by
  generalize T_eq : [[ λ x? : T. E ]] = T_ at Ety
  induction Ety <;> cases T_eq
  . case lam.refl Δ B' I EtyB' _ =>
    have := eqC.EqParallelReduction_of
    have ⟨wf, AkiStar, TB'lc⟩ := (
      have ⟨x, xnin⟩ := I.exists_fresh
      have EtyB' := EtyB' x xnin
      have ⟨wf, AkiStar⟩ := match EtyB'.WellFormedness_of with | .termVarExt wf _ AkiStar => And.intro wf AkiStar
      have B'lc := EtyB'.Type_TypeVarLocallyClosed_of
      have Tlc := EtyB'.Δext_TypeVarLocallyClosed_of
      have TB'lc := Tlc.arr B'lc
      And.intro wf (And.intro AkiStar TB'lc)
    )
    have ⟨eTA, eB'B⟩ := this TB'lc wf |>.inv_arr wf TB'lc
    refine ⟨eTA.TypeEquivalence_of wf, ?_⟩
    refine ⟨I ++ Δ.termVarDom, λ x xnin => ?_⟩
    refine .equiv (EtyB' x (by simp_all)) ?_
    refine eB'B.weakening (Δ'' := [[ ε ]]) (Δ' := [[ ε, x: T ]]) (.termVarExt wf.EnvironmentTypeWellFormedness_of)
      |>.TypeEquivalence_of ?_
    refine wf.termVarExt (by simp_all [TermVarNotInDom, TermVarInDom]) AkiStar
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqC) rfl

theorem inv_arr (Ety: [[Δ ⊢ λ x? : T. E : A → B ]]) : [[ Δ ⊢ T ≡ A ]] ∧ (∃(I: List _), ∀x ∉ I, [[ Δ, x: T ⊢ E^x : B ]]) := Ety.inv_arr' .refl

open Environment in
theorem inv_forall' (Ety: [[Δ ⊢ Λ a? : K. E : T ]]) (eqT: [[ Δ ⊢ T ≡ ∀ a?: K'. A ]]): K = K' ∧ (∃(I: List _), ∀a ∉ I, [[ Δ, a: K ⊢ E^a : A^a ]]) := by
  generalize T_eq : [[ Λ a? : K. E ]] = T_ at Ety
  induction Ety <;> cases T_eq
  . case typeLam.refl Δ A' I EtyA' _ =>
    have := eqT.EqParallelReduction_of
    -- have ⟨a, nin⟩ := (I ++ A'.freeTypeVars).exists_fresh
    -- have EtyA' := EtyA' a (by simp_all)
    -- have wf := match EtyA'.WellFormedness_of with | .typeVarExt wf _ => wf
    -- have A'lc := EtyA'.Type_TypeVarLocallyClosed_of |>.TypeVar_close_inc (a := a)
    -- simp at A'lc
    -- rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at A'lc
    have ⟨wf, A'lc⟩ := (
      have ⟨a, nin⟩ := (I ++ A'.freeTypeVars).exists_fresh
      have EtyA' := EtyA' a (by simp_all)
      have wf := match EtyA'.WellFormedness_of with | .typeVarExt wf _ => wf
      have A'lc := EtyA'.Type_TypeVarLocallyClosed_of |>.TypeVar_close_inc (a := a)
      have A'lc: A'.TypeVarLocallyClosed 1 := (by
        rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at A'lc
        exact A'lc
      )
      And.intro wf A'lc
    )
    have ⟨eqKK', I', eA'A⟩ := this A'lc.forall wf |>.inv_forall wf A'lc.forall
    refine ⟨eqKK', ?_⟩
    refine ⟨I ++ I' ++ Δ.typeVarDom, λ a anin => ?_⟩
    refine .equiv (EtyA' a (by simp_all)) ?_
    refine eA'A a (by simp_all) |>.TypeEquivalence_of (wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom]))
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqT) rfl

theorem inv_forall (Ety: [[Δ ⊢ Λ a? : K. E : ∀ a?: K'. A ]]) : K = K' ∧ (∃(I: List _), ∀a ∉ I, [[ Δ, a: K ⊢ E^a : A^a ]]) := Ety.inv_forall' .refl

theorem inv_prod' (Ety: [[ Δ ⊢ (</ E@i // i in [:n] />) : T ]]) (eqT: [[ Δ ⊢ T ≡ ⊗ {</ A@i // i in [:n'] />} ]]) (Alc: [[⊗ {</ A@i // i in [:n'] />}]].TypeVarLocallyClosed): n = n' ∧ [[ </ Δ ⊢ E@i : A@i // i in [:n] /> ]] := by
  generalize T_eq : [[ (</ E@i // i in [:n] />) ]] = T_ at Ety
  induction Ety <;> try cases T_eq
  . case prodIntro Δ n_ E_ A_ wf EtyA ih =>
    clear ih
    injection T_eq with eq
    have eqnn_ := Std.Range.length_eq_of_mem_eq eq; simp at eqnn_; subst n_
    have eqEE_ := Std.Range.eq_of_mem_of_map_eq eq; clear eq
    have Alc' := match Alc with | .prod Alc => Alc
    have ⟨eqn'n, eAA_⟩ := eqT.EqParallelReduction_of (by
      simp_all [Std.Range.mem_of_mem_map]
      refine .prod (.list λ T Tin => ?_)
      have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
      exact EtyA i iltn |>.Type_TypeVarLocallyClosed_of
    ) wf |>.sym.inv_prod wf Alc |>.inv_list wf Alc'
    subst n'
    refine ⟨rfl, λ x xin => ?_⟩
    simp_all
    exact .equiv (EtyA x xin) <| eAA_ x xin |>.sym.TypeEquivalence_of wf
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqT) rfl

theorem inv_prod (Ety: [[ Δ ⊢ (</ E@i // i in [:n] />) : ⊗ {</ A@i // i in [:n'] />} ]]) : n = n' ∧ [[ </ Δ ⊢ E@i : A@i // i in [:n] /> ]] := Ety.inv_prod' .refl Ety.Type_TypeVarLocallyClosed_of

-- NOTE I believe this stronger version holds but idk how to prove it. For details, check the notes.
-- theorem inv_sum' (Ety: [[ Δ ⊢ ι n E : T ]]) (eqT: [[ Δ ⊢ T ≡ ⊕ {</ A@i // i in [:n'] />} ]]) (Alc: [[ ⊕ {</ A@i // i in [:n'] />} ]].TypeVarLocallyClosed) : n ∈ [0:n'] ∧ [[ Δ ⊢ E : A@n ]] ∧ [[ </ Δ ⊢ A@i : * // i in [:n'] /> ]] := by
--   generalize T_eq : [[ ι n E ]] = T_ at Ety
--   induction Ety <;> cases T_eq
--   . case sumIntro.refl n_ Δ A' A'kiStar nin EtyA' ih =>
--     clear ih
--     have wf := EtyA'.WellFormedness_of
--     have Alc' := match Alc with | .sum Alc => Alc
--     have ⟨eqn'n_, eAA'⟩ := eqT.EqParallelReduction_of.sym.inv_sum wf Alc |>.inv_list wf Alc'
--     subst n_
--     refine ⟨nin, ?_, ?_⟩
--     . exact .equiv EtyA' (eAA' n nin |>.sym.TypeEquivalence_of)
--     . refine λ i iin => ?_
--       have A'kiStar := A'kiStar i iin
--       have eAA' := eAA' i iin
--       -- NOTE this requires preservation of type equivalence (aka type parallelreduction), and idk how to prove this
--       sorry

-- theorem inv_sum (Ety: [[ Δ ⊢ ι n E : ⊕ {</ A@i // i in [:n'] />} ]]) : n ∈ [0:n'] ∧ [[ Δ ⊢ E : A@n ]] ∧ [[ </ Δ ⊢ A@i : * // i in [:n'] /> ]] := Ety.inv_sum' .refl Ety.Type_TypeVarLocallyClosed_of

theorem inv_sum' (Ety: [[ Δ ⊢ ι n E : T ]]) (eqT: [[ Δ ⊢ T ≡ ⊕ {</ A@i // i in [:n'] />} ]]) (Alc: [[ ⊕ {</ A@i // i in [:n'] />} ]].TypeVarLocallyClosed) : n ∈ [0:n'] ∧ [[ Δ ⊢ E : A@n ]] := by
  generalize T_eq : [[ ι n E ]] = T_ at Ety
  induction Ety <;> cases T_eq
  . case sumIntro.refl n_ Δ A' A'kiStar nin EtyA' ih =>
    clear ih
    have wf := EtyA'.WellFormedness_of
    have Alc' := match Alc with | .sum Alc => Alc
    have ⟨eqn'n_, eAA'⟩ := eqT.EqParallelReduction_of (by
      simp_all [Std.Range.mem_of_mem_map]
      refine .sum (.list λ T Tin => ?_)
      have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
      exact A'kiStar i iltn |>.TypeVarLocallyClosed_of
    ) wf |>.sym.inv_sum wf Alc |>.inv_list wf Alc'
    subst n_
    exact ⟨nin, .equiv EtyA' <| eAA' n nin |>.sym.TypeEquivalence_of wf⟩
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqT) rfl

theorem inv_sum (Ety: [[ Δ ⊢ ι n E : ⊕ {</ A@i // i in [:n'] />} ]]) : n ∈ [0:n'] ∧ [[ Δ ⊢ E : A@n ]] := Ety.inv_sum' .refl Ety.Type_TypeVarLocallyClosed_of

end Typing

end TabularTypeInterpreter.«F⊗⊕ω»
