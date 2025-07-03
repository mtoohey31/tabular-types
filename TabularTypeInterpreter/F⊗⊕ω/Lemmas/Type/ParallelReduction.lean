import Mathlib.Tactic
import TabularTypeInterpreter.Data.Range
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Kinding

namespace TabularTypeInterpreter.«F⊗⊕ω»

open Std

local instance : Inhabited «Type» where
  default := .list []

namespace ParallelReduction

def refl : [[Δ ⊢ A ≡> A]] :=
  match A with
  | .var _ => .var
  | .lam _ _ => .lam (I := []) fun _ _ => .refl
  | .app .. => .app .refl .refl
  | .forall .. => .scheme (I := []) fun _ _ => .refl
  | .arr .. => .arr .refl .refl
  | .list As => by
    rw [← Std.Range.map_get!_eq (as := As)]
    exact .list fun _ mem => .refl
  | .listApp .. => .listApp .refl .refl
  | .prod _ => .prod .refl
  | .sum _ => .sum .refl
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  simp [List.getElem?_eq_getElem mem.upper]

def list' (As Bs: List «Type») (length_eq: As.length = Bs.length) (red: ∀A B, ⟨A, B⟩ ∈ (As.zip Bs) → [[ Δ ⊢ A ≡> B ]]): ParallelReduction Δ (Type.list As) (Type.list Bs) := by
  rw [← Std.Range.map_get!_eq (as := As), ← Std.Range.map_get!_eq (as := Bs), ← length_eq]
  apply list
  intro i mem
  apply red
  have := (As.zip Bs).get!_mem <| by
    rw [List.length_zip, ← length_eq, Nat.min_self]
    exact mem.upper
  rw [List.get!_zip length_eq mem.upper] at this
  exact this

local instance : Inhabited «Type» where
  default := .list []
in
def listAppList' (A A' : «Type») (Bs B's : List «Type») (length_eq: Bs.length = B's.length)
  (redA: [[ Δ ⊢ A ≡> A' ]])
  (redB: ∀B B', ⟨B, B'⟩ ∈ (Bs.zip B's) → [[ Δ ⊢ B ≡> B' ]])
  (Alc: A.TypeVarLocallyClosed)
  : ParallelReduction Δ (A.listApp (Type.list Bs)) (Type.list <| B's.map fun B' => A'.app B') := by
    rw [← Std.Range.map_get!_eq (as := Bs), ← Std.Range.map_f_get!_eq (as := B's) (f := fun B' => A'.app B'), <- length_eq]
    refine listAppList redA ?_ Alc
    . intro i mem
      apply redB
      have := (Bs.zip B's).get!_mem <| by
        rw [List.length_zip, ← length_eq, Nat.min_self]
        exact mem.upper
      rw [List.get!_zip length_eq mem.upper] at this
      exact this

theorem inv_arr (red: [[ Δ ⊢ (A → B) ≡> T ]]): ∃ A' B', T = [[(A' → B')]] ∧ [[ Δ ⊢ A ≡> A' ]] ∧ [[ Δ ⊢ B ≡> B' ]] := by
  cases red <;> aesop  (rule_sets := [pred])

theorem inv_lam (red: [[ Δ ⊢ (λ a? : K. A) ≡> T ]]): ∃ A', T = [[λ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a ≡> A'^a ]] := by
  cases red <;> aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem inv_forall (red: [[ Δ ⊢ (∀ a? : K. A) ≡> T ]]): ∃ A', T = [[∀ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a ≡> A'^a ]] := by
  cases red <;> aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem inv_prod (red: [[ Δ ⊢ ⊗A ≡> T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ≡> A' ]] := by
  cases red <;> aesop (rule_sets := [pred])

theorem inv_sum (red: [[ Δ ⊢ ⊕A ≡> T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ≡> A' ]] := by
  cases red <;> aesop (rule_sets := [pred])

theorem inv_list (red: [[ Δ ⊢ { </ A@i // i in [:n] /> } ≡> T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ Δ ⊢ A@i ≡> B@i // i in [:n] /> ]] := by
  generalize T_eq : [[{ </ A@i // i in [:n] /> }]] = T_ at red
  cases red <;> try cases T_eq
  case list n' A_ B AB =>
  injection T_eq with eq
  have eqnn' := Std.Range.length_eq_of_mem_eq eq
  subst eqnn'
  have eqAA_ := Std.Range.eq_of_mem_of_map_eq eq; clear eq
  exact ⟨B, rfl, λx nin => by simp_all⟩

open «Type» in
theorem inv_id (red: [[Δ ⊢ λa: K. a$0 ≡> A']]): A' = [[ λa: K. a$0 ]] := by
  cases red
  case lam I B2 aa =>
  have ⟨a, nin⟩ := (I ++ B2.freeTypeVars).exists_fresh
  simp [TypeVar_open] at aa
  specialize aa a (by simp_all)
  generalize B2eq: [[ (B2^a) ]] = B2_ at aa
  cases aa; case var =>
  have B2eq := congrArg (λt => TypeVar_close t a) B2eq
  simp [TypeVar_open, TypeVar_close] at B2eq
  rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at B2eq
  subst B2eq
  rfl

open «Type» in
theorem preserve_not_mem_freeTypeVars (red: [[ Δ ⊢ A ≡> B ]]) a (notInFV: a ∉ A.freeTypeVars): a ∉ B.freeTypeVars := by
  induction red generalizing a <;> simp_all [«Type».freeTypeVars]
  . case lamApp Δ B K I A A' B' kinding redA redB ihA' ihB' =>
    obtain ⟨notInAfv, notInBfv⟩ := notInFV
    apply not_mem_freeTypeVars_Type_open_intro
    . have ⟨a', notInI⟩ := (I ++ A'.freeTypeVars).exists_fresh
      by_cases a = a'
      . case pos eq => simp_all
      . case neg neq =>
        specialize ihA' a' (by simp_all) a (not_mem_freeTypeVars_TypeVar_open_intro notInAfv (by simp_all))
        exact not_mem_freeTypeVars_TypeVar_open_drop ihA'
    . simp_all
  . case listAppList =>
    intro i inRange
    simp_all [Std.Range.mem_of_mem_toList]
  . case lam I Δ K A B red ih =>
    have ⟨a', notInI⟩ := (a :: I).exists_fresh
    have ih' := @ih a' (by simp_all) a (by apply not_mem_freeTypeVars_TypeVar_open_intro <;> aesop)
    exact not_mem_freeTypeVars_TypeVar_open_drop ih'
  . case scheme I Δ K A B red ih =>
    have ⟨a', notInI⟩ := (a :: I).exists_fresh
    have ih' := ih a' (by aesop) a (by apply not_mem_freeTypeVars_TypeVar_open_intro <;> aesop)
    exact not_mem_freeTypeVars_TypeVar_open_drop ih'
  . case list n Δ A B red ih =>
    intro as i inRange
    simp_all [Std.Range.mem_of_mem_toList]

open «Type» TypeVarLocallyClosed in
theorem preserve_lc (red: [[ Δ ⊢ A ≡> B ]]): A.TypeVarLocallyClosed → B.TypeVarLocallyClosed := by
  induction red
  case lamApp Δ B K I A A' B' kindB redA redB ihA ihB =>
    intro lcAB
    cases lcAB; case app lcA lcB =>
    cases lcA; case lam lcA =>
    have lcA' := lcA.modus_ponens_open ihA
    apply Type_open_dec <;> simp_all
  case listAppList ihA ihB =>
    intro lcAB
    simp_all
    cases lcAB; case listApp lcA lcB =>
    cases lcB; case list lcB =>
    constructor
    simp_all
    intro i In
    exact ihA.app (by simp_all [Std.Range.mem_of_mem_toList])
  case listAppComp lcA₀ _ _ _ ihA₀ ihA₁ ihB =>
    sorry
    -- intro lc
    -- match lc with
    -- | .listApp _ (.listApp (.lam bodyA₁) lcB) =>
    --   simp_all
    --   have bodyA₁' := bodyA₁.modus_ponens_open ihA₁
    --   exact ihA₀.weaken.app bodyA₁' |>.lam |>.listApp ihB
  all_goals
    set_option aesop.dev.statefulForward false in
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

open «Type» TypeVarLocallyClosed in
theorem preserve_lc_rev (red: [[ Δ ⊢ A ≡> B ]]): B.TypeVarLocallyClosed → A.TypeVarLocallyClosed := by
  induction red
  case lamApp Δ B K I A A' B' kindB redA redB ihA ihB =>
    intro lcA'B'
    have ⟨a, notIn⟩ := (I ++ A.freeTypeVars ++ A'.freeTypeVars).exists_fresh
    rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)] at lcA'B'
    have Blc := kindB.TypeVarLocallyClosed_of
    have Abody := ihA a (by simp_all) lcA'B'.TypeVar_subst_drop
    apply TypeVar_close_inc (a := a) at Abody
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Abody
    exact Abody.lam.app Blc
  case listAppList Δ A A' n B B' redA redB Alc ihA ihB =>
    intro lcA'B'
    simp_all
    cases lcA'B'; case list lcA'B' =>
    refine Alc.listApp ?_
    cases n
    . case zero => constructor; simp [Std.Range.map, Std.Range.toList]
    . case succ n =>
      constructor
      simp_all [Std.Range.mem_map_of_mem, Std.Range.mem_of_mem_toList]
      intro i iltSn
      match lcA'B' i iltSn with
      | .app lcA' lcB' =>
        exact ihB i (Std.Range.mem_of_mem_toList iltSn) lcB'
  case listAppComp lcA₀ _ _ _ ihA₀ ihA₁ ihB =>
    sorry
    -- intro lcA₀'A₁'B'
    -- match lcA₀'A₁'B' with
    -- | .listApp (.lam (.app _ bodyA₁')) lcB' =>
    --   simp_all
    --   have bodyA₁ := bodyA₁'.modus_ponens_open ihA₁
    --   exact lcA₀.listApp (bodyA₁.lam.listApp ihB)
  all_goals
    set_option aesop.dev.statefulForward false in
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

theorem weakening_type' (red: [[ Δ, Δ' ⊢ A ≡> B ]]) (freshΔ: a ∉ Δ.typeVarDom) : [[ Δ, a: K, Δ' ⊢ A ≡> B ]] := by
  generalize Δ_eq : Δ.append Δ' = Δ_ at red
  induction red generalizing Δ Δ' <;> try (aesop (add norm Type.freeTypeVars) (add safe constructors ParallelReduction); done)
  . case lamApp Δ_ B K' I A A' B' kindB redA redB ihA ihB =>
    subst Δ_
    apply ParallelReduction.lamApp (I := a :: I ++ A.freeTypeVars)
    . rw [<- Environment.append_type_assoc]; exact Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) kindB
    . intro a' notIn
      specialize @ihA a' (by simp_all) Δ (Δ'.typeExt a' K')
      simp_all [Environment.append]
    . specialize @ihB Δ Δ'; simp_all
  . case listAppId Δ_ A K' A' AkiLK AA' ih =>
    subst Δ_
    refine .listAppId ?_ (by simp_all)
    . rw [<- Environment.append_type_assoc]; exact Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) AkiLK
  . case lam I Δ_ K' A B red ih =>
    subst Δ_
    apply ParallelReduction.lam (I := a :: I ++ A.freeTypeVars)
    intro a' notIn
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K')
    simp_all [Environment.append]
  . case scheme I Δ_ K' A B red ih =>
    subst Δ_
    apply ParallelReduction.scheme (I := a :: I ++ A.freeTypeVars)
    intro a' notIn
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K')
    simp_all [Environment.append]
  . sorry
    -- case listAppComp A₀ Δ_ A₀' I K' A₁ A₁' B B' lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    -- subst Δ_
    -- apply ParallelReduction.listAppComp (I := a :: I ++ A₀.freeTypeVars) <;> try simp_all; done
    -- . intro a' nin
    --   specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]]
    --   simp_all [Environment.append]


theorem weakening_type (red: [[ Δ ⊢ A ≡> B ]]) (freshΔ: a ∉ Δ.typeVarDom) : [[ Δ, a: K ⊢ A ≡> B ]] := by
  apply weakening_type' (Δ' := Environment.empty) <;> assumption

theorem weakening_term' (red: [[ Δ, Δ' ⊢ A ≡> B ]]) : [[ Δ, x: T, Δ' ⊢ A ≡> B ]] := by
  generalize Δ_eq : Δ.append Δ' = Δ_ at red
  induction red generalizing Δ Δ' <;> try (aesop (rule_sets := [pred]); done)
  . case lamApp Δ_ B K' I A A' B' kindB redA redB ihA ihB =>
    subst Δ_
    apply ParallelReduction.lamApp (I := x :: I)
    . rw [<- Environment.append_term_assoc]; apply Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) kindB
    . intro x' notIn
      specialize @ihA x' (by simp_all) Δ (Δ'.typeExt x' K') (by aesop)
      simp_all [Environment.append]
    . specialize @ihB Δ Δ'; simp_all
  . case listAppId Δ_ A K' A' AkiLK AA' ih =>
    subst Δ_
    refine .listAppId ?_ (by simp_all)
    . rw [<- Environment.append_term_assoc]; exact Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) AkiLK
  . case lam I Δ_ K' A B red ih =>
    subst Δ_
    apply ParallelReduction.lam (I := x :: I)
    intro a' notIn
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K') (by aesop)
    simp_all [Environment.append]
  . case scheme I Δ_ K' A B red ih =>
    subst Δ_
    apply ParallelReduction.scheme (I := x :: I)
    intro a' notIn
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K') (by aesop)
    simp_all [Environment.append]

theorem weakening_term (red: [[ Δ ⊢ A ≡> B ]]) : [[ Δ, x: T ⊢ A ≡> B ]] := by
  apply weakening_term' (Δ' := Environment.empty); assumption

open Environment in
theorem weakening' (red: [[ Δ, Δ'' ⊢ A ≡> B ]]) (wfτ: [[ ⊢τ Δ, Δ', Δ'' ]]) : [[ Δ, Δ', Δ'' ⊢ A ≡> B ]] := by
  induction Δ' generalizing Δ''
  . case empty => simp_all [empty_append]
  . case typeExt Δ' a' K' ih =>
    specialize ih red (by
      rw [append_assoc, <- append_typeExt_assoc] at wfτ
      rw [append_assoc]
      exact wfτ.TypeVar_drop
    )
    rw [append_assoc]
    apply weakening_type'
    . rw [<- append_assoc]
      exact ih
    . rw [<- append_type_assoc, append_assoc] at wfτ
      exact wfτ.append_typeVar_fresh_l a' (by simp_all [typeVarDom_append, typeVarDom])
  . case termExt Δ' x T ih =>
    specialize ih red (by
      rw [append_assoc, <- append_termExt_assoc] at wfτ
      rw [append_assoc]
      exact wfτ.TermVar_drop
    )
    rw [append_assoc]
    apply weakening_term'
    rw [<- append_assoc]
    exact ih

-- NOTE we could use a weaker wf: wfτ
-- NOTE using this weaker wf we can remove subst on Δ' for pred_subst theorems (25/03/07: what does this mean?)
theorem weakening (red: [[ Δ ⊢ A ≡> B ]]) (wf: [[ ⊢ Δ, Δ' ]]) : [[ Δ, Δ' ⊢ A ≡> B ]] := by
  induction Δ'
  . case empty => simp_all [Environment.append]
  . case typeExt Δ' a' K' ih =>
    simp_all [Environment.append]
    apply weakening_type
    . apply ih
      cases wf; assumption
    . cases wf; simp_all [Environment.TypeVarNotInDom, Environment.TypeVarInDom]
  . case termExt Δ' a' T ih =>
    simp_all [Environment.append]
    apply weakening_term
    apply ih
    cases wf; assumption

theorem subst_in {A B T: «Type»} (red: [[ Δ ⊢ A ≡> B ]]) (lcA: A.TypeVarLocallyClosed 0) (lcT: T.TypeVarLocallyClosed 0): ParallelReduction Δ (T.TypeVar_subst a A) (T.TypeVar_subst a B) := by
  rw [<- Type.TypeVarLocallyClosed.aux_iff] at lcT
  induction lcT generalizing Δ <;> simp_all [«Type».TypeVar_subst] <;> try aesop (rule_sets := [pred])
  . case lam I K T lc ih =>
    apply ParallelReduction.lam (I := a :: I ++ A.freeTypeVars ++ Δ.typeVarDom)
    intro a' notIn
    rw [<- lcA.TypeVar_open_TypeVar_subst_comm (by aesop)]
    rw [<- red.preserve_lc lcA |>.TypeVar_open_TypeVar_subst_comm (by aesop)]
    obtain red := weakening_type (a := a') (K := K) (red := red) (freshΔ := by simp_all)
    simp_all
  . case «forall» I K T lc ih =>
    apply ParallelReduction.scheme (I := a :: I ++ A.freeTypeVars ++ Δ.typeVarDom)
    intro a' notIn
    rw [<- lcA.TypeVar_open_TypeVar_subst_comm (by aesop)]
    rw [<- red.preserve_lc lcA |>.TypeVar_open_TypeVar_subst_comm (by aesop)]
    obtain red := weakening_type (a := a') (K := K) (red := red) (freshΔ := by simp_all)
    simp_all
  . case list Tl lc ih =>
    apply ParallelReduction.list' (length_eq := by simp_all [List.length_map])
    simp_all [List.zip]
    aesop

-- NOTE we could use a weaker wf: wfτ
theorem subst_out' {A T T' : «Type»} (wf: [[ ⊢ Δ, a: K, Δ' ]]) (red : [[ Δ, a: K, Δ' ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡> T'[A/a] ]] := by
  generalize Δ_eq: (Δ.typeExt a K |>.append Δ') = Δ_ at red
  induction red generalizing Δ Δ' <;> (try simp_all [Type.TypeVar_subst]) <;> try (aesop (rule_sets := [pred]); done)
  · case var => split <;> exact .refl
  . case lamApp Δ_ T2 K' I T1 T1' T2' kindT2 redT1 redT2 ihT1 ihT2 =>
    subst Δ_
    rw [kindA.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist]
    apply ParallelReduction.lamApp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    . apply Kinding.subst' (K := K) <;> simp_all
    . intro a' notIn
      repeat rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
      rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
      apply ihT1 <;> simp_all [Environment.append]
      . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    . simp_all
  . case listAppList Δ_ T1 T1' n T2 T2' redT1 redT2 T1lc ihT1 ihT2 =>
    subst Δ_
    unfold Function.comp
    simp [Type.TypeVar_subst]
    apply ParallelReduction.listAppList
    . apply ihT1 <;> simp_all [Environment.append]
    . simp_all
    . have Alc := kindA.TypeVarLocallyClosed_of
      exact T1lc.TypeVar_subst Alc
  . case listAppId Δ_ A K' A' AkiLK AA' ih =>
    subst Δ_
    refine .listAppId ?_ (by simp_all)
    . apply Kinding.subst' (K := K) <;> simp_all
  . case lam I Δ_ K' T T' red ih =>
    subst Δ_
    apply ParallelReduction.lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    repeat rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
  . case scheme I Δ_ K' T T' red ih =>
    subst Δ_
    apply ParallelReduction.scheme (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    repeat rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
  . sorry
    -- case listAppComp Δ_ _ I K' _ _ _ _ lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    -- subst Δ_
    -- have Alc := kindA.TypeVarLocallyClosed_of
    -- refine .listAppComp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    --   (lcA₀.TypeVar_subst Alc)
    --   (by simp_all) (λa' nin => ?_) (by simp_all)
    -- specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]] (by
    --   rw [← Environment.append_typeExt_assoc]
    --   refine wf.typeVarExt ?_
    --   simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    -- ) kindA rfl
    -- repeat1' rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    -- simp_all [Environment.append_typeExt_assoc, Environment.typeExt_subst]

-- NOTE we could use a weaker wf: wfτ
theorem subst_out {A T T' : «Type»} (wf: [[ ⊢ Δ, a: K ]]) (red : [[ Δ, a: K ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ ⊢ T[A/a] ≡> T'[A/a] ]] := by
  apply subst_out' (Δ' := Environment.empty) <;> assumption

-- NOTE we could use a weaker wf: wfτ
set_option maxHeartbeats 400000 in  -- bruh
theorem subst_all' {A B T: «Type»} (wf: [[ ⊢ Δ, a: K, Δ' ]]) (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ, a: K, Δ' ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) (lcT: T.TypeVarLocallyClosed): [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡> T'[B/a] ]] := by
  generalize Δ_eq: (Δ.typeExt a K |>.append Δ') = Δ_ at red2
  induction red2 generalizing Δ Δ' A B
  . case var Δ_ T_ =>
    apply subst_in (lcA := kindA.TypeVarLocallyClosed_of) (lcT := lcT)
    apply weakening
    . assumption
    . apply EnvironmentWellFormedness.subst (K := K) <;> simp_all
  . case lamApp Δ_ T2 K2 I T1 T1' T2' kindT2 redT1 redT2 ihT1 ihT2 =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    rw [red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.Type_open_TypeVar_subst_dist]
    apply ParallelReduction.lamApp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    . apply Kinding.subst' (K := K) <;> assumption
    . case a =>
      intro a' notIn
      rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
      rw [<- red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
      rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
      apply ihT1 <;> simp_all [Environment.append]
      . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
      . aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
    . apply ihT2 <;> try simp_all [Environment.append]
      aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
  . case listAppList Δ_ T1 T1' n T2 T2' redT1 redT2 T1lc ihT1 ihT2 =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    unfold Function.comp
    simp [«Type».TypeVar_subst]
    apply ParallelReduction.listAppList
    . apply ihT1 <;> simp_all [Environment.append]
    . intro i iltn
      match lcT with
      | .listApp _ (.list lcT2) =>
        simp_all [Std.Range.mem_map_of_mem, Std.Range.mem_of_mem_toList]
    . have Alc := kindA.TypeVarLocallyClosed_of
      exact T1lc.TypeVar_subst Alc
  . case listAppId Δ_ _ _ _ _ _ ih =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    apply ParallelReduction.listAppId
    . apply Kinding.subst' (K := K) <;> simp_all
    . match lcT with
      | .listApp _ _ =>
        apply ih <;> try simp_all [Environment.append]
  . case lam I Δ_ K' T T' redT ih =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    apply ParallelReduction.lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [<- red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    . aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
  . case app =>
    cases lcT
    simp_all [«Type».TypeVar_subst]
    constructor <;> simp_all
  . case scheme I Δ_ K' T T' redT ih =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    apply ParallelReduction.scheme (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [<- red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    . aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
  . case arr =>
    cases lcT
    simp_all [«Type».TypeVar_subst]
    constructor <;> simp_all
  . case list n Δ_ T T' red ih =>
    cases lcT
    simp_all [«Type».TypeVar_subst]
    constructor; simp_all [Std.Range.mem_toList_of_mem]
  . case listApp =>
    cases lcT
    simp_all [«Type».TypeVar_subst]
    constructor <;> simp_all
  . sorry
    -- case listAppComp Δ_ _ I K' _ _ _ _ lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    -- subst Δ_
    -- match lcT with
    -- | .listApp lcA₀ (.listApp (.lam bodyA₁) lcB) =>
    --   cases lcT
    --   simp [«Type».TypeVar_subst]
    --   refine .listAppComp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    --     (lcA₀.TypeVar_subst kindA.TypeVarLocallyClosed_of)
    --     (by simp_all) (λa' nin => ?_) (by simp_all)
    --   . specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]] _ _ (by
    --       rw [← Environment.append_typeExt_assoc]
    --       refine wf.typeVarExt ?_
    --       simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    --     ) red1 kindA bodyA₁.strengthen rfl
    --     rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    --     rw [<- red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    --     rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    --     simp_all [Environment.append_typeExt_assoc, Environment.typeExt_subst]
  . case prod =>
    cases lcT
    simp_all [«Type».TypeVar_subst]
    constructor; simp_all
  . case sum =>
    cases lcT
    simp_all [«Type».TypeVar_subst]
    constructor; simp_all

theorem subst_all {A B T: «Type»} (wf: [[ ⊢ Δ, a: K ]]) (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ, a: K ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) (lcT: T.TypeVarLocallyClosed): [[ Δ ⊢ T[A/a] ≡> T'[B/a] ]] := by
  apply subst_all' (Δ' := Environment.empty) <;> assumption

-- NOTE this lemma doesn't necessarily require subst lemma. See rename lemma in the paper.
theorem rename (red: [[ Δ, a: K ⊢ A^a ≡> B^a ]]) (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (fresh2: a' ∉ a :: Δ.typeVarDom) (wf: [[ ⊢ Δ ]]): [[ Δ, a': K ⊢ A^a' ≡> B^a' ]] := by
  repeat rw [Type.Type_open_var]
  repeat rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
  apply subst_out (K := K)
  . aesop (add norm Environment.typeVarDom, safe constructors EnvironmentWellFormedness, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom)
  . rw [<- Environment.append_empty (Δ := Δ |>.typeExt a' K |>.typeExt a K)]
    rw [<- Environment.append_type_assoc (Δ' := Environment.empty)]
    apply weakening_type'
    . simp_all [Environment.append]
    . simp_all
  . repeat' constructor

theorem lam_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (wf: [[ ⊢ Δ ]]) (red: [[ Δ, a : K ⊢ A^a ≡> B^a ]]): [[ Δ ⊢ (λ a : K. A) ≡> (λ a : K. B) ]] := by
  apply ParallelReduction.lam (I := a :: Δ.typeVarDom)
  intro a' notIn
  apply ParallelReduction.rename (a := a) <;> simp_all

theorem lamApp_intro_ex a (fresh: a ∉ A.freeTypeVars ++ A'.freeTypeVars ++ Δ.typeVarDom) (wf: [[ ⊢ Δ ]]) (kind: [[ Δ ⊢ B: K ]]) (redA: [[ Δ, a: K ⊢ A^a ≡> A'^a ]]) (redB: [[ Δ ⊢ B ≡> B' ]]): [[ Δ ⊢ (λ a : K. A) B ≡> A'^^B' ]] := by
  apply ParallelReduction.lamApp (I := a :: Δ.typeVarDom) <;> try assumption
  intro a' notIn
  apply ParallelReduction.rename (a := a) <;> simp_all

theorem forall_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (wf: [[ ⊢ Δ ]]) (red: [[ Δ, a : K ⊢ A^a ≡> B^a ]]): [[ Δ ⊢ (∀ a : K. A) ≡> (∀ a : K. B) ]] := by
  apply ParallelReduction.scheme (I := a :: Δ.typeVarDom)
  intro a' notIn
  apply ParallelReduction.rename (a := a) <;> simp_all

-- NOTE must have for conf_lamApp: needed when using pred_subst

theorem preservation (red: [[ Δ ⊢ A ≡> B ]]) (wf: [[ ⊢ Δ ]]) (k: [[ Δ ⊢ A: K ]]): [[ Δ ⊢ B: K ]] := by
  induction red generalizing K
  case var => simp_all
  case lamApp Δ B KB I A A' B' kindB redA redB ihA ihB =>
    cases k; case app _ _ k =>
    cases k; case lam I' _ kindA =>
    have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ Δ.typeVarDom).exists_fresh
    have wf': [[ ⊢ Δ, a: KB ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    have kindA' := ihA a (by simp_all) wf' (kindA a (by aesop))
    have kindB' := ihB wf kindB
    rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a:=a) (by aesop)]
    apply Kinding.subst <;> assumption
  case listAppList Δ A A' n B B' redA redB Alc ihA ihB =>
    cases k; case listApp K KB kA kB =>
    have kB := kB.inv_list; rename_i kB_; clear kB_
    constructor; case a =>
    intro i mem; simp_all
    have kA' := ihA kA
    cases n
    . case zero => simp_all [Membership.mem]
    . case succ n =>
      have kB' := ihB i mem (kB i mem)
      exact kA'.app kB'
  case listAppComp => sorry
  -- case listAppComp Δ A₀' I K _ _ _ _ lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
  --   cases k; case listApp K1 K2 kA₀ kA₁B =>
  --   cases kA₁B; case listApp K3 kB kA₁ =>
  --   cases kA₁; case lam I' kA₁ =>

  --   specialize ihA₀ wf kA₀
  --   specialize ihB wf kB

  --   have ⟨a, nin⟩ := (I ++ I' ++ Δ.typeVarDom ++ A₀'.freeTypeVars).exists_fresh
  --   refine .listApp (.lam (I ++ I' ++ Δ.typeVarDom ++ A₀'.freeTypeVars) λa nin => ?_) ihB

  --   specialize ihA₁ a (by simp_all) (wf.typeVarExt (by simp_all [Environment.TypeVarNotInDom, Environment.TypeVarInDom])) (kA₁ a (by simp_all))

  --   have ihA₀ := ihA₀.weakening_r (Δ' := [[ ε, a: K ]]) (by simp_all [Environment.typeVarDom])
  --   simp [Environment.append] at ihA₀
  --   rw [← A₀A₀'.preserve_lc lcA₀ |>.TypeVar_open_id (a := a)] at ihA₀
  --   have ihA₀A₁ := ihA₀.app ihA₁
  --   simp_all [Type.TypeVar_open]
  case lam I Δ K1 A B red ih =>
    cases k; case lam K2 I' kindA =>
    apply Kinding.lam (I := I ++ I' ++ Δ.typeVarDom)
    intro a notIn
    have wf': [[ ⊢ Δ, a: K1 ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    simp_all
  case scheme I Δ K1 A B red ih =>
    cases k; case scheme I' kindA =>
    apply Kinding.scheme (I := I ++ I' ++ Δ.typeVarDom)
    intro a notIn
    have wf': [[ ⊢ Δ, a: K1 ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    simp_all
  case list n Δ_ A B red ih =>
    have ⟨K_, eqK_, k'⟩ := k.inv_list'; subst K
    set_option aesop.dev.statefulForward false in
    constructor; aesop (add safe forward Std.Range.mem_toList_of_mem, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed)
  case listAppId Δ _ _ K_ _ _ _ =>
    -- NOTE wts. K2 = K_
    cases k; case listApp K1 K2 ka kA =>
    cases ka; case lam I ka =>
    have ⟨a, nin⟩ := (I ++ Δ.typeVarDom).exists_fresh
    specialize ka a (by simp_all)
    simp [Type.TypeVar_open] at ka
    cases ka; case var ain =>
    cases ain <;> simp_all [TypeVarNe]
  all_goals cases k; constructor <;> aesop (add safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })

-- NOTE critical

@[app_unexpander Std.Range.mk]
def Rangemk.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) 0 $n 1 $_) =>
    `([ : $n ])
  | `($(_) $m $n 1 $_) =>
    `([ $m : $n ])
  | `($(_) $m $n $i $_) =>
    `([ $m : $n : $i ])
  | _ => throw ()

end ParallelReduction

lemma Type.expand_app_id (T: «Type») : T = [[ (a$0^^T) ]] := by simp [Type.Type_open]

namespace CompleteDevelopment

theorem list_inversion (pr : [[Δ ⊢ {</ A@i // i in [:n] />} ≡>> B]])
  : ∃ C, B = [[{</ C@i // i in [:n] />}]] ∧ ∀ i ∈ [:n], [[Δ ⊢ A@i ≡>> C@i]] := by
  generalize Aseq : [:n].map _ = As at pr
  let .list pr' (B := C) := pr
  let lengths_eq : List.length ([:n].map ..) = _ := by rw [Aseq]
  rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
      Nat.sub_zero] at lengths_eq
  cases lengths_eq
  refine ⟨_, rfl, ?_⟩
  intro i mem
  rw [Range.eq_of_mem_of_map_eq Aseq _ mem]
  exact pr' i mem

open «Type» in
theorem TypeVar_subst_var {a' : TypeVarId} (cd : [[Δ, a : K, Δ' ⊢ A ≡>> B]])
  (wf : [[⊢ Δ, a : K, Δ']]) (a'ki : [[Δ ⊢ a' : K]])
  : [[Δ, Δ'[a' / a] ⊢ A[a' / a] ≡>> B[a' / a] ]] := by match cd with
  | .var =>
    rw [TypeVar_subst]
    split <;> exact .var
  | lamApp B'ki A'cd B'cd (I := I) =>
    rw [TypeVar_subst, TypeVar_subst, TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free]
    apply lamApp (I := a :: I ++ [[Δ, a : K, Δ']].typeVarDom) (B'ki.subst' wf a'ki) _
      (TypeVar_subst_var B'cd wf a'ki)
    intro a'' a''nin
    let ⟨a''ninaI, a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨a''ne, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm .var_free a''ne.symm,
        ← TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm .var_free a''ne.symm]
    rw [← Environment.append, ← Environment.TypeVar_subst]
    apply TypeVar_subst_var _ _ a'ki
    all_goals rw [Environment.append]
    · exact A'cd a'' a''ninI
    · exact wf.typeVarExt a''ninΔ
  | listAppList ne A'cd B'cd (A := A') (A' := A'') (B := B') (B' := B'') =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, List.mapMem_eq_map, List.mapMem_eq_map,
        List.map_map, List.map_map, ← Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = [[(B'@i[a' / a])]]
      simp
    ), ← Range.map, Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = [[(A''[a' / a] B''@i[a' / a])]]
      simp [TypeVar_subst]
    ), ← Range.map]
    apply listAppList _ (TypeVar_subst_var A'cd wf a'ki) (B'cd · · |>.TypeVar_subst_var wf a'ki)
    intro K eq
    cases A'
    all_goals rw [TypeVar_subst] at eq
    case var =>
      split at eq <;> nomatch eq
    case lam K' A''' =>
      rcases Type.lam.inj eq with ⟨rfl, eq'⟩
      cases A'''
      all_goals rw [TypeVar_subst] at eq'
      case var =>
        split at eq'
        · cases eq'
        · cases eq'
          nomatch ne K'
      all_goals nomatch eq'
    all_goals nomatch eq
  | listAppId A'ki A'cd =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, if_neg nofun]
    exact listAppId (A'ki.subst' wf a'ki) <| TypeVar_subst_var A'cd wf a'ki
  | lam A'cd (I := I) =>
    rw [TypeVar_subst, TypeVar_subst]
    apply lam (I := a :: I ++ [[Δ, a : K, Δ']].typeVarDom)
    intro a'' a''nin
    let ⟨a''ninaI, a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨a''ne, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm .var_free a''ne.symm,
        ← TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm .var_free a''ne.symm]
    rw [← Environment.append, ← Environment.TypeVar_subst]
    apply TypeVar_subst_var _ _ a'ki
    all_goals rw [Environment.append]
    · exact A'cd a'' a''ninI
    · exact wf.typeVarExt a''ninΔ
  | app ne A'cd B'cd (A₁ := A₁) =>
    rw [TypeVar_subst, TypeVar_subst]
    apply app _ (TypeVar_subst_var A'cd wf a'ki) (TypeVar_subst_var B'cd wf a'ki)
    intro K' A₁' eq
    cases A₁
    all_goals rw [TypeVar_subst] at eq
    case var => split at eq <;> nomatch eq
    case lam K' A₁'' => nomatch ne K' A₁''
    all_goals nomatch eq
  | scheme A'cd (I := I) =>
    rw [TypeVar_subst, TypeVar_subst]
    apply scheme (I := a :: I ++ [[Δ, a : K, Δ']].typeVarDom)
    intro a'' a''nin
    let ⟨a''ninaI, a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨a''ne, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm .var_free a''ne.symm,
        ← TypeVarLocallyClosed.TypeVar_open_TypeVar_subst_comm .var_free a''ne.symm]
    rw [← Environment.append, ← Environment.TypeVar_subst]
    apply TypeVar_subst_var _ _ a'ki
    all_goals rw [Environment.append]
    · exact A'cd a'' a''ninI
    · exact wf.typeVarExt a''ninΔ
  | arr A'cd B'cd =>
    rw [TypeVar_subst, TypeVar_subst]
    apply arr (TypeVar_subst_var A'cd wf a'ki) (TypeVar_subst_var B'cd wf a'ki)
  | list A'cd (A := A') (B := A'') =>
    rw [TypeVar_subst, TypeVar_subst, List.mapMem_eq_map, List.mapMem_eq_map,
        List.map_map, List.map_map, ← Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = [[(A'@i[a' / a])]]
      simp
    ), ← Range.map, Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = [[(A''@i[a' / a])]]
      simp
    ), ← Range.map]
    exact list (A'cd · · |>.TypeVar_subst_var wf a'ki)
  | listApp ne ne' A'cd B'cd (A₁ := A') (B₁ := B') =>
    rw [TypeVar_subst, TypeVar_subst]
    apply listApp _ _ (TypeVar_subst_var A'cd wf a'ki) (TypeVar_subst_var B'cd wf a'ki)
    · intro K eq
      cases A'
      all_goals rw [TypeVar_subst] at eq
      case var =>
        split at eq <;> nomatch eq
      case lam K' A''' =>
        rcases Type.lam.inj eq with ⟨rfl, eq'⟩
        cases A'''
        all_goals rw [TypeVar_subst] at eq'
        case var =>
          split at eq'
          · cases eq'
          · cases eq'
            nomatch ne K'
        all_goals nomatch eq'
      all_goals nomatch eq
    · intro B'' n eq
      cases B'
      all_goals rw [TypeVar_subst] at eq
      case var => split at eq <;> nomatch eq
      case list B's =>
        rw [List.mapMem_eq_map] at eq
        specialize ne' B's.get! n
        injection eq with eq
        let lengths_eq : List.length (List.map ..) = _ := by rw [eq]
        rw [List.length_map, List.length_map, Range.length_toList, Nat.sub_zero] at lengths_eq
        cases lengths_eq
        rw (occs := .pos [1]) [← Range.map_get!_eq (as := B's)] at eq ne'
        apply ne'
        apply Type.list.injEq .. |>.mpr
        apply Range.map_eq_of_eq_of_mem''
        intro i mem
        rfl
      all_goals nomatch eq
  | listAppComp ne A'cd B'cd (A := A') =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst]
    apply listAppComp _ (TypeVar_subst_var A'cd wf a'ki)
    · rw [← TypeVar_subst, ← TypeVar_subst]
      exact TypeVar_subst_var B'cd wf a'ki
    · intro K eq
      cases A'
      all_goals rw [TypeVar_subst] at eq
      case var =>
        split at eq <;> nomatch eq
      case lam K' A''' =>
        rcases Type.lam.inj eq with ⟨rfl, eq'⟩
        cases A'''
        all_goals rw [TypeVar_subst] at eq'
        case var =>
          split at eq'
          · cases eq'
          · cases eq'
            nomatch ne K'
        all_goals nomatch eq'
      all_goals nomatch eq
  | prod A'cd =>
    rw [TypeVar_subst, TypeVar_subst]
    exact prod <| TypeVar_subst_var A'cd wf a'ki
  | sum A'cd =>
    rw [TypeVar_subst, TypeVar_subst]
    exact sum <| TypeVar_subst_var A'cd wf a'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · apply Nat.le_of_lt
    apply Nat.lt_add_right
    apply Nat.lt_add_left
    apply List.sizeOf_lt_of_mem
    apply Range.mem_map_of_mem
    assumption
  · apply Nat.le_of_lt
    apply List.sizeOf_lt_of_mem
    apply Range.mem_map_of_mem
    assumption

theorem weakening : [[Δ, Δ'' ⊢ A ≡>> B]] → [[⊢ Δ, Δ', Δ'']] → [[Δ, Δ', Δ'' ⊢ A ≡>> B]] := sorry

theorem TypeVar_open_swap (cd : [[Δ, a : K ⊢ A^a ≡>> B]]) (Alc : A.TypeVarLocallyClosed 1)
  (Blc : B.TypeVarLocallyClosed) (aninA : a ∉ A.freeTypeVars) (Δwf : [[⊢ Δ, a' : K, a : K]])
  : [[Δ, a' : K ⊢ A^a' ≡>> (\a^B)^a']] := by
  have : A.TypeVar_open a' = (A.TypeVar_open a).TypeVar_subst a (.var a') := by
    rw [Type.Type_open_var, Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA, Type.TypeVar_subst, if_pos rfl]
  rw [this]
  let Aoplc := Alc.Type_open_dec .var_free (B := .var a)
  rw [← Type.Type_open_var] at Aoplc
  have : (B.TypeVar_close a).TypeVar_open a' = B.TypeVar_subst a (.var a') := by
    rw [Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst Blc]
  rw [this]
  apply TypeVar_subst_var (Δ' := .empty) _ Δwf (.var .head)
  exact cd.weakening Δwf (Δ' := [[ε, a' : K]]) (Δ'' := [[ε, a : K]])

set_option maxHeartbeats 4000000 in
open «Type» in
def ParallelReduction_close
  (cd : [[Δ ⊢ A ≡>> C]]) (pr : [[Δ ⊢ A ≡> B]]) (wf : [[⊢ Δ]]) (lc : TypeVarLocallyClosed A)
  : [[Δ ⊢ B ≡> C]] := by match cd, pr, lc with
  | .var, .var, _ => exact .var
  | .lamApp B'ki A'cd B'cd (I := I) (K := K) (A' := A''), .lamApp _ A'pr B'pr (I := I'), .app (.lam A'lc) B'lc =>
    rename_i A''' _ _
    let ⟨a, anin⟩ := A''.freeTypeVars ++ A'''.freeTypeVars ++ I ++ I' ++ Δ.typeVarDom
      |>.exists_fresh
    let ⟨aninA''A'''II', aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA''A'''I, aninI'⟩ := List.not_mem_append'.mp aninA''A'''II'
    let ⟨aninA''A''', aninI⟩ := List.not_mem_append'.mp aninA''A'''I
    let ⟨aninA'', aninA'''⟩ := List.not_mem_append'.mp aninA''A'''
    let awf := wf.typeVarExt aninΔ (K := K)
    rw [← TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA'',
        ← TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA''']
    specialize A'pr a aninI'
    exact ParallelReduction.subst_all awf (B'cd.ParallelReduction_close B'pr wf B'lc)
      (ParallelReduction_close (A'cd a aninI) A'pr awf A'lc.TypeVar_open_dec)
      (B'pr.preservation wf B'ki) <| A'pr.preserve_lc A'lc.TypeVar_open_dec
  | .lamApp B'ki A'cd B'cd (I := I), .app A'pr B'pr, .app (.lam A'lc) B'lc =>
    rcases A'pr.inv_lam with ⟨A'', rfl, I', A'pr'⟩
    apply ParallelReduction.lamApp (I := I ++ I' ++ Δ.typeVarDom) (B'pr.preservation wf B'ki) _
      (ParallelReduction_close B'cd B'pr wf B'lc)
    intro a anin
    let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact ParallelReduction_close (A'cd a aninI) (A'pr' a aninI') (wf.typeVarExt aninΔ)
      A'lc.TypeVar_open_dec
  | .listAppList ne A'cd B'cd (A := A'), pr, .listApp A'lc (.list B'lc) =>
    generalize Bseq : [:_].map _ = Bs at pr
    match __ : pr with
    | .listAppList A'pr B'pr _ =>
      let lengths_eq : List.length ([:_].map _) = _ := by rw [Bseq]
      rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
          Nat.sub_zero] at lengths_eq
      cases lengths_eq
      apply ParallelReduction.list
      intro i mem
      apply ParallelReduction.app
      · exact ParallelReduction_close A'cd A'pr wf A'lc
      · apply ParallelReduction_close (B'cd i mem) _ wf <| B'lc _ <|
          Range.mem_map_of_mem mem
        rw [Range.eq_of_mem_of_map_eq Bseq _ mem]
        exact B'pr i mem
    | .listAppId _ _ (K := K) => nomatch ne K
    | .listApp A'pr B'pr =>
      cases Bseq
      rcases B'pr.inv_list with ⟨_, rfl, B'pr'⟩
      apply ParallelReduction.listAppList (ParallelReduction_close A'cd A'pr wf A'lc) _ <|
        A'pr.preserve_lc A'lc
      intro i mem
      exact ParallelReduction_close (B'cd i mem) (B'pr' i mem) wf <| B'lc _ <|
        Range.mem_map_of_mem mem
  | .listAppId A'ki A'cd, .listAppId _ A'pr, .listApp _ A'lc =>
    exact ParallelReduction_close A'cd A'pr wf A'lc
  | .listAppId A'ki A'cd, .listAppList idpr A'pr _, .listApp _ (.list A'lc) =>
    let A'ki' := A'ki.inv_list
    cases idpr.inv_id
    rcases A'cd.list_inversion with ⟨C, rfl, A'cd'⟩
    apply ParallelReduction.list
    intro i mem
    specialize A'pr i mem
    have : C i = Type_open (.var (.bound 0)) (C i) := by
      rw [Type_open, if_pos rfl]
    rw [this]
    apply ParallelReduction.lamApp (A'pr.preservation wf (A'ki' i mem)) (I := []) (fun _ _ => .refl)
    exact ParallelReduction_close (A'cd' i mem) A'pr wf <| A'lc _ <| Range.mem_map_of_mem mem
  | .listAppId A'ki A'cd, .listApp idpr A'pr, .listApp _ A'lc =>
    cases idpr.inv_id
    apply ParallelReduction.listAppId (A'pr.preservation wf A'ki)
    exact ParallelReduction_close A'cd A'pr wf A'lc
  | .listAppId .., .listAppComp .., _ => sorry
  | .lam A'cd (I := I), .lam A'pr (I := I'), .lam A'lc =>
    apply ParallelReduction.lam (I := I ++ I' ++ Δ.typeVarDom)
    intro a anin
    let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact ParallelReduction_close (A'cd a aninI) (A'pr a aninI') (wf.typeVarExt aninΔ)
      A'lc.TypeVar_open_dec
  | .app ne A'cd B'cd, pr, .app A'lc B'lc => match pr with
    | .app A'pr B'pr =>
      exact ParallelReduction.app (ParallelReduction_close A'cd A'pr wf A'lc)
        (ParallelReduction_close B'cd B'pr wf B'lc)
    | .lamApp _ _ _ (K := K) (A := A') => nomatch ne K A'
  | .scheme A'cd (I := I), .scheme A'pr (I := I'), .forall A'lc =>
    apply ParallelReduction.scheme (I := I ++ I' ++ Δ.typeVarDom)
    intro a anin
    let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact ParallelReduction_close (A'cd a aninI) (A'pr a aninI') (wf.typeVarExt aninΔ)
      A'lc.TypeVar_open_dec
  | .arr A'cd B'cd, .arr A'pr B'pr, .arr A'lc B'lc =>
    exact .arr (ParallelReduction_close A'cd A'pr wf A'lc)
      (ParallelReduction_close B'cd B'pr wf B'lc)
  | .list A'cd, pr, .list A'lc =>
    rcases pr.inv_list with ⟨_, rfl, A'pr⟩
    exact .list fun i mem =>
      ParallelReduction_close (A'cd i mem) (A'pr i mem) wf <| A'lc _ <| Range.mem_map_of_mem mem
  | .listApp ne ne' A'cd B'cd, pr, .listApp A'lc B'lc => match pr with
    | .listAppList _ _ _ (B := B') (n := n) => nomatch ne' B' n
    | .listAppId _ _ (K := K) => nomatch ne K
    | .listApp A'pr B'pr =>
      exact .listApp (ParallelReduction_close A'cd A'pr wf A'lc)
        (ParallelReduction_close B'cd B'pr wf B'lc)
    | .listAppComp .. => sorry
  | .listAppComp ne A'cd B'cd, pr, _ => match pr with
    | .listAppList .. =>
      rcases B'cd.list_inversion with ⟨_, eq, _⟩
      nomatch eq
    | .listAppId _ _ (K := K) => nomatch ne K
    | .listApp .. => sorry
    | .listAppComp .. => sorry
  | .prod A'cd, .prod A'pr, .prod A'lc =>
    exact .prod <| ParallelReduction_close A'cd A'pr wf A'lc
  | .sum A'cd, .sum A'pr, .sum A'lc =>
    exact .sum <| ParallelReduction_close A'cd A'pr wf A'lc
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · rename _ = A' => eq
    cases eq
    simp_arith
  · apply Nat.le_of_lt
    apply Nat.lt_add_right
    apply Nat.lt_add_left
    apply List.sizeOf_lt_of_mem
    exact Range.mem_map_of_mem mem
  · rename _ = A' => eq
    cases eq
    simp_arith
  · apply Nat.le_of_lt
    apply Nat.lt_add_right
    apply Nat.lt_add_left
    apply List.sizeOf_lt_of_mem
    exact Range.mem_map_of_mem mem
  · apply Nat.le_of_lt
    apply Nat.lt_add_right
    apply Nat.lt_add_left
    apply List.sizeOf_lt_of_mem
    exact Range.mem_map_of_mem mem
  · apply Nat.le_of_lt
    apply List.sizeOf_lt_of_mem
    exact Range.mem_map_of_mem mem

theorem preserve_lc (cd : [[Δ ⊢ A ≡>> B]]) (Δwf : [[⊢ Δ]]) (Alc : A.TypeVarLocallyClosed)
  : B.TypeVarLocallyClosed :=
  ParallelReduction_close cd .refl Δwf Alc |>.preserve_lc Alc

open «Type» in
theorem total (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]]) : ∃ B, [[Δ ⊢ A ≡>> B]] := by match A, Aki with
  | .var _, .var _ => exact ⟨_, .var⟩
  | .lam K' A', .lam I A'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
    let ⟨aninA'I, aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp aninA'I
    specialize A'ki a aninI
    let Δawf := Δwf.typeVarExt aninΔ (K := K')
    let ⟨B', A'cd⟩ := total A'ki Δawf
    refine ⟨.lam K' (B'.TypeVar_close a), .lam (I := a :: Δ.typeVarDom) ?_⟩
    intro a' a'nin
    let ⟨ane, a'ninΔ⟩ := List.not_mem_cons.mp a'nin
    let Δa'awf := Δwf.typeVarExt a'ninΔ (K := K') |>.typeVarExt (K := K') <|
      List.not_mem_cons.mpr ⟨ane.symm, aninΔ⟩
    let A'lc := A'ki.TypeVarLocallyClosed_of
    let B'lc := A'cd.preserve_lc Δawf A'lc
    apply TypeVarLocallyClosed.TypeVar_close_inc (a := a) at A'lc
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact TypeVar_open_swap A'cd A'lc B'lc aninA' Δa'awf
  | .app A' B', .app A'ki B'ki =>
    let ⟨B'', B'cd⟩ := total B'ki Δwf
    by_cases ∃ K A'', A' = [[λ a : K. A'']]
    · case pos h =>
      rcases h with ⟨K, A'', rfl⟩
      let .lam I A''ki := A'ki
      let ⟨a, anin⟩ := A''.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
      let ⟨aninA''I, aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninA'', aninI⟩ := List.not_mem_append'.mp aninA''I
      let ⟨A''', A''cd⟩ := total (A''ki a aninI) (Δwf.typeVarExt aninΔ)
      let A''lc := A''ki a aninI |>.TypeVarLocallyClosed_of
      let A'''lc := A''cd.preserve_lc (Δwf.typeVarExt aninΔ) A''lc
      apply TypeVarLocallyClosed.TypeVar_close_inc (a := a) at A''lc
      rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A''lc
      refine ⟨[[((\a^A''')^^B'')]], lamApp B'ki (I := a :: Δ.typeVarDom) ?_ B'cd⟩
      intro a' a'nin
      let ⟨ane, a'ninΔ⟩ := List.not_mem_cons.mp a'nin
      exact TypeVar_open_swap A''cd A''lc A'''lc aninA'' <|
        Δwf.typeVarExt a'ninΔ |>.typeVarExt <| List.not_mem_cons.mpr ⟨ane.symm, aninΔ⟩
    · case neg ne =>
      let ⟨_, A'cd⟩ := total A'ki Δwf
      exact ⟨_, .app (not_exists.mp <| not_exists.mp ne ·) A'cd B'cd⟩
  | .forall K' A', .scheme I A'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
    let ⟨aninA'I, aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp aninA'I
    specialize A'ki a aninI
    let Δawf := Δwf.typeVarExt aninΔ (K := K')
    let ⟨B', A'cd⟩ := total A'ki Δawf
    refine ⟨.forall K' (B'.TypeVar_close a), .scheme (I := a :: Δ.typeVarDom) ?_⟩
    intro a' a'nin
    let ⟨ane, a'ninΔ⟩ := List.not_mem_cons.mp a'nin
    let Δa'awf := Δwf.typeVarExt a'ninΔ (K := K') |>.typeVarExt (K := K') <|
      List.not_mem_cons.mpr ⟨ane.symm, aninΔ⟩
    let A'lc := A'ki.TypeVarLocallyClosed_of
    let B'lc := A'cd.preserve_lc Δawf A'lc
    apply TypeVarLocallyClosed.TypeVar_close_inc (a := a) at A'lc
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact TypeVar_open_swap A'cd A'lc B'lc aninA' Δa'awf
  | .arr A' B', .arr A'ki B'ki =>
    let ⟨_, A'cd⟩ := total A'ki Δwf
    let ⟨_, B'cd⟩ := total B'ki Δwf
    exact ⟨_, .arr A'cd B'cd⟩
  | .list A's, Aki =>
    rw [← Range.map_get!_eq (as := A's)] at *
    rcases Aki.inv_list' with ⟨_, rfl, A'ki⟩
    let ⟨A'', A'cd⟩ := Range.skolem (fun i mem => total (A'ki i mem) Δwf)
    exact ⟨_, list A'cd⟩
  | .listApp A' B', .listApp A'ki B'ki =>
    let ⟨A'', A'cd⟩ := total A'ki Δwf
    let ⟨B'', B'cd⟩ := total B'ki Δwf
    by_cases ∃ K', A' = [[λ a : K'. a$0]]
    · case pos h =>
      rcases h with ⟨K', rfl⟩
      let .lam .. := A'ki
      exact ⟨_, listAppId B'ki B'cd⟩
    · case neg ne =>
      by_cases ∃ B''' n, B' = [[{</ B'''@i // i in [:n] />}]]
      · case pos h =>
        rcases h with ⟨B''', n, rfl⟩
        rcases B'cd.list_inversion with ⟨_, rfl, B'cd'⟩
        exact ⟨_, listAppList (not_exists.mp ne) A'cd B'cd'⟩
      · case neg ne' =>
        exact ⟨_, listApp (not_exists.mp ne) (not_exists.mp <| not_exists.mp ne' ·) A'cd B'cd⟩
  | .prod A', .prod A'ki =>
    let ⟨_, A'cd⟩ := total A'ki Δwf
    exact ⟨_, .prod A'cd⟩
  | .sum A', .sum A'ki =>
    let ⟨_, A'cd⟩ := total A'ki Δwf
    exact ⟨_, .sum A'cd⟩
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · rename A' = _ => eq
    cases eq
    simp_arith
  · apply Nat.le_of_lt
    apply List.sizeOf_lt_of_mem
    rw [List.getElem?_eq_getElem mem.upper, Option.getD]
    exact List.getElem_mem mem.upper

end CompleteDevelopment

theorem ParallelReduction.diamond (Δwf : [[⊢ Δ]]) (prB : [[Δ ⊢ A ≡> B]]) (prC : [[Δ ⊢ A ≡> C]])
  (Aki : [[Δ ⊢ A : K]])
  : ∃ T, [[Δ ⊢ B ≡> T]] ∧ [[Δ ⊢ C ≡> T]] ∧ T.TypeVarLocallyClosed := by
  let ⟨T, Acd⟩ := CompleteDevelopment.total Aki Δwf
  let Alc := Aki.TypeVarLocallyClosed_of
  let Bpr := Acd.ParallelReduction_close prB Δwf Alc
  exact ⟨_, Bpr, Acd.ParallelReduction_close prC Δwf Alc, Bpr.preserve_lc <| prB.preserve_lc Alc⟩

namespace MultiParallelReduction
@[elab_as_elim]
def rec_one {Δ: Environment} {motive: ∀A B, [[ Δ ⊢ A ≡>* B ]] → Prop}
  (base: ∀ {A B}(red: [[ Δ ⊢ A ≡> B ]]), motive A B (.step red .refl))
  (step: ∀ {A B C}(red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ ⊢ B ≡>* C ]]), motive B C red2 → motive A C (.step red1 red2))
  {A B} (red: [[ Δ ⊢ A ≡>* B ]]): motive A B red := by
  induction red
  . case refl A => exact base .refl
  . case step A B C red1 red2 ih => exact step red1 red2 ih

-- Preservation of shapes under reduction
theorem preserve_shape_arr (mred: [[ Δ ⊢ (A → B) ≡>* T ]]): ∃ A' B', T = [[(A' → B')]] ∧ [[ Δ ⊢ A ≡>* A' ]] ∧ [[ Δ ⊢ B ≡>* B' ]] :=
by
  generalize AarrBeq : [[(A → B)]] = AarrB at mred
  induction mred generalizing A B
  . case refl => aesop (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    subst AarrBeq
    have := red.inv_arr
    aesop (rule_sets := [pred])

theorem preserve_shape_forall (mred: [[ Δ ⊢ (∀ a? : K. A) ≡>* T ]]): ∃ A', T = [[∀ a? : K. A']] ∧ (∃I, ∀a ∉ (I: List _), [[ Δ, a : K ⊢ A^a ≡>* A'^a ]]) :=
by
  generalize LamAeq : [[(∀ a : K. A)]] = LamA at mred
  induction mred generalizing A
  . case refl => aesop (add unsafe tactic guessI) (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    subst LamAeq
    have ⟨A', eqT2, I, AA'⟩ := red.inv_forall
    have ⟨A'', ih⟩ := ih eqT2.symm
    exists A''
    aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem preserve_shape_prod (mred: [[ Δ ⊢ ⊗A ≡>* T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ≡>* A' ]] :=
by
  generalize ProdAeq : [[(⊗A)]] = ProdA at mred
  induction mred generalizing A
  . case refl => aesop (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    subst ProdAeq
    have := red.inv_prod
    aesop (rule_sets := [pred])

theorem preserve_shape_sum (mred: [[ Δ ⊢ ⊕A ≡>* T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ≡>* A' ]] :=
by
  generalize SumAeq : [[(⊕A)]] = SumA at mred
  induction mred generalizing A
  . case refl => aesop (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    subst SumAeq
    have := red.inv_sum
    aesop (rule_sets := [pred])

theorem preserve_shape_list (mred: [[ Δ ⊢ { </ A@i // i in [:n] /> } ≡>* T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ Δ ⊢ A@i ≡>* B@i // i in [:n] /> ]] :=
by
  generalize ListAeq : [[{ </ A@i // i in [:n] /> }]] = ListA at mred
  induction mred generalizing A
  . case refl => aesop (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    subst ListAeq
    have ⟨B, eqT2, AB⟩ := red.inv_list
    have ⟨B', ih⟩ := ih eqT2.symm
    exists B'
    aesop (rule_sets := [pred])

theorem confluence_on_the_left (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ A ≡> C ]]) (wf: [[ ⊢ Δ ]])  (Aki : [[Δ ⊢ A : K]])
  : ∃ T, [[ Δ ⊢ B ≡>* T ]] ∧ [[ Δ ⊢ C ≡>* T ]] ∧ T.TypeVarLocallyClosed := by
  induction red1 generalizing C
  . case refl A =>
    exists C
    exact ⟨red2.Multi_of, ⟨.refl, red2.preserve_lc Aki.TypeVarLocallyClosed_of⟩⟩
  . case step A B B' red1 red1' ih =>
    have ⟨T1, redBT1, redCT1, lcT1⟩ := ParallelReduction.diamond wf red1 red2 Aki
    have ⟨T2, redB'T2, redT1T2, lcT2⟩ := ih redBT1 (red1.preservation wf Aki)
    exists T2
    exact ⟨redB'T2, .step redCT1 redT1T2, lcT2⟩

theorem trans (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ B ≡>* C ]]): [[ Δ ⊢ A ≡>* C ]] := by
  induction red1 generalizing C <;> aesop (add unsafe constructors MultiParallelReduction)

theorem preserve_lc  (red: [[ Δ ⊢ A ≡>* B ]]) (lc: A.TypeVarLocallyClosed): B.TypeVarLocallyClosed := by
  induction red <;> aesop (add unsafe ParallelReduction.preserve_lc)

theorem confluence (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ A ≡>* C ]]) (wf: [[ ⊢ Δ ]]) (Aki : [[Δ ⊢ A : K]])
  : ∃ T, [[ Δ ⊢ B ≡>* T ]] ∧ [[ Δ ⊢ C ≡>* T ]] ∧ T.TypeVarLocallyClosed := by
  induction red2 generalizing B
  . case refl A =>
    exists B
    exact ⟨.refl,red1, red1.preserve_lc Aki.TypeVarLocallyClosed_of⟩
  . case step A C C' red2 red2' ih =>
    have ⟨T1, redBT1, redCT1, lcT1⟩ := red1.confluence_on_the_left red2 wf Aki
    have ⟨T2, redT1T2, redC'T2, lcT2⟩ := ih redCT1 (red2.preservation wf Aki)
    exists T2
    exact ⟨redBT1.trans redT1T2, redC'T2, lcT2⟩

theorem common_reduct (red: [[ Δ ⊢ A ≡>* B ]]) (wf: [[ ⊢ Δ ]]) (Aki : [[Δ ⊢ A : K]])
  : exists C, [[ Δ ⊢ A ≡>* C ]] ∧ [[ Δ ⊢ B ≡>* C ]] ∧ C.TypeVarLocallyClosed :=
  refl |>.confluence red wf Aki

end MultiParallelReduction

namespace EqParallelReduction

theorem weakening (red: [[ Δ, Δ'' ⊢ A <≡>* B ]]) (wfτ: [[ ⊢τ Δ, Δ', Δ'' ]]) : [[ Δ, Δ', Δ'' ⊢ A <≡>* B ]] := by
  induction red with
  | refl => exact .refl
  | step AB => exact .step (AB.weakening' wfτ)
  | sym _ ih => exact ih.sym
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem subst_out' {A T T' : «Type»} (red : [[ Δ, a: K, Δ' ⊢ T <≡>* T' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] <≡>* T'[A/a] ]] := by
  induction red with
  | refl => exact .refl
  | step AB => exact .step (AB.subst_out' wf kindA)
  | sym _ ih => exact ih.sym
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem preserve_lc (red: [[ Δ ⊢ A <≡>* B ]]): (A.TypeVarLocallyClosed → B.TypeVarLocallyClosed) ∧ (B.TypeVarLocallyClosed → A.TypeVarLocallyClosed) := by
  induction red <;> try aesop (add unsafe ParallelReduction.preserve_lc); done
  . case step A B eAB => exact ⟨eAB.preserve_lc, eAB.preserve_lc_rev⟩

theorem common_reduct (eAB: [[ Δ ⊢ A <≡>* B ]]) (wf: [[ ⊢ Δ ]]) (Aki : [[Δ ⊢ A : K]])
  (Bki : [[Δ ⊢ B : K]]) : ∃ C, [[ Δ ⊢ A ≡>* C ]] ∧ [[ Δ ⊢ B ≡>* C ]] := by
  induction eAB
  . case refl A => exact ⟨A, .refl, .refl⟩
  . case step A B AB => exact ⟨B, AB.Multi_of, .refl⟩
  . case sym B A mBA ih =>
    obtain ⟨C, mBC, mAC⟩ := ih Bki Aki
    exact ⟨C, mAC, mBC⟩
  . case trans A A' B eAA' eA'B ih1 ih2 =>
    obtain ⟨C, mAC, mA'C⟩ := ih1 Aki sorry
    obtain ⟨C', mA'C', mBC'⟩ := ih2 sorry Bki
    have ⟨T, mCT, mC'T, _⟩ := mA'C.confluence mA'C' wf sorry (K := K)
    exact ⟨T, mAC.trans mCT, mBC'.trans mC'T⟩

-- Injectivity of Type Constructors.
theorem inj_arr (ered: [[ Δ ⊢ (A → B) <≡>* (A' → B') ]]) (wf: [[ ⊢ Δ ]]) (ABlc: [[ A → B ]].TypeVarLocallyClosed): [[ Δ ⊢ A <≡>* A' ]] ∧ [[ Δ ⊢ B <≡>* B' ]] := by
  have ⟨T, AB_T, A'B'_T⟩ := ered.common_reduct wf ABlc (ered.preserve_lc.1 ABlc)
  have ⟨A1, B1, Teq1, AA1, BB1⟩:= AB_T.preserve_shape_arr
  have ⟨A2, B2, Teq2, A'A2, B'B2⟩ := A'B'_T.preserve_shape_arr
  subst T; cases Teq2; case refl =>
  exact ⟨AA1.Equiv_of.trans A'A2.Equiv_of.sym, BB1.Equiv_of.trans B'B2.Equiv_of.sym⟩

theorem inj_forall (ered: [[ Δ ⊢ (∀ a? : K. A) <≡>* (∀ a? : K'. A') ]]) (wf: [[ ⊢ Δ ]]) (Alc: [[ (∀ a : K. A) ]].TypeVarLocallyClosed): K = K' ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a: K ⊢ A^a <≡>* A'^a ]] := by
  have ⟨T, AT, A'T⟩ := ered.common_reduct wf Alc (ered.preserve_lc.1 Alc)
  have ⟨A1, Teq1, I1, AA1⟩:= AT.preserve_shape_forall
  have ⟨A2, Teq2, I2, A'A2⟩ := A'T.preserve_shape_forall
  subst T; cases Teq2; case refl =>
  exact ⟨rfl, I1 ++ I2, λa nin => AA1 a (by simp_all) |>.Equiv_of.trans <| A'A2 a (by simp_all) |>.Equiv_of.sym⟩

theorem inj_prod (ered: [[ Δ ⊢ ⊗A <≡>* ⊗A' ]]) (wf: [[ ⊢ Δ ]]) (Alc: [[ ⊗A ]].TypeVarLocallyClosed): [[ Δ ⊢ A <≡>* A' ]] := by
  have ⟨T, AT, A'T⟩ := ered.common_reduct wf Alc (ered.preserve_lc.1 Alc)
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_prod
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_prod
  subst T; cases Teq2; case refl =>
  exact AA1.Equiv_of.trans A'A2.Equiv_of.sym

theorem inj_sum (ered: [[ Δ ⊢ ⊕A <≡>* ⊕A' ]]) (wf: [[ ⊢ Δ ]]) (Alc: [[ ⊕A ]].TypeVarLocallyClosed): [[ Δ ⊢ A <≡>* A' ]] := by
  have ⟨T, AT, A'T⟩ := ered.common_reduct wf Alc (ered.preserve_lc.1 Alc)
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_sum
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_sum
  subst T; cases Teq2; case refl =>
  exact AA1.Equiv_of.trans A'A2.Equiv_of.sym

theorem inj_list (mred: [[ Δ ⊢ { </ A@i // i in [:n] /> } <≡>* { </ B@i // i in [:n'] /> } ]]) (wf: [[ ⊢ Δ ]]) (Alc: [[ { </ A@i // i in [:n] /> } ]].TypeVarLocallyClosed): n = n' ∧ [[ </ Δ ⊢ A@i <≡>* B@i // i in [:n] /> ]] := by
  have ⟨T, AT, BT⟩ := mred.common_reduct wf Alc (mred.preserve_lc.1 Alc)
  have ⟨A1, Teq1, AA1⟩ := AT.preserve_shape_list
  have ⟨B1, Teq2, BB1⟩ := BT.preserve_shape_list
  subst T
  injection Teq2 with eq
  have eqn'n := Std.Range.length_eq_of_mem_eq eq; subst eqn'n
  have eqBA := Std.Range.eq_of_mem_of_map_eq eq; clear eq
  simp_all
  exact λ x xin => AA1 x xin |>.Equiv_of.trans <| BB1 x xin |>.Equiv_of.sym

end EqParallelReduction

end TabularTypeInterpreter.«F⊗⊕ω»
