import Mathlib.Tactic
import TabularTypeInterpreter.Data.Range
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Kinding

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace ParallelReduction

local instance : Inhabited «Type» where
  default := .list []
in
def list' (As Bs: List «Type») (length_eq: As.length = Bs.length) (red: ∀A B, ⟨A, B⟩ ∈ (As.zip Bs) → [[ Δ ⊢ A ≡> B ]]): ParallelReduction Δ (Type.list As) (Type.list Bs) := by
  rw [← Std.Range.map_get!_eq (as := As), ← Std.Range.map_get!_eq (as := Bs), ← length_eq,
      Std.Range.map, Std.Range.map, ← List.map_singleton_flatten, ← Std.Range.map,
      ← List.map_singleton_flatten, ← Std.Range.map]
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
def lamListApp' (A A' : «Type») (Bs B's : List «Type») (length_eq: Bs.length = B's.length)
  (kind: ∀B ∈ Bs, [[ Δ ⊢ B : K ]])
  (redA: ∀a ∉ (I: List _), [[ Δ, a : K ⊢ A^a ≡> A'^a ]])
  (redB: ∀B B', ⟨B, B'⟩ ∈ (Bs.zip B's) → [[ Δ ⊢ B ≡> B' ]])
  : ParallelReduction Δ ((Type.lam K A).listApp (Type.list Bs)) (Type.list <| B's.map fun B' => A'.Type_open B') := by
    rw [← Std.Range.map_get!_eq (as := Bs), ← Std.Range.map_f_get!_eq (as := B's) (f := fun B' => A'.Type_open B'), <- length_eq,
      Std.Range.map, Std.Range.map, ← List.map_singleton_flatten, ← Std.Range.map,
      ← List.map_singleton_flatten, ← Std.Range.map]
    apply lamListApp (I := I)
    . intro i mem
      apply kind
      exact List.get!_mem mem.upper
    . exact redA
    . intro i mem
      apply redB
      have := (Bs.zip B's).get!_mem <| by
        rw [List.length_zip, ← length_eq, Nat.min_self]
        exact mem.upper
      rw [List.get!_zip length_eq mem.upper] at this
      exact this


theorem inv_lam : ∀I: List _, [[ Δ ⊢ (λ a? : K. A) ≡> T ]] → ∃ a A', a ∉ I ∧ T = [[λ a : K. A']] ∧ [[ Δ, a : K ⊢ A^a ≡> A'^a ]] := by
  intro I red
  cases red
  . case refl =>
    have ⟨a, notInI⟩ := I.exists_fresh
    exists a, A
    aesop (rule_sets := [pred])
  . case lam I' A' red =>
    have ⟨a, notInI⟩ := (I ++ I').exists_fresh
    exists a, A'
    constructor <;> aesop

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
  . case lamListApp n Δ B K I A A' B' kinding redA redB ihA' ihB' =>
    intro as i inRange _
    obtain ⟨notInAfv, notInBfv⟩ := notInFV
    apply not_mem_freeTypeVars_Type_open_intro
    . have ⟨a', notInI⟩ := (I ++ A'.freeTypeVars).exists_fresh
      by_cases a = a'
      . case pos eq => simp_all
      . case neg neq =>
        specialize ihA' a' (by simp_all) a (not_mem_freeTypeVars_TypeVar_open_intro notInAfv (by simp_all))
        exact not_mem_freeTypeVars_TypeVar_open_drop ihA'
    . simp_all [Std.Range.mem_of_mem_toList]
  . case lam I Δ K A B red ih =>
    have ⟨a', notInI⟩ := (a :: I).exists_fresh
    have ih' := @ih a' (by simp_all) a (by apply not_mem_freeTypeVars_TypeVar_open_intro <;> aesop)
    exact not_mem_freeTypeVars_TypeVar_open_drop ih'
  . case scheme I Δ K A B red ih =>
    have ⟨a', notInI⟩ := (a :: I).exists_fresh
    have ih' := ih a' (by aesop) a (by apply not_mem_freeTypeVars_TypeVar_open_intro <;> aesop)
    exact not_mem_freeTypeVars_TypeVar_open_drop ih'
  . case list n Δ A B red ih =>
    intro as i inRange _
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
  case lamListApp n Δ B K I A A' B' kindB redA redB ihA ihB =>
    intro lcAB
    simp_all
    cases lcAB; case listApp lcA lcB =>
    cases lcA; case lam lcA =>
    have lcA' := lcA.modus_ponens_open ihA
    cases lcB; case list lcB =>
    constructor
    simp_all
    intro _ i In _
    apply Type_open_dec <;> simp_all [Std.Range.mem_of_mem_toList]
  all_goals
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

theorem weakening_type' (red: [[ Δ, Δ' ⊢ A ≡> B ]]) (freshΔ: a ∉ Δ.typeVarDom) : [[ Δ, a: K, Δ' ⊢ A ≡> B ]] := by
  generalize Δ_eq : Δ.append Δ' = Δ_ at red
  induction red generalizing Δ Δ' <;> try (aesop (add norm Type.freeTypeVars) (add safe constructors ParallelReduction); done)
  . case lamApp Δ_ B K' I A A' B' kindB redA redB ihA ihB =>
    subst Δ_
    apply ParallelReduction.lamApp (I := a :: I ++ A.freeTypeVars)
    . rw [<- Environment.append_type_assoc]; apply Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) kindB
    . intro a' notIn
      specialize @ihA a' (by simp_all) Δ (Δ'.typeExt a' K')
      simp_all [Environment.append]
    . specialize @ihB Δ Δ'; simp_all
  . case lamListApp n Δ_ B K' I A A' B' kindB redA redB ihA ihB =>
    subst Δ_
    apply ParallelReduction.lamListApp (I := a :: I ++ A.freeTypeVars)
    . rw [<- Environment.append_type_assoc]
      intros n In
      apply Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) (kindB n In)
    . intro a' notIn
      specialize @ihA a' (by simp_all) Δ (Δ'.typeExt a' K')
      simp_all [Environment.append]
    . intros n In
      specialize @ihB n In Δ Δ'; simp_all
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
  . case lamListApp n Δ_ B K' I A A' B' kindB redA redB ihA ihB =>
    subst Δ_
    apply ParallelReduction.lamListApp (I := x :: I)
    . rw [<- Environment.append_term_assoc]
      intro i In
      apply Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) (kindB i In)
    . intro x' notIn
      specialize @ihA x' (by simp_all) Δ (Δ'.typeExt x' K') (by aesop)
      simp_all [Environment.append]
    . intro i notIn
      specialize @ihB i notIn Δ Δ'; simp_all
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

-- NOTE a weaker version (replacing wf with ∀a ∈, ∉ ...) should also be provable, but this requries a "kind only" wf
-- NOTE using this weaker wf we can remove subst on Δ' for pred_subst theorems
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
    rw [<- Type.subst_open_var (neq := by aesop) (lc := lcA)]
    rw [<- Type.subst_open_var (neq := by aesop) (lc := red.preserve_lc lcA)]
    obtain red := weakening_type (a := a') (K := K) (red := red) (freshΔ := by simp_all)
    simp_all
  . case «forall» I K T lc ih =>
    apply ParallelReduction.scheme (I := a :: I ++ A.freeTypeVars ++ Δ.typeVarDom)
    intro a' notIn
    rw [<- Type.subst_open_var (neq := by aesop) (lc := lcA)]
    rw [<- Type.subst_open_var (neq := by aesop) (lc := red.preserve_lc lcA)]
    obtain red := weakening_type (a := a') (K := K) (red := red) (freshΔ := by simp_all)
    simp_all
  . case list Tl lc ih =>
    apply ParallelReduction.list' (length_eq := by simp_all [List.length_map])
    simp_all [List.zip]
    aesop

-- NOTE this is also provable: no subst on Δ' is needed
theorem subst_out2 {A T T' : «Type»} (wf: [[ ⊢ Δ, a: K, Δ' ]]) (red : [[ Δ, a: K, Δ' ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ' ⊢ T[A/a] ≡> T'[A/a] ]] := by sorry

theorem subst_out' {A T T' : «Type»} (wf: [[ ⊢ Δ, a: K, Δ' ]]) (red : [[ Δ, a: K, Δ' ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡> T'[A/a] ]] := by
  generalize Δ_eq: (Δ.typeExt a K |>.append Δ') = Δ_ at red
  induction red generalizing Δ Δ' <;> (try simp_all [Type.TypeVar_subst]) <;> try (aesop (rule_sets := [pred]); done)
  . case lamApp Δ_ T2 K' I T1 T1' T2' kindT2 redT1 redT2 ihT1 ihT2 =>
    subst Δ_
    rw [kindA.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist]
    apply ParallelReduction.lamApp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    . apply Kinding.subst' (K := K) <;> simp_all
    . intro a' notIn
      repeat rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
      rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
      apply ihT1 <;> simp_all [Environment.append]
      . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    . simp_all
  . case lamListApp n Δ_ T2 K' I T1 T1' T2' kindT2 redT1 redT2 ihT1 ihT2 =>
    subst Δ_
    unfold Function.comp
    simp
    -- TODO bruhhh
    have := funext <| λx => congrArg (λa => [a]) (kindA.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist (a := a) (n := 0) (A := T1') (B := T2' x) (B' := A) )
    rw [this]
    apply ParallelReduction.lamListApp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    . intro i mem
      apply Kinding.subst' (K := K) <;> simp_all
    . intro a' notIn
      repeat rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
      rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
      apply ihT1 <;> simp_all [Environment.append]
      . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    . simp_all
  . case lam I Δ_ K' T T' red ih =>
    subst Δ_
    apply ParallelReduction.lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    repeat rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
  . case scheme I Δ_ K' T T' red ih =>
    subst Δ_
    apply ParallelReduction.scheme (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    repeat rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]

theorem subst_out {A T T' : «Type»} (wf: [[ ⊢ Δ, a: K ]]) (red : [[ Δ, a: K ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ ⊢ T[A/a] ≡> T'[A/a] ]] := by
  apply subst_out' (Δ' := Environment.empty) <;> assumption

set_option maxHeartbeats 400000 in  -- bruh
theorem subst_all' {A B T: «Type»} (wf: [[ ⊢ Δ, a: K, Δ' ]]) (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ, a: K, Δ' ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) (lcT: T.TypeVarLocallyClosed): [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡> T'[B/a] ]] := by
  generalize Δ_eq: (Δ.typeExt a K |>.append Δ') = Δ_ at red2
  induction red2 generalizing Δ Δ' A B
  . case refl Δ_ T_ =>
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
      rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
      rw [<- Type.subst_open_var (neq := by aesop) (lc := (red1.preserve_lc kindA.TypeVarLocallyClosed_of))]
      rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
      apply ihT1 <;> simp_all [Environment.append]
      . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
      . aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
    . apply ihT2 <;> simp_all [Environment.append]
      aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
  . case lamListApp n Δ_ T2 K2 I T1 T1' T2' kindT2 redT1 redT2 ihT1 ihT2 =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    unfold Function.comp
    simp
    have := funext <| λx => congrArg (λa => [a]) (red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.Type_open_TypeVar_subst_dist (a := a) (n := 0) (A := T1') (B := T2' x) (B' := B))
    rw [this]
    apply ParallelReduction.lamListApp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    . intros i mem
      apply Kinding.subst' (K := K) <;> simp_all
    . case a =>
      intro a' notIn
      rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
      rw [<- Type.subst_open_var (neq := by aesop) (lc := (red1.preserve_lc kindA.TypeVarLocallyClosed_of))]
      rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
      apply ihT1 <;> simp_all [Environment.append]
      . constructor <;> simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
      . aesop (add safe Type.TypeVarLocallyClosed.strengthen, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
    . intros i mem
      apply ihT2 <;> simp_all [Environment.append]
      simp [List.map_singleton_flatten] at lcT
      aesop (add safe Type.TypeVarLocallyClosed.strengthen, safe forward Std.Range.mem_toList_of_mem, safe List.mem_map_of_mem, norm Environment.TypeVarNotInDom, norm Environment.TypeVarInDom, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })
  . case lam I Δ_ K' T T' redT ih =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    apply ParallelReduction.lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
    rw [<- Type.subst_open_var (neq := by aesop) (lc := (red1.preserve_lc kindA.TypeVarLocallyClosed_of))]
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
    rw [<- Type.subst_open_var (neq := by aesop) (lc := kindA.TypeVarLocallyClosed_of)]
    rw [<- Type.subst_open_var (neq := by aesop) (lc := (red1.preserve_lc kindA.TypeVarLocallyClosed_of))]
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

theorem preservation (lc: A.TypeVarLocallyClosed) (wf: [[ ⊢ Δ ]]) (red: [[ Δ ⊢ A ≡> B ]]) (k: [[ Δ ⊢ A: K ]]): [[ Δ ⊢ B: K ]] := by
  induction red generalizing K
  case refl => simp_all
  case lamApp Δ B KB I A A' B' kindB redA redB ihA ihB =>
    cases k; case app _ _ k =>
    cases k; case lam I' _ kindA =>
    have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ Δ.typeVarDom).exists_fresh
    have wf': [[ ⊢ Δ, a: KB ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    cases lc
    case app lcA lcB =>
    cases lcA
    case lam lcA =>
    have kindA' := ihA a (by aesop) (Type.TypeVarLocallyClosed.strengthen lcA) wf' (kindA a (by aesop))
    have kindB' := ihB lcB wf kindB
    rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a:=a) (by aesop)]
    have lcB' := redB.preserve_lc lcB
    apply Kinding.subst <;> assumption
  case lamListApp n Δ B KB I A A' B' kindB redA redB ihA ihB =>
    cases k; case listApp _ K k _ =>
    constructor; case a =>
    intro i mem; simp_all
    cases k; case lam I' _ kindA =>
    have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ Δ.typeVarDom).exists_fresh
    have wf': [[ ⊢ Δ, a: KB ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    cases lc; case listApp lcA lcB =>
    cases lcA; case lam lcA =>
    have kindA' := ihA a (by aesop) (Type.TypeVarLocallyClosed.strengthen lcA) wf' (kindA a (by aesop))
    cases lcB; case list lcB =>
    have kindB' := ihB i mem (lcB (B i) (by
      aesop (add safe forward Std.Range.mem_toList_of_mem) (config := { useSimpAll := false })
    )) (kindB i mem)
    rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a:=a) (by aesop)]
    apply Kinding.subst <;> assumption
  case lam I Δ K1 A B red ih =>
    cases k; case lam K2 I' kindA =>
    apply Kinding.lam (I := I ++ I' ++ Δ.typeVarDom)
    intro a notIn
    have wf': [[ ⊢ Δ, a: K1 ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    cases lc
    case lam lc =>
    obtain lc := lc.strengthen (a := a)
    simp_all
  case scheme I Δ K1 A B red ih =>
    cases k; case scheme I' kindA =>
    apply Kinding.scheme (I := I ++ I' ++ Δ.typeVarDom)
    intro a notIn
    have wf': [[ ⊢ Δ, a: K1 ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
    cases lc
    case «forall» lc =>
    obtain lc := lc.strengthen (a := a)
    simp_all
  case list n Δ_ A B red ih =>
    have ⟨K_, eqK_, k'⟩ := k.inv_list'; subst K
    constructor; aesop (add safe forward Std.Range.mem_toList_of_mem, safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed)
  all_goals cases k; constructor <;> aesop (add safe Type.TypeVarLocallyClosed, unsafe cases Type.TypeVarLocallyClosed) (config := { enableSimp := false })

-- NOTE critical

theorem diamond : [[ ⊢ Δ ]] → [[ Δ ⊢ A ≡> B ]] -> [[ Δ ⊢ A ≡> C ]] -> A.TypeVarLocallyClosed -> ∃ T, [[ Δ ⊢ B ≡> T ]] ∧ [[ Δ ⊢ C ≡> T ]] ∧ T.TypeVarLocallyClosed := by
  intro wf red1
  revert C
  induction red1
  case lam I Δ' K A' B' red1 ih =>
    clear Δ A B
    intro C red2 lcA

    -- NOTE alternatively, lc_abs_iff_body
    cases lcA
    case lam lcA =>

    have ⟨a, C', notIn, eqC, red2'⟩ := ParallelReduction.inv_lam (I ++ A'.freeTypeVars ++ B'.freeTypeVars ++ C.freeTypeVars ++ Δ'.typeVarDom) red2
    subst C
    have freshC' : a ∉ C'.freeTypeVars := by
      apply preserve_not_mem_freeTypeVars  at red2
      simp_all [«Type».freeTypeVars]
    have wf' : [[ ⊢ Δ', a: K ]] := by
      constructor
      . assumption
      . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop

    have ⟨T', predA, predB, lcT'⟩ := ih a (by aesop) wf' red2' (lcA.strengthen (a := a)); clear ih

    rw [<- Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id (A:=T') (a:=a)] at predA predB <;> try assumption

    exists («Type».lam K (T'.TypeVar_close a))

    constructor
    . apply (lam_intro_ex a) <;> simp_all [Type.not_mem_freeTypeVars_TypeVar_close ]
    . constructor
      . apply (lam_intro_ex a) <;> simp_all [Type.not_mem_freeTypeVars_TypeVar_close ]
      . constructor
        apply Type.TypeVarLocallyClosed.TypeVar_close_inc
        assumption
  case lamApp Δ' B_ K I A_ A' B' k redA redB ihA ihB =>
    clear A B Δ
    rename' A_ => A, B_ => B, Δ' => Δ

    intro C redAB lcAB

    cases lcAB
    case app lcA lcB =>
    cases lcA
    case lam lcA =>
    have lcA_a := λa => lcA.strengthen (a := a)
    have lcA': A'.TypeVarLocallyClosed 1 := by
      have ⟨a, notIn⟩ := (I ++ A'.freeTypeVars).exists_fresh
      obtain lcA := lcA.strengthen (a := a)
      apply redA a (by simp_all) |>.preserve_lc at lcA
      apply Type.TypeVarLocallyClosed.TypeVar_close_inc (a := a) at lcA
      rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at lcA
      assumption
    simp_all
    cases redAB
    . case refl =>
      exists (A'.Type_open B')
      repeat' apply And.intro
      . constructor
      . apply ParallelReduction.lamApp (I:=I) <;> try simp_all
      . apply redB.preserve_lc at lcB
        simp_all [Type.TypeVarLocallyClosed.Type_open_dec]
    . case lamApp I' A2 B2 redA' redB' _ =>
      have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ A2.freeTypeVars ++ Δ.typeVarDom ++ B'.freeTypeVars).exists_fresh
      have wf' : [[ ⊢ Δ, a: K ]] := by
        constructor
        . assumption
        . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
      specialize redA' a (by simp_all)
      have ⟨T1, redA'T, redA2T, lcT1⟩ := ihA a (by simp_all) wf' redA'
      have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'
      exists T1.TypeVar_subst a T2
      repeat' apply And.intro
      . rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
        apply subst_all <;> try assumption
        . apply preservation (red := redB) <;> simp_all
        . apply (redA _ (by simp_all) |>.preserve_lc); simp_all
      . rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
        apply subst_all <;> try assumption
        . apply preservation (red := redB') <;> simp_all
        . apply redA'.preserve_lc; simp_all
      . apply Type.TypeVarLocallyClosed.TypeVar_subst <;> assumption
    . case app A2 B2 redA' redB' =>
      cases redA'
      . case refl =>
        have ⟨a, notInI⟩ := (I ++ A.freeTypeVars ++ A'.freeTypeVars ++ Δ.typeVarDom).exists_fresh
        have wf' : [[ ⊢ Δ, a: K ]] := by
          constructor
          . assumption
          . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
        specialize redA a (by simp_all)
        have ⟨T1, redA'T, _, lcT1⟩ := ihA a (by simp_all) wf' redA
        have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'

        rw [<- Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id (A:=T1) (a:=a)] at redA'T <;> try assumption
        exists A'.Type_open T2
        repeat' apply And.intro
        . rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
          rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
          apply subst_in <;> try assumption
          . apply redB.preserve_lc; simp_all
          . apply redA.preserve_lc; simp_all
        . apply (lamApp_intro_ex a) <;> try (simp_all; done)
          . apply preservation (red := redB') <;> simp_all
        . apply redB.preserve_lc at lcB
          simp_all [Type.TypeVarLocallyClosed.Type_open_dec]
      . case lam I' B22 redA' =>
        have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ B22.freeTypeVars ++ Δ.typeVarDom).exists_fresh
        have wf' : [[ ⊢ Δ, a: K ]] := by
          constructor
          . assumption
          . simp [Environment.TypeVarNotInDom, Environment.TypeVarInDom]; aesop
        specialize redA' a (by simp_all)
        have ⟨T1, redA'T, redA2T, lcT1⟩ := ihA a (by simp_all) wf' redA'
        have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'

        rw [<- Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id (A:=T1) (a:=a)] at redA'T redA2T <;> try assumption
        exists (T1.TypeVar_close a).Type_open T2
        repeat' apply And.intro
        . rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
          rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (Type.not_mem_freeTypeVars_TypeVar_close )]
          apply subst_all <;> try assumption
          . apply preservation (red := redB) <;> simp_all
          . apply redA _ (by simp_all) |>.preserve_lc; simp_all
        . apply (lamApp_intro_ex a) <;> try (simp_all; done)
          . simp_all [Type.not_mem_freeTypeVars_TypeVar_close ]
          . apply preservation (red := redB') <;> simp_all
        . simp_all [Type.TypeVarLocallyClosed.Type_open_dec, Type.TypeVarLocallyClosed.TypeVar_close_inc]
  all_goals sorry

end ParallelReduction

namespace MultiParallelReduction
@[elab_as_elim]
def rec_one {Δ: Environment} {motive: ∀A B, [[ Δ ⊢ A ≡>* B ]] → Prop}
  (base: ∀ {A B}(red: [[ Δ ⊢ A ≡> B ]]), motive A B (.step red .refl))
  (step: ∀ {A B C}(red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ ⊢ B ≡>* C ]]), motive B C red2 → motive A C (.step red1 red2))
  {A B} (red: [[ Δ ⊢ A ≡>* B ]]): motive A B red := by
  induction red
  . case refl A => exact base .refl
  . case step A B C red1 red2 ih => exact step red1 red2 ih

theorem inv_arr: [[ Δ ⊢ (A → B) ≡>* T ]] → (∃ A' B', T = [[(A' → B')]] ∧ [[ Δ ⊢ A ≡>* A' ]] ∧ [[ Δ ⊢ B ≡>* B' ]]) :=
by
  intro mred
  generalize AarrBeq : [[(A → B)]] = AarrB at mred
  revert A B
  induction mred
  . case refl => aesop (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    intro A B AarrBeq
    subst AarrBeq
    cases red <;> aesop (rule_sets := [pred])

-- TODO check why it's different from ParallelReduction.inv_lam
theorem inv_typeLam: [[ Δ ⊢ (∀ a : K. A) ≡>* T ]] → (∃ A', T = [[∀ a : K. A']] ∧ (∃I, ∀a ∉ (I: List _), [[ Δ, a : K ⊢ A^a ≡>* A'^a ]])) :=
by
  intro mred
  generalize LamAeq : [[(∀ a : K. A)]] = LamA at mred
  revert A
  induction mred
  . case refl => aesop (add unsafe tactic guessI) (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    intro A LamAeq
    subst LamAeq
    cases red <;> aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem inv_prodIntro: [[ Δ ⊢ ⊗A ≡>* T ]] → (∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ≡>* A' ]]) :=
by
  intro mred
  generalize LamAeq : [[(⊗A)]] = ProdA at mred
  revert A
  induction mred
  . case refl => aesop (add unsafe tactic guessI) (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    intro A LamAeq
    subst LamAeq
    cases red <;> aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem inv_sumIntro: [[ Δ ⊢ ⊕A ≡>* T ]] → (∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ≡>* A' ]]) :=
by
  intro mred
  generalize LamAeq : [[(⊕A)]] = SumA at mred
  revert A
  induction mred
  . case refl => aesop (add unsafe tactic guessI) (rule_sets := [pred])
  . case step T1 T2 T3 red mred ih =>
    intro A LamAeq
    subst LamAeq
    cases red <;> aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem confluence_on_the_left (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ A ≡> C ]]) (wf: [[ ⊢ Δ ]])  (lc: A.TypeVarLocallyClosed): ∃ T, [[ Δ ⊢ B ≡>* T ]] ∧ [[ Δ ⊢ C ≡>* T ]] ∧ T.TypeVarLocallyClosed := by
  induction red1 generalizing C
  . case refl A =>
    exists C
    exact ⟨.step red2 .refl, ⟨.refl, red2.preserve_lc lc⟩⟩
  . case step A B B' red1 red1' ih =>
    have ⟨T1, redBT1, redCT1, lcT1⟩ := ParallelReduction.diamond wf red1 red2 lc
    have ⟨T2, redB'T2, redT1T2, lcT2⟩ := ih redBT1 (red1.preserve_lc lc)
    exists T2
    exact ⟨redB'T2, .step redCT1 redT1T2, lcT2⟩

theorem trans (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ B ≡>* C ]]): [[ Δ ⊢ A ≡>* C ]] := by
  induction red1 generalizing C <;> aesop (add unsafe constructors MultiParallelReduction)

theorem preserve_lc  (red: [[ Δ ⊢ A ≡>* B ]]) (lc: A.TypeVarLocallyClosed): B.TypeVarLocallyClosed := by
  induction red <;> aesop (add unsafe ParallelReduction.preserve_lc)

theorem confluence (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ A ≡>* C ]]) (wf: [[ ⊢ Δ ]]) (lc: A.TypeVarLocallyClosed): ∃ T, [[ Δ ⊢ B ≡>* T ]] ∧ [[ Δ ⊢ C ≡>* T ]] ∧ T.TypeVarLocallyClosed := by
  induction red2 generalizing B
  . case refl A =>
    exists B
    exact ⟨.refl,red1, red1.preserve_lc lc⟩
  . case step A C C' red2 red2' ih =>
    have ⟨T1, redBT1, redCT1, lcT1⟩ := red1.confluence_on_the_left red2 wf lc
    have ⟨T2, redT1T2, redC'T2, lcT2⟩ := ih redCT1 (red2.preserve_lc lc)
    exists T2
    exact ⟨redBT1.trans redT1T2, redC'T2, lcT2⟩

theorem common_reduct (red: [[ Δ ⊢ A ≡>* B ]]) (wf: [[ ⊢ Δ ]]) (lc: A.TypeVarLocallyClosed): exists C, [[ Δ ⊢ A ≡>* C ]] ∧ [[ Δ ⊢ B ≡>* C ]] ∧ C.TypeVarLocallyClosed :=
  refl |>.confluence red wf lc

end MultiParallelReduction

end TabularTypeInterpreter.«F⊗⊕ω»
