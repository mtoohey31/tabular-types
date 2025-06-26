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
def lamListApp' (A A' : «Type») (Bs B's : List «Type») (length_eq: Bs.length = B's.length)
  (redA: [[ Δ ⊢ A ≡> A' ]])
  (redB: ∀B B', ⟨B, B'⟩ ∈ (Bs.zip B's) → [[ Δ ⊢ B ≡> B' ]])
  (Alc: A.TypeVarLocallyClosed)
  : ParallelReduction Δ (A.listApp (Type.list Bs)) (Type.list <| B's.map fun B' => A'.app B') := by
    rw [← Std.Range.map_get!_eq (as := Bs), ← Std.Range.map_f_get!_eq (as := B's) (f := fun B' => A'.app B'), <- length_eq]
    refine lamListApp redA ?_ Alc
    . intro i mem
      apply redB
      have := (Bs.zip B's).get!_mem <| by
        rw [List.length_zip, ← length_eq, Nat.min_self]
        exact mem.upper
      rw [List.get!_zip length_eq mem.upper] at this
      exact this

theorem inv_arr (red: [[ Δ ⊢ (A → B) ≡> T ]]): ∃ A' B', T = [[(A' → B')]] ∧ [[ Δ ⊢ A ≡> A' ]] ∧ [[ Δ ⊢ B ≡> B' ]] := by
  cases red <;> aesop  (rule_sets := [pred])

theorem inv_forall (red: [[ Δ ⊢ (∀ a? : K. A) ≡> T ]]): ∃ A', T = [[∀ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a ≡> A'^a ]] := by
  cases red <;> aesop (add unsafe tactic guessI) (rule_sets := [pred])

theorem inv_prod (red: [[ Δ ⊢ ⊗A ≡> T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ≡> A' ]] := by
  cases red <;> aesop (rule_sets := [pred])

theorem inv_sum (red: [[ Δ ⊢ ⊕A ≡> T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ≡> A' ]] := by
  cases red <;> aesop (rule_sets := [pred])

theorem inv_list (red: [[ Δ ⊢ { </ A@i // i in [:n] /> } ≡> T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ Δ ⊢ A@i ≡> B@i // i in [:n] /> ]] := by
  generalize T_eq : [[{ </ A@i // i in [:n] /> }]] = T_ at red
  cases red <;> try cases T_eq
  . case refl.refl => exact ⟨A, rfl, fun i mem => refl⟩
  . case list n' A_ B AB =>
    injection T_eq with eq
    have eqnn' := Std.Range.length_eq_of_mem_eq eq
    subst eqnn'
    have eqAA_ := Std.Range.eq_of_mem_of_map_eq eq; clear eq
    exact ⟨B, rfl, λx nin => by simp_all⟩

open «Type» in
theorem inv_id (red: [[Δ ⊢ λa: K. a$0 ≡> A']]): A' = [[ λa: K. a$0 ]] := by
  cases red
  . case refl => rfl
  . case lam I B2 aa =>
    have ⟨a, nin⟩ := (I ++ B2.freeTypeVars).exists_fresh
    simp [TypeVar_open] at aa
    specialize aa a (by simp_all)
    generalize B2eq: [[ (B2^a) ]] = B2_ at aa
    cases aa; case refl =>
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
  . case lamListApp =>
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
  . case listAppComp I _ _ _ _ _ _ _ _ _ _ ihA₁ _ =>
    obtain ⟨_, notInA₁fv, _⟩ := notInFV
    have ⟨a', nin⟩ := (a :: I).exists_fresh
    specialize ihA₁ a' (by simp_all) a (not_mem_freeTypeVars_TypeVar_open_intro notInA₁fv (by aesop))
    exact not_mem_freeTypeVars_TypeVar_open_drop ihA₁

open «Type» TypeVarLocallyClosed in
theorem preserve_lc (red: [[ Δ ⊢ A ≡> B ]]): A.TypeVarLocallyClosed → B.TypeVarLocallyClosed := by
  induction red
  case lamApp Δ B K I A A' B' kindB redA redB ihA ihB =>
    intro lcAB
    cases lcAB; case app lcA lcB =>
    cases lcA; case lam lcA =>
    have lcA' := lcA.modus_ponens_open ihA
    apply Type_open_dec <;> simp_all
  case lamListApp ihA ihB =>
    intro lcAB
    simp_all
    cases lcAB; case listApp lcA lcB =>
    cases lcB; case list lcB =>
    constructor
    simp_all
    intro i In
    exact ihA.app (by simp_all [Std.Range.mem_of_mem_toList])
  case listAppComp lcA₀ _ _ _ ihA₀ ihA₁ ihB =>
    intro lc
    match lc with
    | .listApp _ (.listApp (.lam bodyA₁) lcB) =>
      simp_all
      have bodyA₁' := bodyA₁.modus_ponens_open ihA₁
      exact ihA₀.weaken.app bodyA₁' |>.lam |>.listApp ihB
  all_goals
    set_option aesop.dev.statefulForward false in
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

open «Type» TypeVarLocallyClosed in
theorem preserve_lc_rev (red: [[ Δ ⊢ A ≡> B ]]): B.TypeVarLocallyClosed → A.TypeVarLocallyClosed := by
  induction red
  case eta ih =>
    intro lc
    exact .lam <| .app (ih lc).weaken <| .var_bound Nat.le.refl
  case lamApp Δ B K I A A' B' kindB redA redB ihA ihB =>
    intro lcA'B'
    have ⟨a, notIn⟩ := (I ++ A.freeTypeVars ++ A'.freeTypeVars).exists_fresh
    rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)] at lcA'B'
    have Blc := kindB.TypeVarLocallyClosed_of
    have Abody := ihA a (by simp_all) lcA'B'.TypeVar_subst_drop
    apply TypeVar_close_inc (a := a) at Abody
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Abody
    exact Abody.lam.app Blc
  case lamListApp Δ A A' n B B' redA redB Alc ihA ihB =>
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
    intro lcA₀'A₁'B'
    match lcA₀'A₁'B' with
    | .listApp (.lam (.app _ bodyA₁')) lcB' =>
      simp_all
      have bodyA₁ := bodyA₁'.modus_ponens_open ihA₁
      exact lcA₀.listApp (bodyA₁.lam.listApp ihB)
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
  . case listAppComp A₀ Δ_ A₀' I K' A₁ A₁' B B' lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    subst Δ_
    apply ParallelReduction.listAppComp (I := a :: I ++ A₀.freeTypeVars) <;> try simp_all; done
    . intro a' nin
      specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]]
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
  . case listAppComp A₀ Δ_ A₀' I K' A₁ A₁' B B' lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    subst Δ_
    apply ParallelReduction.listAppComp (I := x :: I) <;> try simp_all; done
    . intro a' nin
      specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]]
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

open «Type» in
theorem TypeVar_drop_of_not_mem_freeTypeVars (Apr : [[Δ, a : K, Δ' ⊢ A ≡> B]])
  (aninA : a ∉ A.freeTypeVars) : [[Δ, Δ' ⊢ A ≡> B]] := by
  match Apr with
  | refl => exact refl
  | eta A'lc A'pr =>
    simp [freeTypeVars] at aninA
    exact eta A'lc <| A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA
  | lamApp B'ki A'pr B'pr (I := I) =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    apply lamApp (I := a :: I) (B'ki.TypeVar_drop_of_not_mem_freeTypeVars aninB') _ <|
      B'pr.TypeVar_drop_of_not_mem_freeTypeVars aninB'
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'pr a' a'ninI
    rw [← Environment.append] at A'pr ⊢
    exact TypeVar_drop_of_not_mem_freeTypeVars A'pr <|
      not_mem_freeTypeVars_TypeVar_open_intro aninA' ane.symm
  | lamListApp A'pr B'pr A'lc =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    apply lamListApp (A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA') _ A'lc
    intro i mem
    specialize B'pr i mem
    apply TypeVar_drop_of_not_mem_freeTypeVars B'pr
    apply aninB'
    exact Std.Range.mem_toList_of_mem mem
  | listAppId A'ki A'pr =>
    simp [freeTypeVars] at aninA
    exact listAppId (A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA)
      (A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA)
  | lam A'pr (I := I) =>
    simp [freeTypeVars] at aninA
    apply lam (I := a :: I)
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'pr a' a'ninI
    rw [← Environment.append] at A'pr ⊢
    exact A'pr.TypeVar_drop_of_not_mem_freeTypeVars <|
      not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  | app A'pr B'pr =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    exact app (A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA')
      (B'pr.TypeVar_drop_of_not_mem_freeTypeVars aninB')
  | scheme A'pr (I := I) =>
    simp [freeTypeVars] at aninA
    apply scheme (I := a :: I)
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'pr a' a'ninI
    rw [← Environment.append] at A'pr ⊢
    exact A'pr.TypeVar_drop_of_not_mem_freeTypeVars <|
      not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  | arr A'pr B'pr =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    exact arr (A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA')
      (B'pr.TypeVar_drop_of_not_mem_freeTypeVars aninB')
  | list A'pr =>
    simp [freeTypeVars] at aninA
    apply list
    intro i mem
    specialize A'pr i mem
    apply TypeVar_drop_of_not_mem_freeTypeVars A'pr
    apply aninA
    exact Std.Range.mem_toList_of_mem mem
  | listApp A'pr B'pr =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    exact listApp (A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA')
      (B'pr.TypeVar_drop_of_not_mem_freeTypeVars aninB')
  | listAppComp A₀lc A₀pr A₁pr B'pr (I := I) =>
    simp [freeTypeVars] at aninA
    let ⟨aninA₀, aninA₁, aninB'⟩ := aninA
    apply listAppComp (I := a :: I) A₀lc (A₀pr.TypeVar_drop_of_not_mem_freeTypeVars aninA₀) _ <|
      B'pr.TypeVar_drop_of_not_mem_freeTypeVars aninB'
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A₁pr a' a'ninI
    rw [← Environment.append] at A₁pr ⊢
    exact A₁pr.TypeVar_drop_of_not_mem_freeTypeVars <|
      not_mem_freeTypeVars_TypeVar_open_intro aninA₁ ane.symm
  | prod A'pr =>
    rw [freeTypeVars] at aninA
    exact prod <| A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA
  | sum A'pr =>
    rw [freeTypeVars] at aninA
    exact sum <| A'pr.TypeVar_drop_of_not_mem_freeTypeVars aninA
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · apply Nat.le_add_right_of_le
    apply Nat.le_trans _ (Nat.le_add_left ..)
    exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| Std.Range.mem_map_of_mem mem
  · exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| Std.Range.mem_map_of_mem mem

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
  · case eta Δ_ _ _ A'lc _ ih =>
    subst Δ_
    apply eta _ <| ih wf kindA rfl
    exact A'lc.TypeVar_subst kindA.TypeVarLocallyClosed_of
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
  . case lamListApp Δ_ T1 T1' n T2 T2' redT1 redT2 T1lc ihT1 ihT2 =>
    subst Δ_
    unfold Function.comp
    simp [Type.TypeVar_subst]
    apply ParallelReduction.lamListApp
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
  . case listAppComp Δ_ _ I K' _ _ _ _ lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    subst Δ_
    have Alc := kindA.TypeVarLocallyClosed_of
    refine .listAppComp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
      (lcA₀.TypeVar_subst Alc)
      (by simp_all) (λa' nin => ?_) (by simp_all)
    specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]] (by
      rw [← Environment.append_typeExt_assoc]
      refine wf.typeVarExt ?_
      simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
    ) kindA rfl
    repeat1' rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    simp_all [Environment.append_typeExt_assoc, Environment.typeExt_subst]

-- NOTE we could use a weaker wf: wfτ
theorem subst_out {A T T' : «Type»} (wf: [[ ⊢ Δ, a: K ]]) (red : [[ Δ, a: K ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ ⊢ T[A/a] ≡> T'[A/a] ]] := by
  apply subst_out' (Δ' := Environment.empty) <;> assumption

-- NOTE we could use a weaker wf: wfτ
set_option maxHeartbeats 400000 in  -- bruh
theorem subst_all' {A B T: «Type»} (wf: [[ ⊢ Δ, a: K, Δ' ]]) (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ, a: K, Δ' ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) (lcT: T.TypeVarLocallyClosed): [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡> T'[B/a] ]] := by
  generalize Δ_eq: (Δ.typeExt a K |>.append Δ') = Δ_ at red2
  induction red2 generalizing Δ Δ' A B
  . case refl Δ_ T_ =>
    apply subst_in (lcA := kindA.TypeVarLocallyClosed_of) (lcT := lcT)
    apply weakening
    . assumption
    . apply EnvironmentWellFormedness.subst (K := K) <;> simp_all
  · case eta Δ_ _ _ A'lc A'A'' ih =>
    subst Δ_
    rw [Type.TypeVar_subst, Type.TypeVar_subst, Type.TypeVar_subst, if_neg nofun]
    exact eta (A'lc.TypeVar_subst kindA.TypeVarLocallyClosed_of) <| ih wf red1 kindA A'lc rfl
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
  . case lamListApp Δ_ T1 T1' n T2 T2' redT1 redT2 T1lc ihT1 ihT2 =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    unfold Function.comp
    simp [«Type».TypeVar_subst]
    apply ParallelReduction.lamListApp
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
  . case listAppComp Δ_ _ I K' _ _ _ _ lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    subst Δ_
    match lcT with
    | .listApp lcA₀ (.listApp (.lam bodyA₁) lcB) =>
      cases lcT
      simp [«Type».TypeVar_subst]
      refine .listAppComp (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
        (lcA₀.TypeVar_subst kindA.TypeVarLocallyClosed_of)
        (by simp_all) (λa' nin => ?_) (by simp_all)
      . specialize @ihA₁ a' (by simp_all) Δ [[ Δ', a': K' ]] _ _ (by
          rw [← Environment.append_typeExt_assoc]
          refine wf.typeVarExt ?_
          simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
        ) red1 kindA bodyA₁.strengthen rfl
        rw [<- kindA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
        rw [<- red1.preserve_lc kindA.TypeVarLocallyClosed_of |>.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
        rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
        simp_all [Environment.append_typeExt_assoc, Environment.typeExt_subst]
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
  case refl => simp_all
  case eta A' _ _ _ A'lc _ ih =>
    apply ih wf
    let .lam I A'appki := k
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    specialize A'appki a aninI
    rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl, A'lc.TypeVar_open_id] at A'appki
    let .app A'ki (.var .head) := A'appki
    exact Kinding.TypeVar_drop_of_not_mem_freeTypeVars A'ki aninA' (Δ' := .empty)
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
  case lamListApp Δ A A' n B B' redA redB Alc ihA ihB =>
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
  case listAppComp Δ A₀' I K _ _ _ _ lcA₀ A₀A₀' A₁A₁' BB' ihA₀ ihA₁ ihB =>
    cases k; case listApp K1 K2 kA₀ kA₁B =>
    cases kA₁B; case listApp K3 kB kA₁ =>
    cases kA₁; case lam I' kA₁ =>

    specialize ihA₀ wf kA₀
    specialize ihB wf kB

    have ⟨a, nin⟩ := (I ++ I' ++ Δ.typeVarDom ++ A₀'.freeTypeVars).exists_fresh
    refine .listApp (.lam (I ++ I' ++ Δ.typeVarDom ++ A₀'.freeTypeVars) λa nin => ?_) ihB

    specialize ihA₁ a (by simp_all) (wf.typeVarExt (by simp_all [Environment.TypeVarNotInDom, Environment.TypeVarInDom])) (kA₁ a (by simp_all))

    have ihA₀ := ihA₀.weakening_r (Δ' := [[ ε, a: K ]]) (by simp_all [Environment.typeVarDom])
    simp [Environment.append] at ihA₀
    rw [← A₀A₀'.preserve_lc lcA₀ |>.TypeVar_open_id (a := a)] at ihA₀
    have ihA₀A₁ := ihA₀.app ihA₁
    simp_all [Type.TypeVar_open]
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

lemma _root_.TabularTypeInterpreter.«F⊗⊕ω».Type.expand_app_id (T: «Type») : T = [[ (a$0^^T) ]] := by simp [Type.Type_open]

local instance : Inhabited «Type» where
  default := .list []
in
set_option maxHeartbeats 400000 in  -- bruh
open Environment «Type» TypeVarLocallyClosed in
theorem diamond (wf: [[ ⊢ Δ ]]) (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ ⊢ A ≡> C ]]) (lc: A.TypeVarLocallyClosed): ∃ T, [[ Δ ⊢ B ≡> T ]] ∧ [[ Δ ⊢ C ≡> T ]] ∧ T.TypeVarLocallyClosed := by
  induction red1 generalizing C
  . case refl Δ A => exact ⟨C, red2, .refl, red2.preserve_lc lc⟩
  · case eta A' _ A'' _ A'lc A'A'' ih =>
    cases red2
    · case refl => exact ⟨_, refl, eta A'lc A'A'', A'A''.preserve_lc A'lc⟩
    · case eta A'C => exact ih wf A'C A'lc
    · case lam I B' A'appB' =>
      let ⟨a, anin⟩ := A'.freeTypeVars ++ B'.freeTypeVars ++ I
        |>.exists_fresh
      let ⟨aninA'B', aninI⟩ := List.not_mem_append'.mp anin
      let ⟨aninA', aninB'⟩ := List.not_mem_append'.mp aninA'B'
      specialize A'appB' a aninI
      rw [TypeVar_open, TypeVar_open, if_pos rfl, A'lc.TypeVar_open_id] at A'appB'
      generalize B''eq : B'.TypeVar_open a = B'' at A'appB'
      cases A'appB'
      · case refl =>
        have : A'.app (var (.free a)) = TypeVar_open (A'.app (.var (.bound 0))) a := by
          simp [TypeVar_open]
          rw [A'lc.TypeVar_open_id]
        rw [this] at B''eq
        cases TypeVar_open_inj_of_not_mem_freeTypeVars aninB'
          (by rw [freeTypeVars, freeTypeVars, List.append_nil]; exact aninA') B''eq
        exact ⟨_, refl, eta A'lc A'A'', A'A''.preserve_lc A'lc⟩
      · case lamApp I' A''' A'''' _ A'''A'''' aki aB' =>
        let .refl := aB'
        rw [← Type_open_var] at B''eq
        let ⟨a', a'nin⟩ := a :: I' |>.exists_fresh
        let ⟨a'nea, a'ninI'⟩ := List.not_mem_cons.mp a'nin
        rw [Type.freeTypeVars] at aninA'
        let aninA''''op := A'''A'''' a' a'ninI' |>.preserve_not_mem_freeTypeVars _ <|
          not_mem_freeTypeVars_TypeVar_open_intro aninA' a'nea.symm (n := 0)
        let aninA'''' := not_mem_freeTypeVars_TypeVar_open_drop aninA''''op
        cases TypeVar_open_inj_of_not_mem_freeTypeVars aninB' aninA'''' B''eq
        let .var .head := aki
        apply ih wf (.lam (I := a :: I') _) A'lc
        intro a'' a''nin
        let ⟨ane, a''ninI'⟩ := List.not_mem_cons.mp a''nin
        specialize A'''A'''' a'' a''ninI'
        exact TypeVar_drop_of_not_mem_freeTypeVars (Δ' := .typeExt .empty ..) A'''A'''' <|
          not_mem_freeTypeVars_TypeVar_open_intro aninA' ane.symm
      · case app A''' B''' A'A''' aB''' =>
        let .refl := aB'''
        have : B'.TypeVar_open a = TypeVar_open (A'''.app (.var (.bound 0))) a := by
          simp [TypeVar_open]
          rw [A'A'''.preserve_lc A'lc |>.TypeVar_open_id, B''eq]
        cases TypeVar_open_inj_of_not_mem_freeTypeVars aninB' (by
          rw [freeTypeVars, freeTypeVars, List.append_nil]
          exact A'A'''.preserve_not_mem_freeTypeVars _ aninA') this
        let ⟨T, A''T, A'''T, Tlc⟩ := ih (C := A''') wf
          (A'A'''.TypeVar_drop_of_not_mem_freeTypeVars aninA' (Δ' := .empty)) A'lc
        exact ⟨_, A''T, .eta (A'A'''.preserve_lc A'lc) A'''T, Tlc⟩
  . case lamApp Δ B K I A A' B' k redA redB ihA ihB =>
    -- Assume [[ Δ, a: K ⊢ A^a ≡> A'^a ]] [[ Δ ⊢ B ≡> B' ]]
    -- Also, red2: [[ Δ ⊢ (λ?: K. A) B ≡> C ]]
    -- wts. [[ Δ ⊢ A'^^B' ≡> ?T ]] and [[ Δ ⊢ C ≡> ?T ]]
    -- So, we need to also discuss the shape of C, by case analysis on red2

    cases lc; case app lcA_ lcB =>
    cases lcA_; case lam lcA =>
    have lcA_a := λa => lcA.strengthen (a := a)
    have lcA': A'.TypeVarLocallyClosed 1 := lcA.modus_ponens_open (λ a nin => redA a nin |>.preserve_lc)
    simp_all
    cases red2
    . case refl => exact ⟨[[ (A'^^B') ]], .refl, .lamApp k redA redB, lcA'.Type_open_dec <| lcB |> redB.preserve_lc⟩
    . case lamApp I' A2 B2 redA' redB' _ =>
      have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ A2.freeTypeVars ++ Δ.typeVarDom ++ B'.freeTypeVars).exists_fresh
      have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
      specialize redA' a (by simp_all)
      have ⟨T1, redA'T, redA2T, lcT1⟩ := ihA a (by simp_all) wf' redA'
      have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'
      exists [[ (T1[T2/a]) ]]
      repeat' apply And.intro
      . rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
        apply subst_all <;> try assumption
        . apply preservation (red := redB) <;> simp_all
        . apply (redA _ (by simp_all) |>.preserve_lc); simp_all
      . rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
        apply subst_all <;> try assumption
        . apply preservation (red := redB') <;> simp_all
        . apply redA'.preserve_lc; simp_all
      . apply TypeVarLocallyClosed.TypeVar_subst <;> assumption
    . case app A2 B2 redA' redB' =>
      cases redA'
      . case refl =>
        have ⟨a, notInI⟩ := (I ++ A.freeTypeVars ++ A'.freeTypeVars ++ Δ.typeVarDom).exists_fresh
        have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
        specialize redA a (by simp_all)
        have ⟨T1, redA'T, _, lcT1⟩ := ihA a (by simp_all) wf' redA
        have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'

        rw [<- TypeVar_open_TypeVar_close_id (A:=T1) (a:=a)] at redA'T <;> try assumption
        exists [[ (A'^^T2) ]]
        repeat' apply And.intro
        . rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
          rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
          apply subst_in <;> try assumption
          . apply redB.preserve_lc; simp_all
          . apply redA.preserve_lc; simp_all
        . apply (lamApp_intro_ex a) <;> try (simp_all; done)
          . apply preservation (red := redB') <;> simp_all
        . apply redB.preserve_lc at lcB
          simp_all [Type_open_dec]
      · case eta Alc AA2 =>
        let ⟨T2, B'T2, B2T2, T2lc⟩ := ihB redB'
        let ⟨a, anin⟩ := A'.freeTypeVars ++ A2.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
        let ⟨aninA'A2I, aninΔ⟩ := List.not_mem_append'.mp anin
        let ⟨aninA'A2, aninI⟩ := List.not_mem_append'.mp aninA'A2I
        let ⟨aninA', aninA2⟩ := List.not_mem_append'.mp aninA'A2
        let awf := wf.typeVarExt aninΔ (K := K)
        let ⟨T1, A'opT1, A2appT1, T1lc⟩ := ihA (C := A2.app (.var (.free a))) _
          aninI awf (by
          rw [TypeVar_open, TypeVar_open, if_pos rfl, Alc.TypeVar_open_id]
          exact AA2.app .refl |>.weakening awf (Δ' := .typeExt .empty ..)
        )
        refine ⟨T1.TypeVar_subst a T2, ?_, ?_, T1lc.TypeVar_subst T2lc⟩
        · rw [← TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA']
          exact subst_all awf B'T2 A'opT1 (redB.preservation wf k) (by
            rw [Type_open_var]
            exact lcA'.Type_open_dec .var_free
          )
        · have : A2.app B2 = Type.TypeVar_subst (A2.app (.var (.free a))) a B2 := by
            simp [Type.TypeVar_subst]
            rw [TypeVar_subst_id_of_not_mem_freeTypeVars aninA2]
          rw [this]
          exact subst_all awf B2T2 A2appT1 (redB'.preservation wf k) (A2appT1.preserve_lc_rev T1lc)
      . case lam I' B22 redA' =>
        have ⟨a, notInI⟩ := (I ++ I' ++ A'.freeTypeVars ++ B22.freeTypeVars ++ Δ.typeVarDom).exists_fresh
        have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
        specialize redA' a (by simp_all)
        have ⟨T1, redA'T, redA2T, lcT1⟩ := ihA a (by simp_all) wf' redA'
        have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'

        rw [<- lcT1.TypeVar_open_TypeVar_close_id (a := a)] at redA'T redA2T
        exists [[ ((\a^T1)^^T2) ]]
        repeat' apply And.intro
        . rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
          rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close]
          apply subst_all <;> try assumption
          . apply preservation (red := redB) <;> simp_all
          . apply redA _ (by simp_all) |>.preserve_lc; simp_all
        . apply (lamApp_intro_ex a) <;> try (simp_all; done)
          . simp_all [not_mem_freeTypeVars_TypeVar_close ]
          . apply preservation (red := redB') <;> simp_all
        . simp_all [Type_open_dec, TypeVar_close_inc]
  . case lamListApp Δ A A' n B B' AA' BB' Alc ih1 ih2 =>
    generalize B_eq : («Type».list ([:n].map fun i => B i)) = B_ at red2
    cases lc; case listApp Alc Blc =>
    have Bilc := λi iltn => match Blc with | .list Blc => Blc (B i) (Std.Range.mem_map_of_mem iltn)
    have B'ilc := λi iltn => BB' i iltn |>.preserve_lc <| Bilc i iltn
    have A'lc := AA'.preserve_lc Alc
    cases red2
    . case refl =>
      subst B_eq
      refine ⟨_, .refl, .lamListApp AA' BB' Alc, .list λT Tin => ?_⟩
      . have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
        exact A'lc.app <| B'ilc i iltn
    . case lamListApp A'' n_ B_ B'' _ BB'' _ AA'' =>
      injection B_eq with eq
      have neq := Std.Range.length_eq_of_mem_eq eq; subst neq
      have Beq := Std.Range.eq_of_mem_of_map_eq eq; clear eq
      have A''lc := AA''.preserve_lc Alc
      -- have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
      have ⟨T1, A'T1, A''T1, T1lc⟩:= ih1 wf AA'' Alc
      have ⟨T2, ih2⟩ := Std.Range.skolem <| λi iltn => ih2 i iltn wf (BB'' i iltn |> (Beq i iltn).substr) (Bilc i iltn)
      refine ⟨[[ { </ T1 T2@i // i in [:n] /> } ]], .list λi iltn => ?_, .list λi iltn => ?_, .list λT Tin => ?_⟩
      . have ⟨B'T2, B''T2, T2ilc⟩ := ih2 i iltn
        exact A'T1.app B'T2
      . have ⟨B'T2, B''T2, T2ilc⟩ := ih2 i iltn
        exact A''T1.app B''T2
      . have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
        have ⟨B'T2, B''T2, T2ilc⟩ := ih2 i iltn
        exact T1lc.app T2ilc
    . case listAppId K _ _ BkiLK BB2 =>
      subst B_eq
      rename' C => B2
      rw [AA'.inv_id]
      have ⟨B2, B2eq, BB2⟩ := BB2.inv_list; rw [B2eq]; clear B2eq
      have ⟨T, ih2⟩ := Std.Range.skolem <| λi iltn => ih2 i iltn wf (BB2 i iltn) (Bilc i iltn)
      refine ⟨[[ { </ T@i // i in [:n] /> } ]], .list λi iltn => ?_, .list λi iltn => ?_, .list λT Tin => ?_⟩
      . have ⟨B'T, B2T, T2ilc⟩ := ih2 i iltn
        rw [ [[ T@i ]].expand_app_id ]
        have B'kiK := BB' i iltn |>.preservation wf (BkiLK.inv_list i iltn)
        exact .lamApp (I := []) B'kiK (λa nin => .refl) B'T
      . have ⟨B'T, B2T, T2ilc⟩ := ih2 i iltn
        exact B2T
      . have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
        have ⟨B'T, B2T, T2ilc⟩ := ih2 i iltn
        exact T2ilc
    . case listApp A2 B2 AA2 BB2 =>
      subst B_eq
      have ⟨T1, A'T1, A2T1, T1lc⟩ := ih1 wf AA2 Alc
      have ⟨B2, B2eq, BB2⟩ := BB2.inv_list; rw [B2eq]; clear B2eq
      have ⟨T2, ih2⟩ := Std.Range.skolem <| λi iltn => ih2 i iltn wf (BB2 i iltn) (Bilc i iltn)
      refine ⟨[[ { </ T1 T2@i // i in [:n] /> } ]], .list λ i iltn => ?_, ?_, .list λ T Tin => ?_⟩
      . have ⟨B'T2, B2T2, T2ilc⟩ := ih2 i iltn
        exact A'T1.app B'T2
      . have A2lc := AA2.preserve_lc Alc
        refine A2T1.lamListApp (λi iltn => ?_) A2lc
        . have ⟨B'T2, B2T2, T2ilc⟩ := ih2 i iltn
          exact B2T2
      . have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
        have ⟨B'T2, B2T2, T2ilc⟩ := ih2 i iltn
        exact T1lc.app T2ilc
    . case listAppComp => cases B_eq
  . case listAppId Δ B K B' BkiLK BB' ih =>
    rename' C => B2
    match lc with
    | .listApp _ Blc =>
    cases red2
    . case refl =>
      have ⟨T, B'T, BT, Tlc⟩ := ih wf .refl Blc
      exact ⟨T, B'T, BT.listAppId BkiLK, Tlc⟩
    . case lamListApp n B B2 BB2 _ aA' =>
      rw [aA'.inv_id]
      have ⟨T, B'T, B2T, Tlc⟩ := ih wf (.list BB2) Blc
      have ⟨T, Teq, B2T⟩ := B2T.inv_list; rw [Teq] at B'T Tlc; clear Teq
      refine ⟨[[ { </ T@i // i in [:n] /> } ]], B'T, .list λ i iltn => ?_, Tlc⟩
      . rw [ [[ T@i ]].expand_app_id ]
        have B2kiK := BB2 i iltn |>.preservation wf (BkiLK.inv_list i iltn)
        exact .lamApp (I := []) B2kiK (λa nin => .refl) (B2T i iltn)
    . case listAppId _ BB2 => exact ih wf BB2 Blc
    . case listApp A2 B2 aA2 BB2 =>
      rw [aA2.inv_id]
      have ⟨T, B'T, B2T, Tlc⟩ := ih wf BB2 Blc
      refine ⟨T, B'T, ?_, Tlc⟩
      have B2kiK := BB2.preservation wf BkiLK
      exact B2T.listAppId B2kiK
    . case listAppComp I K A₁ A₁' B' B'' A₁A₁' B'B'' _ idA₀' =>
      cases idA₀'.inv_id
      let ⟨T, B''T, A₁'B''T, Tlc⟩ := ih wf (.listApp (.lam A₁A₁') B'B'') Blc
      refine ⟨T, B''T, ?_, Tlc⟩
      sorry
  . case lam I Δ K A B red1 ih =>
    -- We know A is of shape (λ _: K. A)
    -- By inversion on the second reduction, C is of shape (λ _: K. C'), and [Δ, a: K ⊢ A^a ≡> C'^a]
    cases red2
    · case refl => exact ⟨_, refl, lam red1, lam red1 |>.preserve_lc lc⟩
    · case eta A' A'lc A'C =>
      let ⟨a, anin⟩ := A'.freeTypeVars ++ B.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
      let ⟨aninA'BI, aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninA'B, aninI⟩ := List.not_mem_append'.mp aninA'BI
      let ⟨aninA', aninB⟩ := List.not_mem_append'.mp aninA'B
      specialize red1 a aninI
      simp [TypeVar_open] at red1
      rw [A'lc.TypeVar_open_id] at red1
      let awf := wf.typeVarExt aninΔ (K := K)
      let ⟨T, BT, CT, Tlc⟩ := ih (C := C.app (.var (.free a))) _ aninI awf (by
        simp [TypeVar_open]
        rw [A'lc.TypeVar_open_id]
        exact app (A'C.weakening awf (Δ' := .typeExt .empty ..)) refl) (by
        simp [TypeVar_open]
        rw [A'lc.TypeVar_open_id]
        exact A'lc.app .var_free)
      generalize B'eq : B.TypeVar_open a = B' at red1
      cases red1
      · case refl =>
        have : B.TypeVar_open a = TypeVar_open (A'.app (.var (.bound 0))) a := by
          simp [TypeVar_open]
          rw [A'lc.TypeVar_open_id]
          exact B'eq
        cases TypeVar_open_inj_of_not_mem_freeTypeVars aninB (by
          rw [freeTypeVars, freeTypeVars, List.append_nil]
          exact aninA') this
        exact ⟨_, eta A'lc A'C, refl, A'C.preserve_lc A'lc⟩
      · case lamApp => sorry
      · case app A'' B'' A'A'' aB'' =>
        let .refl := aB''
        have : B.TypeVar_open a = TypeVar_open (A''.app (.var (.bound 0))) a := by
          simp [TypeVar_open]
          rw [A'A''.preserve_lc A'lc |>.TypeVar_open_id]
          exact B'eq
        cases TypeVar_open_inj_of_not_mem_freeTypeVars aninB (by
          rw [freeTypeVars, freeTypeVars, List.append_nil]
          exact A'A''.preserve_not_mem_freeTypeVars _ aninA') this
        -- refine ⟨_, eta (A'A''.preserve_lc A'lc) ?_, ?_, Tlc⟩
        sorry
    · case lam I' C red2' =>
      -- have ⟨C', eqC, I', red2'⟩ := red2.inv_lam
      have ⟨a, nin⟩ := I ++ I' ++ A.freeTypeVars ++ B.freeTypeVars ++ C.freeTypeVars ++ Δ.typeVarDom |>.exists_fresh
      specialize red2' a (by simp_all)
      -- By I.H. [Δ, a: K ⊢ B^a ≡> T'] and [Δ, a: K ⊢ C'^a ≡> T']
      have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
      have lc' := match lc with |.lam lc => lc.strengthen (a := a)
      have ⟨T', predA, predB, lcT'⟩ := ih a (by simp_all) wf' red2' lc'; clear ih
      -- Important: to introduce lam reduction, we need both sides to be (?^a), so we close and open rhs.
      rw [<- TypeVar_open_TypeVar_close_id (A:=T') (a:=a)] at predA predB <;> try assumption
      -- Now we know that [Δ, a: K ⊢ B^a ≡> T'\a^a], and we want [[ Δ ⊢ λ?: K. B ≡> ?T ]]
      exists [[λa?: K. \a^T']]
      exact ⟨
        lam_intro_ex a (by simp_all [not_mem_freeTypeVars_TypeVar_close]) wf predA,
        lam_intro_ex a (by simp_all [not_mem_freeTypeVars_TypeVar_close]) wf predB,
        .lam lcT'.TypeVar_close_inc
      ⟩
  . case app Δ A A' B B' AA' BB' ih1 ih2 =>
    cases lc; case app Alc Blc =>
    cases red2
    . case refl => exact ⟨[[ (A' B') ]], .refl, .app AA' BB', .app (AA'.preserve_lc Alc) (BB'.preserve_lc Blc)⟩
    . case lamApp K I A A'' B'' AA'' BkiK BB'' =>
      sorry
      -- have ⟨A', eqA', _, AA'⟩ := AA'.inv_lam; subst eqA'
      -- have ⟨T1, A'T1, A''T1, T1lc⟩ := ih1 wf (.lam AA'') Alc
      -- have ⟨T2, B'T2, B''T2, T2lc⟩ := ih2 wf BB'' Blc
      -- have ⟨T1, T1eq, _, A'T1⟩ := A'T1.inv_lam; rw [T1eq] at A''T1 T1lc; clear T1eq
      -- have ⟨T1, T1eq, I', A''T1⟩ := A''T1.inv_lam; injection T1eq with _ eq; rw [eq] at A'T1 T1lc; clear eq
      -- exists [[ (T1^^T2) ]]
      -- have T1T2lc := match T1lc with |.lam T1lc => T1lc.Type_open_dec T2lc
      -- have B'kiK := BB'.preservation wf BkiK
      -- refine ⟨.lamApp B'kiK A'T1 B'T2, ?_, T1T2lc⟩
      -- have ⟨a, nin⟩ := I ++ I' ++ Δ.typeVarDom ++ A''.freeTypeVars ++ T1.freeTypeVars |>.exists_fresh
      -- repeat1' rw [<- TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
      -- have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
      -- have A''open_lc := match Alc with | .lam Alc => AA'' a (by simp_all) |>.preserve_lc <| Alc.strengthen
      -- have B''kiK := BB''.preservation wf BkiK
      -- exact subst_all wf' B''T2 (A''T1 a (by simp_all)) B''kiK A''open_lc
    . case app A'' B''  AA'' BB'' =>
      have ⟨T1, A'T1, A''T1, T1lc⟩ := ih1 wf AA'' Alc
      have ⟨T2, B'T2, B''T2, T2lc⟩ := ih2 wf BB'' Blc
      exact ⟨[[ (T1 T2) ]], .app A'T1 B'T2, .app A''T1 B''T2, .app T1lc T2lc⟩
  . case scheme I' Δ K A B AB ih =>
    have ⟨C, eqC, I, AC⟩:= red2.inv_forall; subst eqC; clear red2
    have ⟨a, notInI⟩ := (I ++ I' ++ B.freeTypeVars ++ C.freeTypeVars ++ Δ.typeVarDom).exists_fresh
    have wf' : [[ ⊢ Δ, a: K ]] := .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom])
    have lc' := match lc with |.forall lc => lc.strengthen (a := a)
    have ⟨T, BT, CT, Tlc⟩ := ih a (by simp_all) wf' (AC a (by simp_all)) lc'; clear ih
    rw [<- TypeVar_open_TypeVar_close_id (A:=T) (a:=a) (by assumption)] at BT CT
    exact ⟨
      [[ ∀a?: K. \a^T ]],
      forall_intro_ex a (by simp_all [not_mem_freeTypeVars_TypeVar_close]) wf BT,
      forall_intro_ex a (by simp_all [not_mem_freeTypeVars_TypeVar_close]) wf CT,
      .forall Tlc.TypeVar_close_inc
    ⟩
  . case arr Δ A1 B1 A2 B2 A1B1 A2B2 ih1 ih2 =>
    cases lc; case arr A1lc A2lc =>
    have ⟨C1, C2, eqC, A1C1, A2C2⟩ := red2.inv_arr; subst eqC; clear red2
    have ⟨T1, B1T1, C1T1, T1lc⟩ := ih1 wf A1C1 A1lc
    have ⟨T2, B2T2, C2T2, T2lc⟩ := ih2 wf A2C2 A2lc
    exact ⟨[[ (T1 → T2) ]], .arr B1T1 B2T2, .arr C1T1 C2T2, .arr T1lc T2lc⟩
  . case list n Δ A B AB ih =>
    cases lc; case list Alc =>
    have ⟨C, eqC, AC⟩ := red2.inv_list; subst eqC; clear red2
    have ih := λi iltn => ih i iltn wf (AC i iltn) (Alc (A i) (Std.Range.mem_map_of_mem iltn))
    have ⟨T, ih⟩ := Std.Range.skolem ih
    refine ⟨[[ { </ T@i // i in [:n] /> } ]], .list λi iltn => ?_, .list λi iltn => ?_, .list λTi Tiin => ?_⟩
    . have ⟨BT, _⟩ := ih i iltn; exact BT
    . have ⟨_, CT, _⟩ := ih i iltn; exact CT
    . have ⟨i, iltn, eqT⟩ := Std.Range.mem_of_mem_map Tiin; subst eqT
      have ⟨_, _, Tlc⟩ := ih i iltn
      exact Tlc
  . case listApp Δ A A' B B' AA' BB' ih1 ih2 =>
    cases lc; case listApp Alc Blc =>
    cases red2
    . case refl => exact ⟨[[ (A' ⟦B'⟧) ]], .refl, .listApp AA' BB', .listApp (AA'.preserve_lc Alc) (BB'.preserve_lc Blc)⟩
    . case lamListApp A'' n B B'' BB'' Alc AA'' =>
      have Bilc := λi iltn => match Blc with | .list Blc => Blc (B i) (Std.Range.mem_map_of_mem iltn)

      have ⟨T1, A'T1, A''T1, T1lc⟩ := ih1 wf AA'' Alc; clear ih1
      have ⟨T2, B'T2, B''T2, T2lc⟩ := ih2 wf (.list BB'') Blc; clear ih2

      have ⟨B', eqB', BB'⟩:= BB'.inv_list; rw [eqB'] at B'T2 ⊢; clear eqB'
      have ⟨T2, T2eq, B'T2⟩:= B'T2.inv_list; rw [T2eq] at B''T2 T2lc; clear T2eq
      have ⟨T2, T2eq, B''T2⟩:= B''T2.inv_list
      injection T2eq with eq
      have T2eq := Std.Range.eq_of_mem_of_map_eq eq; clear eq
      have B'T2 := λ i iltn => T2eq i iltn |>.subst (B'T2 i iltn)
      have T2lc := λi iltn => match T2lc with |.list T2lc => T2lc (T2 i) (T2eq i iltn |>.subst <| Std.Range.mem_map_of_mem iltn)
      clear T2eq

      exact ⟨
        [[ { </ T1 T2@i // i in [:n] /> } ]],
        .lamListApp A'T1 B'T2 (AA'.preserve_lc Alc),
        .list (λ i iltn => A''T1.app <| B''T2 i iltn),
        .list (λ T Tin => (by
          have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
          exact T1lc.app <| T2lc i iltn
        ))
      ⟩
    . case listAppId K BkiLK BB'' =>
      rename' C => B''
      rw [AA'.inv_id]
      have ⟨T, B'T, B''T, Tlc⟩ := ih2 wf BB'' Blc
      have B'kiLK := BB'.preservation wf BkiLK
      exact ⟨T, .listAppId B'kiLK B'T, B''T, Tlc⟩
    . case listApp A'' B''  AA'' BB'' =>
      have ⟨T1, A'T1, A''T1, T1lc⟩ := ih1 wf AA'' Alc
      have ⟨T2, B'T2, B''T2, T2lc⟩ := ih2 wf BB'' Blc
      exact ⟨[[ (T1 ⟦T2⟧) ]], .listApp A'T1 B'T2, .listApp A''T1 B''T2, .listApp T1lc T2lc⟩
    . case listAppComp A₀'' I K A₁ A₁'' B B'' A₁A₁' BB' Alc AA₀' =>
      rename' A' => A₀'
      rename' BB' => A₁BA₁B'
      rename' A₁A₁' => A₁A₁''
      rename' BB' => BB''
      rename' B' => A₁'B'
      have ⟨T1, A₀'T1, A₀''T1, T1lc⟩ := ih1 wf AA₀' Alc
      have ⟨T2, A₁'B'T2, A₁''B''T2, T2lc⟩ := ih2 wf (.listApp (.lam A₁A₁'') BB'') Blc
      clear ih1 ih2
      cases A₁BA₁B'
      . case refl =>
        let .listApp (.lam A₁lc) Blc := Blc
        exact ⟨
          .listApp (.lam K (T1.app A₁'')) B'',
          listAppComp (I := I) (AA'.preserve_lc Alc) A₀'T1 A₁A₁'' BB'',
          listApp (lam (I := Δ.typeVarDom) (by
            intro _ anin
            rw [TypeVar_open, TypeVar_open, T1lc.TypeVar_open_id,
                AA₀'.preserve_lc Alc |>.TypeVar_open_id]
            apply app _ refl
            exact A₀''T1.weakening (Δ' := .typeExt .empty ..) <| wf.typeVarExt anin
          )) refl,
          .listApp (.lam (.app T1lc.weaken <| A₁lc.modus_ponens_open (λ a nin => A₁A₁'' a nin |>.preserve_lc)))
            <| BB''.preserve_lc Blc
        ⟩
      . case lamListApp A₁' n B B' BB' A₁body A₁A₁' => sorry
      . case listAppId Bki BA₁'B' =>
        refine ⟨[[(T1 ⟦T2⟧)]], listApp A₀'T1 A₁'B'T2, ?_, .listApp T1lc T2lc⟩
        let ⟨a, anin⟩ := A₁''.freeTypeVars ++ I |>.exists_fresh
        let ⟨aninA₁'', aninI⟩ := List.not_mem_append'.mp anin
        let aA₁''' := A₁A₁'' a aninI
        rw [Type.TypeVar_open, if_pos rfl] at aA₁'''
        generalize A₁'''eq : A₁''.TypeVar_open a = A₁''' at aA₁'''
        cases aA₁'''
        cases A₁''
        all_goals rw [Type.TypeVar_open] at A₁'''eq
        case var =>
          split at A₁'''eq
          case isFalse =>
            cases A₁'''eq
            rw [Type.freeTypeVars] at aninA₁''
            nomatch List.not_mem_singleton.mp aninA₁''
          case isTrue h =>
            cases h
            cases A₁''B''T2
            apply listApp (eta (AA₀'.preserve_lc Alc) A₀''T1)
            sorry
            sorry
            sorry
            sorry
            sorry
        all_goals nomatch A₁'''eq
      . case listApp A₁' B' A₁A₁' BB' =>
        cases A₁A₁'
        . case refl => sorry
        · case eta => sorry
        . case lam I A₁' A₁A₁' => sorry
          -- cases A₁''B''T2
      . case listAppComp =>
      sorry
  . case listAppComp => sorry
  . case prod Δ A B AB ih =>
    cases lc; case prod Alc =>
    have ⟨C, eqC, AC⟩ := red2.inv_prod; subst eqC; clear red2
    have ⟨T, BT, CT, Tlc⟩ := ih wf AC Alc
    exact ⟨[[ ⊗T ]], .prod BT, .prod CT, .prod Tlc⟩
  . case sum Δ A B AB ih =>
    cases lc; case sum Alc =>
    have ⟨C, eqC, AC⟩ := red2.inv_sum; subst eqC; clear red2
    have ⟨T, BT, CT, Tlc⟩ := ih wf AC Alc
    exact ⟨[[ ⊕T ]], .sum BT, .sum CT, .sum Tlc⟩

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

theorem confluence_on_the_left (red1: [[ Δ ⊢ A ≡>* B ]]) (red2: [[ Δ ⊢ A ≡> C ]]) (wf: [[ ⊢ Δ ]])  (lc: A.TypeVarLocallyClosed): ∃ T, [[ Δ ⊢ B ≡>* T ]] ∧ [[ Δ ⊢ C ≡>* T ]] ∧ T.TypeVarLocallyClosed := by
  induction red1 generalizing C
  . case refl A =>
    exists C
    exact ⟨red2.Multi_of, ⟨.refl, red2.preserve_lc lc⟩⟩
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

theorem common_reduct (eAB: [[ Δ ⊢ A <≡>* B ]]) (wf: [[ ⊢ Δ ]]) (Alc: A.TypeVarLocallyClosed) (Blc: B.TypeVarLocallyClosed): ∃ C, [[ Δ ⊢ A ≡>* C ]] ∧ [[ Δ ⊢ B ≡>* C ]] := by
  induction eAB
  . case refl A => exact ⟨A, .refl, .refl⟩
  . case step A B AB => exact ⟨B, AB.Multi_of, .refl⟩
  . case sym B A mBA ih =>
    obtain ⟨C, mBC, mAC⟩ := ih Blc Alc
    exact ⟨C, mAC, mBC⟩
  . case trans A A' B eAA' eA'B ih1 ih2 =>
    have A'lc := eAA'.preserve_lc.1 Alc
    obtain ⟨C, mAC, mA'C⟩ := ih1 Alc A'lc
    obtain ⟨C', mA'C', mBC'⟩ := ih2 A'lc Blc
    have ⟨T, mCT, mC'T, _⟩ := mA'C.confluence mA'C' wf A'lc
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
