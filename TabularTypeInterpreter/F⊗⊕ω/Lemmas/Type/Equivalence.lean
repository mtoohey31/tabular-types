import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.ParallelReduction

namespace TabularTypeInterpreter.«F⊗⊕ω»

open Environment in
-- TODO need to add wf judgment to this theorem and also parallel reduction + TypeEq definition
theorem ParallelReduction.TypeEquivalence_of (h: [[ Δ ⊢ A ≡> B ]]) (wf: [[ ⊢ Δ ]]) (Alc: A.TypeVarLocallyClosed) : [[ Δ ⊢ A ≡ B ]] := by
  induction h
  . case refl => exact (.refl Alc)
  . case lamApp Δ _ _ I _ _ _ kinding AA' BB' ih1 ih2 =>
    match Alc with
    | .app (.lam Abody) Blc =>
      simp_all [Abody.strengthen]
      have A'body := Abody.modus_ponens_open (λ a nin => AA' a nin |>.preserve_lc)
      have B'lc := BB'.preserve_lc Blc
      refine .trans (.app (.lam (I ++ Δ.typeVarDom) ?_) ih2) (.lamApp A'body B'lc ?_)
      . exact λa nin => ih1 a (by simp_all) (wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom]))
      . exact BB'.preservation wf Blc kinding
  . case lamListApp _ Δ _ _ I _ _ _ _ AA' BB' _ ih1 ih2 =>
    match Alc with
    | .listApp (.lam Abody) (.list Blc) =>
      simp_all [Abody.strengthen, Std.Range.mem_toList_of_mem]
      have A'body := Abody.modus_ponens_open (λ a nin => AA' a nin |>.preserve_lc)
      have B'lc := λi iltn => BB' i iltn |>.preserve_lc (Blc i (Std.Range.mem_toList_of_mem iltn))
      refine .trans (.listApp (.lam (I ++ Δ.typeVarDom) ?_) (.list ih2))
                (.trans (.lamListApp A'body.lam B'lc) (.list λi iltn => (.lamApp A'body (B'lc i iltn) ?_)))
      . exact λa nin => ih1 a (by simp_all) (wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom]))
      . exact BB' i iltn |>.preservation wf (Blc i (Std.Range.mem_toList_of_mem iltn)) (by simp_all [TypeVarNotInDom, TypeVarInDom])
  . case lam I Δ _ _ _ _ ih =>
    match Alc with
    | .lam Alc =>
      refine .lam (I ++ Δ.typeVarDom) ?_
      exact λa nin => ih a (by simp_all) (wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom])) Alc.strengthen
  . case app ih1 ih2 =>
    match Alc with | .app Alc Blc => simp_all; exact .app ih1 ih2
  . case scheme I Δ _ _ _ _ ih =>
    match Alc with
    | .forall Alc =>
      refine .scheme (I ++ Δ.typeVarDom) ?_
      exact λa nin => ih a (by simp_all) (wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom])) Alc.strengthen
  . case arr _ _ ih1 ih2 =>
    match Alc with | .arr Alc Blc => simp_all; exact .arr ih1 ih2
  . case list _ ih =>
    match Alc with | .list Alc => simp_all [Std.Range.mem_toList_of_mem]; exact .list ih
  . case listApp _ _ ih1 ih2 =>
    match Alc with | .listApp Alc Blc => simp_all; exact .listApp ih1 ih2
  . case prod _ ih => match Alc with | .prod Alc => simp_all; exact .prod ih
  . case sum _ ih => match Alc with | .sum Alc => simp_all; exact .sum ih

theorem EqParallelReduction.TypeEquivalence_of (h: [[ Δ ⊢ A <≡>* B ]]) (wf: [[ ⊢ Δ ]]) (Alc: A.TypeVarLocallyClosed) : [[ Δ ⊢ A ≡ B ]] := by
  induction h with
  | refl => exact .refl Alc
  | step h => exact h.TypeEquivalence_of wf Alc
  | sym BA ih => exact ih (BA.preserve_lc.2 Alc) |>.symm
  | trans AB BC ih1 ih2 => exact (ih1 Alc).trans (ih2 <| AB.preserve_lc.1 Alc)

namespace TypeEquivalenceI

theorem ParallelReduction_of (h: [[ Δ ⊢ A ≡ᵢ B ]]) : [[ Δ ⊢ A <≡>* B ]] := by
  induction h
  case lamApp Abody Blc kinding => exact .lamApp (I := []) kinding (λ _ _ => .refl) .refl |> ParallelReduction.Equiv_of
  case lamListApp Alc Blc =>
    have := ParallelReduction.lamListApp

    constructor





local instance : Inhabited «Type» where
  default := .list []
in
def list' (As Bs: List «Type») (length_eq: As.length = Bs.length) (h : ∀A B, ⟨A, B⟩ ∈ As.zip Bs → [[ Δ ⊢ A ≡ᵢ B ]] )
  : TypeEquivalenceI Δ (.list As) (.list Bs) := by
  rw [← Std.Range.map_get!_eq (as := As), ← Std.Range.map_get!_eq (as := Bs), ← length_eq]
  apply list
  intro i mem
  apply h
  have := (As.zip Bs).get!_mem <| by
    rw [List.length_zip, ← length_eq, Nat.min_self]
    exact mem.upper
  rw [List.get!_zip length_eq mem.upper] at this
  exact this

theorem subst_rename' {a': TypeVarId}
  (h: [[ Δ, a: K, Δ' ⊢ A ≡ᵢ B ]]):
  [[ Δ, Δ'[a'/a] ⊢ A[a'/a] ≡ᵢ B[a'/a] ]] := by
  have a'lc: [[ (a') ]].TypeVarLocallyClosed := by constructor
  generalize Δ_eq: [[ (Δ, a: K, Δ') ]] = Δ_ at h
  induction h generalizing Δ Δ' <;> (try simp_all [Type.TypeVar_subst]) <;> subst Δ_eq <;> try aesop (add unsafe constructors TypeEquivalenceI)
  . case refl A lc => exact .refl (lc.TypeVar_subst a'lc)
  . case lamApp A B K' Abody Blc =>
    rw [a'lc.Type_open_TypeVar_subst_dist]
    exact .lamApp (Abody.TypeVar_subst <| a'lc.weaken (n := 1)) (Blc.TypeVar_subst a'lc)
  . case lamListApp A n B Alc Blc =>
    unfold Function.comp
    simp_all [Type.TypeVar_subst]
    exact .lamListApp (Alc.TypeVar_subst a'lc) (λi iltn => Blc i iltn |>.TypeVar_subst a'lc)
  . case listAppId A K' Alc => exact .listAppId (Alc.TypeVar_subst a'lc)
  . case lam K' A B I AB ih =>
    apply TypeEquivalenceI.lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a'' nin
    repeat rw [<- a'lc.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
  . case scheme K' A B I AB ih =>
    apply TypeEquivalenceI.scheme (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a'' nin
    repeat rw [<- a'lc.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
  . case listAppComp A₀ A₁ B K A₀lc A₁body Blc =>
    exact .listAppComp
      (A₀lc.TypeVar_subst a'lc)
      (A₁body.TypeVar_subst <| a'lc.weaken (n := 1))
      (Blc.TypeVar_subst a'lc)

theorem subst_rename {a': TypeVarId} (h: [[ Δ, a: K ⊢ A ≡ᵢ B ]]): [[ Δ ⊢ A[a'/a] ≡ᵢ B[a'/a] ]] :=
  subst_rename' (Δ' := [[ ε ]]) h

theorem weakening_type' (h: [[ Δ, Δ' ⊢ A ≡ᵢ B ]]) (fresh: a ∉ Δ.typeVarDom) : [[ Δ, a: K, Δ' ⊢ A ≡ᵢ B ]] := by
  generalize Δ_eq : [[ (Δ, Δ') ]] = Δ_ at h
  induction h generalizing Δ Δ' <;> subst Δ_eq <;> try aesop (add norm Type.freeTypeVars) (add unsafe constructors TypeEquivalenceI)
  . case lam K' A B I AB ih =>
    apply TypeEquivalenceI.lam (I := a :: I ++ Δ.typeVarDom)
    intro a' nin
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K')
    simp_all [Environment.append]
  . case scheme K' A B I AB ih =>
    apply TypeEquivalenceI.scheme (I := a :: I ++ Δ.typeVarDom)
    intro a' nin
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K')
    simp_all [Environment.append]

theorem weakening_type (h: [[ Δ ⊢ A ≡ᵢ B ]]) (fresh: a ∉ Δ.typeVarDom) : [[ Δ, a: K ⊢ A ≡ᵢ B ]] := weakening_type' (Δ' := [[ ε ]]) h fresh

theorem lam_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ᵢ B^a ]]): [[ Δ ⊢ (λ a : K. A) ≡ᵢ (λ a : K. B) ]] := by
  refine .lam (I := a :: Δ.typeVarDom) ?_
  intro a' notIn
  repeat1' rw [Type.TypeVar_open_eq_Type_open_var]
  repeat1' rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
  exact h.subst_rename.weakening_type (by simp_all)

theorem scheme_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ᵢ B^a ]]): [[ Δ ⊢ (∀ a : K. A) ≡ᵢ (∀ a : K. B) ]] := by
  refine .scheme (I := a :: Δ.typeVarDom) ?_
  intro a' notIn
  repeat1' rw [Type.TypeVar_open_eq_Type_open_var]
  repeat1' rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
  exact h.subst_rename.weakening_type (by simp_all)

open «Type» TypeVarLocallyClosed in
theorem regularity (h: [[ Δ ⊢ A ≡ᵢ B ]]): A.TypeVarLocallyClosed ∧ B.TypeVarLocallyClosed := by
  induction h
  case lam Δ K A B I AB ih =>
    have ⟨a, notIn⟩ := (I ++ A.freeTypeVars ++ B.freeTypeVars).exists_fresh
    have ⟨Alc, Blc⟩ := ih a (by simp_all)
    have Alc := Alc.TypeVar_close_inc (a := a); rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Alc
    have Blc := Blc.TypeVar_close_inc (a := a); rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Blc
    exact ⟨Alc.lam, Blc.lam⟩
  case scheme Δ K A B I AB ih =>
    have ⟨a, notIn⟩ := (I ++ A.freeTypeVars ++ B.freeTypeVars).exists_fresh
    have ⟨Alc, Blc⟩ := ih a (by simp_all)
    have Alc := Alc.TypeVar_close_inc (a := a); rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Alc
    have Blc := Blc.TypeVar_close_inc (a := a); rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Blc
    exact ⟨Alc.forall, Blc.forall⟩
  case listAppComp A₀ A₁ B Δ K A₀lc A₁body Blc =>
    exact ⟨A₀lc.listApp <| A₁body.lam.listApp Blc,  A₀lc.weaken (n:=1) |>.app A₁body |>.lam |>.listApp Blc⟩
  all_goals aesop (add safe constructors TypeVarLocallyClosed, safe TypeVarLocallyClosed.weaken, safe forward Type_open_dec, safe forward Std.Range.mem_of_mem_toList)

end TypeEquivalenceI

namespace TypeEquivalenceS

theorem sym (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ B ≡ₛ A ]] := by
  induction h with
  | base h => exact .symm h
  | symm h => exact .base h
  | trans _ _ ih1 ih2 => exact ih2.trans ih1

theorem regularity (h: [[ Δ ⊢ A ≡ₛ B ]]): A.TypeVarLocallyClosed ∧ B.TypeVarLocallyClosed := by
  induction h with
  | base h => exact h.regularity
  | symm h => exact ⟨h.regularity.2, h.regularity.1⟩
  | trans _ _ ih1 ih2 => simp_all

theorem lam_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ₛ B^a ]]): [[ Δ ⊢ (λ a : K. A) ≡ₛ (λ a : K. B) ]] := by
  generalize Aa_eq : [[ (A^a) ]] = Aa at h
  generalize Ba_eq : [[ (B^a) ]] = Ba at h
  induction h generalizing A B
  . case base h =>
    subst Aa_eq Ba_eq
    exact .base (TypeEquivalenceI.lam_intro_ex a fresh h)
  . case symm h =>
    subst Aa_eq Ba_eq
    exact .symm (TypeEquivalenceI.lam_intro_ex a (by simp_all) h)
  . case trans A_ B_ C_ AB BC ih1 ih2 =>
    subst Aa_eq Ba_eq
    have ⟨_, Blc⟩ := AB.regularity
    specialize ih1 (B := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) rfl (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc])
    specialize ih2 (A := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc]) rfl
    exact .trans ih1 ih2

theorem scheme_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ₛ B^a ]]): [[ Δ ⊢ (∀ a : K. A) ≡ₛ (∀ a : K. B) ]] := by
  generalize Aa_eq : [[ (A^a) ]] = Aa at h
  generalize Ba_eq : [[ (B^a) ]] = Ba at h
  induction h generalizing A B
  . case base h =>
    subst Aa_eq Ba_eq
    exact .base (TypeEquivalenceI.scheme_intro_ex a fresh h)
  . case symm h =>
    subst Aa_eq Ba_eq
    exact .symm (TypeEquivalenceI.scheme_intro_ex a (by simp_all) h)
  . case trans A_ B_ C_ AB BC ih1 ih2 =>
    subst Aa_eq Ba_eq
    have ⟨_, Blc⟩ := AB.regularity
    specialize ih1 (B := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) rfl (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc])
    specialize ih2 (A := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc]) rfl
    exact .trans ih1 ih2

private
theorem ctor1 {T: «Type» → «Type»} (h: [[ Δ ⊢ A ≡ₛ B ]]) (c: ∀{Δ A B}, [[ Δ ⊢ A ≡ᵢ B]] → TypeEquivalenceI Δ (T A) (T B) ) : TypeEquivalenceS Δ (T A) (T B) := by
  induction h with
  | base h => exact .base (c h)
  | symm h => exact .symm (c h)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem prod (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ ⊗ A ≡ₛ ⊗ B ]] := ctor1 h (.prod)
theorem sum (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ ⊕ A ≡ₛ ⊕ B ]] := ctor1 h (.sum)

private
theorem ctor2_left_refl {T: «Type» → «Type» → «Type»} (h: [[ Δ ⊢ A ≡ₛ A' ]]) (Clc: C.TypeVarLocallyClosed) (c: ∀{Δ A A' B B'}, [[ Δ ⊢ A ≡ᵢ A' ]] → [[ Δ ⊢ B ≡ᵢ B' ]] → TypeEquivalenceI Δ (T A B) (T A' B') ) : TypeEquivalenceS Δ (T C A) (T C A') := by
  induction h with
  | base h => exact .base (c (.refl Clc) h)
  | symm h => exact .symm (c (.refl Clc) h)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private
theorem ctor2 {T: «Type» → «Type» → «Type»} (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) (c: ∀{Δ A A' B B'}, [[ Δ ⊢ A ≡ᵢ A' ]] → [[ Δ ⊢ B ≡ᵢ B' ]] → TypeEquivalenceI Δ (T A B) (T A' B') ) : TypeEquivalenceS Δ (T A B) (T A' B') := by
  induction h1 <;> induction h2
  . case base.base h1 _ _ h2 => exact .base (c h1 h2)
  . case base.symm h1 _ _ h2 =>
    exact .trans
      (.symm (c (.refl h1.regularity.1) h2))
      (.base (c h1 (.refl h2.regularity.1)))
  . case base.trans h _ _ _ _ BC ih1 ih2 =>
    refine (.trans (.trans
      ih1
      (.symm (c h (.refl BC.regularity.1))))
      ih2)
  . case symm.base h1 _ _ h2 =>
    exact .trans
      (.base (c (.refl h1.regularity.2) h2))
      (.symm (c h1 (.refl h2.regularity.2)))
  . case symm.symm h1 _ _ h2 =>
    exact .trans
      (.symm (c (.refl h1.regularity.2) h2))
      (.symm (c h1 (.refl h2.regularity.1)))
  . case symm.trans h _ _ _ _ BC ih1 ih2 =>
    exact (.trans (.trans
      ih1
      (.base (c h (.refl BC.regularity.1))))
      ih2)
  . case trans.base BC _ _ h ih1 ih2 =>
    exact (.trans (.trans
      ih1
      (.symm (c (.refl BC.regularity.1) h)))
      ih2)
  . case trans.symm BC _ _ h ih1 ih2 =>
    exact (.trans (.trans
      ih1
      (.base (c (.refl BC.regularity.1) h)))
      ih2)
  . case trans.trans A T A' AT TA' B U B' BU UB' _ _ ih1 ih2 =>
    exact .trans (.trans
      ih1
      (ctor2_left_refl (BU.trans UB').sym AT.regularity.2 c))
      ih2

theorem app (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) : [[ Δ ⊢ A B ≡ₛ A' B' ]] := ctor2 h1 h2 (.app)
theorem arr (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) : [[ Δ ⊢ A → B ≡ₛ A' → B' ]] := ctor2 h1 h2 (.arr)
theorem listApp (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) : [[ Δ ⊢ A ⟦B⟧ ≡ₛ A' ⟦B'⟧ ]] := ctor2 h1 h2 (.listApp)

end TypeEquivalenceS

-- TODO use upstream version after we upgrade to latest lott
theorem _root_.Std.Range.mem_zip_map_append_cons {f g : Nat → α}
  (h : xy ∈ (([:m - (i + 1)].map f) ++ x :: [m - i:m].map g).zip (([:m - (i + 1)].map f) ++ y :: [m - i:m].map g))
  : (∃ j < m - (i + 1), xy.fst = f j ∧ xy.snd = f j) ∨
    (xy.fst = x ∧ xy.snd = y) ∨
    (∃ j, m - (i + 1) < j ∧ j < m ∧ xy.fst = g j ∧ xy.snd = g j) := sorry

open Std.Range in
theorem _root_.Std.Range.map_eq_cons_of_lt (mltn : m < n) : [m:n].map f = f m :: [m+1:n].map f := by
  rw [map, toList, if_pos mltn, List.map_cons, ← map]

open Std.Range in
theorem _root_.Std.Range.map_same_eq_nil : [n:n].map f = [] := by
  rw [map, toList, if_neg <| Nat.not_lt_of_le Nat.le.refl, List.map_nil]

open Std.Range in
theorem _root_.Std.Range.map_eq_snoc_of_lt (mltn : m < n) : [m:n].map f = [m:n - 1].map f ++ [f (n - 1)] := by
  let npos := Nat.lt_of_le_of_lt (Nat.zero_le _) mltn
  rw [map, ← map_append (l := m) (m := n - 1) (n := n) (Nat.le_sub_one_of_lt mltn) (Nat.sub_le _ _),
      ← map, ← map, map_eq_cons_of_lt <| Nat.sub_lt npos Nat.one_pos, Nat.sub_add_cancel npos,
      map_same_eq_nil]

theorem TypeEquivalence.TypeEquivalenceS_of (h: [[Δ ⊢ A ≡ B]]) : [[Δ ⊢ A ≡ₛ B]] := by
  induction h
  . case refl lc => exact .base (.refl lc)
  . case lamApp Abody Blc => exact .base (.lamApp Abody Blc)
  . case lamListApp Alc Blc => exact .base (.lamListApp Alc Blc)
  . case listAppId Alc => exact .base (.listAppId Alc)
  . case lam Δ K A B I h ih =>
    have ⟨a, nin⟩ := I ++ Δ.typeVarDom ++ A.freeTypeVars ++ B.freeTypeVars |>.exists_fresh
    specialize ih a (by simp_all)
    clear h
    generalize Aa_eq: [[ (A^a) ]] = Aa at ih
    generalize Ba_eq: [[ (B^a) ]] = Ba at ih
    generalize Δ_eq : [[(Δ, a:K)]] = Δ_ at ih
    induction ih generalizing A B Δ
    . case base h =>
      subst Aa_eq Ba_eq Δ_eq
      refine TypeEquivalenceS.lam_intro_ex a (by simp_all) (.base h)
    . case symm h =>
      subst Aa_eq Ba_eq Δ_eq
      refine TypeEquivalenceS.lam_intro_ex a (by simp_all) (.symm h)
    . case trans A_ B_ C_ AB _ ih1 ih2 =>
      have ⟨_, Blc⟩ := AB.regularity
      subst Aa_eq Ba_eq Δ_eq
      specialize ih1 (B := [[\a^B_]]) (by simp_all; exact Type.not_mem_freeTypeVars_TypeVar_close) rfl (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc]) rfl
      specialize ih2 (A := [[\a^B_]]) (by simp_all; exact Type.not_mem_freeTypeVars_TypeVar_close) (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc]) rfl rfl
      exact .trans ih1 ih2
  . case app A1 A2 B1 B2 h1 h2 ih1 ih2 => exact ih1.app ih2
  . case scheme Δ K A B I h ih =>
    have ⟨a, nin⟩ := I ++ Δ.typeVarDom ++ A.freeTypeVars ++ B.freeTypeVars |>.exists_fresh
    specialize ih a (by simp_all)
    clear h
    generalize Aa_eq: [[ (A^a) ]] = Aa at ih
    generalize Ba_eq: [[ (B^a) ]] = Ba at ih
    generalize Δ_eq : [[(Δ, a:K)]] = Δ_ at ih
    induction ih generalizing A B Δ
    . case base h =>
      subst Aa_eq Ba_eq Δ_eq
      refine TypeEquivalenceS.scheme_intro_ex a (by simp_all) (.base h)
    . case symm h =>
      subst Aa_eq Ba_eq Δ_eq
      refine TypeEquivalenceS.scheme_intro_ex a (by simp_all) (.symm h)
    . case trans A_ B_ C_ AB _ ih1 ih2 =>
      have ⟨_, Blc⟩ := AB.regularity
      subst Aa_eq Ba_eq Δ_eq
      specialize ih1 (B := [[\a^B_]]) (by simp_all; exact Type.not_mem_freeTypeVars_TypeVar_close) rfl (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc]) rfl
      specialize ih2 (A := [[\a^B_]]) (by simp_all; exact Type.not_mem_freeTypeVars_TypeVar_close) (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc]) rfl rfl
      exact .trans ih1 ih2
  . case arr ih1 ih2 => exact ih1.arr ih2
  . case list n Δ A B h ih =>
    clear h
    have : ([:n].map fun i => B i) = ([:n - n].map fun i => A i) ++ [n - n:n].map fun i => B i := by
      have : ([:0].map fun i => A i) = [] := by
        rw [Std.Range.map, Std.Range.toList, if_neg nofun, List.map_nil]
      rw [Nat.sub_self, this, List.nil_append]
    rw [this]
    generalize neqm : n = m
    let nlem := Nat.le_refl n
    rw (occs := .pos [3, 5]) [← neqm]
    rw [neqm] at ih
    rw (occs := .pos [2]) [neqm] at nlem
    clear neqm this
    induction n with
    | zero =>
      rw [Nat.sub_zero]
      rw (occs := .pos [3]) [Std.Range.map]
      rw [Std.Range.toList, if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_nil, List.append_nil]
      refine .base <| .refl ?_
      . refine .list (λAi mem => ?_)
        have ⟨i, iltm, eq⟩ := Std.Range.mem_of_mem_map mem; subst eq
        exact ih i iltm |>.regularity.1
    | succ i ih' =>
      generalize A'eq : A (m - (i + 1)) = A', B'eq : B (m - (i + 1)) = B' at *
      let ih'' := ih (m - (i + 1)) (by simp_all [Membership.mem]; omega)
      specialize ih' <| Nat.le_of_add_right_le nlem
      rw [A'eq, B'eq] at ih''
      rw [Std.Range.map, ← Std.Range.map_append (Nat.zero_le _) (Nat.sub_le _ i),
          ← Std.Range.map, ← Std.Range.map, Std.Range.map_eq_snoc_of_lt (by omega), Nat.sub_sub,
          List.append_assoc, List.singleton_append, A'eq] at ih' ⊢
      rw [List.append_assoc, List.singleton_append] at ih'
      rw (occs := .pos [4]) [Std.Range.map_eq_cons_of_lt (by omega)]
      rw [B'eq]
      rw (occs := .pos [3]) [Nat.sub_add_eq]
      rw [Nat.sub_add_cancel (by omega)]
      clear A'eq B'eq
      apply TypeEquivalenceS.trans ih'
      clear ih'
      induction ih'' with
      | base h =>
        refine .base <| .list' _ _ (by simp_all) (λ _ _ mem => ?_)
        match Std.Range.mem_zip_map_append_cons mem with
        | .inl ⟨j, jlt, Aeq, Beq⟩ =>
          subst Aeq Beq
          refine .refl ?_
          . exact ih j (by simp_all [Membership.mem]; omega) |>.regularity.1
        | .inr (.inl ⟨Aeq, Beq⟩) =>
          subst Aeq Beq
          exact h
        | .inr (.inr ⟨j, ltj, jlt, Aeq, Beq⟩) =>
          subst Aeq Beq
          refine .refl ?_
          . exact ih j (by simp_all [Membership.mem]; omega) |>.regularity.2
      | symm h =>
        refine .symm <| .list' _ _ (by simp_all) (λ _ _ mem => ?_)
        match Std.Range.mem_zip_map_append_cons mem with
        | .inl ⟨j, jlt, Aeq, Beq⟩ =>
          subst Aeq Beq
          refine .refl ?_
          . exact ih j (by simp_all [Membership.mem]; omega) |>.regularity.1
        | .inr (.inl ⟨Aeq, Beq⟩) =>
          subst Aeq Beq
          exact h
        | .inr (.inr ⟨j, ltj, jlt, Aeq, Beq⟩) =>
          subst Aeq Beq
          refine .refl ?_
          . exact ih j (by simp_all [Membership.mem]; omega) |>.regularity.2
      | trans h h' ih'' ih''' =>
        exact .trans ih'' ih'''
  . case listApp ih1 ih2 => exact ih1.listApp ih2
  . case listAppComp A₀lc A₁body Blc => exact .base (.listAppComp A₀lc A₁body Blc)
  . case prod Δ A B h ih => exact ih.prod
  . case sum ih => exact ih.sum
  . case symm _ _ _ _ ih =>  exact ih.sym
  . case trans _ _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

theorem TypeEquivalenceS.ParallelReduction_of (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ A <≡>* B ]] := by
  induction h with
  | base h =>
  | symm h => exact .symm h.ParallelReduction

namespace TypeEquivalence

theorem EqParallelReduction_of (eq: [[Δ ⊢ A ≡ B]]) : [[Δ ⊢ A <≡>* B]] := sorry

theorem weakening (equiv: [[ Δ, Δ'' ⊢ A ≡ B ]]) (wfτ: [[ ⊢τ Δ, Δ', Δ'' ]]) : [[ Δ, Δ', Δ'' ⊢ A ≡ B ]] :=
  -- equiv.EqParallelReduction_of |>.weakening wfτ |>.TypeEquivalence_of
  -- TODO add lc precondition
  sorry

theorem subst' {A T T' : «Type»} (equiv : [[ Δ, a: K, Δ' ⊢ T ≡ T' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡ T'[A/a] ]] :=
  -- equiv.EqParallelReduction_of |>.subst_out' wf kindA |>.TypeEquivalence_of
  -- TODO add lc precondition
  sorry

-- TODO this is not dt so properties on typing apparently have nothing to do with terms in env
theorem TermVar_drop (equiv: [[ Δ, x: T, Δ'' ⊢ A ≡ B ]]): [[ Δ, Δ'' ⊢ A ≡ B ]] := sorry

end TypeEquivalence

end TabularTypeInterpreter.«F⊗⊕ω»
