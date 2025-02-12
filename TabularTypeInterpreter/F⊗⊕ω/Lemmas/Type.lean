import Aesop
import TabularTypeInterpreter.Data.Range
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace «Type»

@[elab_as_elim]
def rec_uniform {motive : «Type» → Prop} (var : ∀ a : TypeVar, motive (var a))
  (lam : ∀ K A, motive A → motive (lam K A)) (app : ∀ A B, motive A → motive B → motive (app A B))
  («forall» : ∀ K A, motive A → motive («forall» K A))
  (arr : ∀ A B, motive A → motive B → motive (arr A B))
  (list : ∀ As, (∀ A ∈ As, motive A) → motive (list As))
  (listApp : ∀ A B, motive A → motive B → motive (listApp A B))
  (prod : ∀ A, motive A → motive (prod A)) (sum : ∀ A, motive A → motive (sum A)) (A : «Type»)
  : motive A :=
  rec (motive_1 := motive) var lam app «forall» arr list listApp prod sum (fun _ => (nomatch ·))
    (fun _ _ ih₀ ih₁ _ mem => match mem with | .head _ => ih₀ | .tail _ mem' => ih₁ _ mem') A

@[simp]
theorem TypeVar_open_sizeOf (A : «Type») : sizeOf (A.TypeVar_open a n) = sizeOf A := by
  match A with
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h' =>
      dsimp only [sizeOf]
      rw [← h', _sizeOf_1, _sizeOf_1]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | var (.free _) =>
    rw [TypeVar_open]
    split <;> rfl
  | lam _ A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
  | app A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _),
        rev (B.TypeVar_open _ _), rev A', rev B, A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | «forall» _ A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
  | arr A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _),
        rev (B.TypeVar_open _ _), rev A', rev B, A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | list A's =>
    match A's with
    | [] =>
      rw [TypeVar_open]
      show sizeOf (list []) = _
      dsimp only [sizeOf]
    | A' :: A's' =>
      rw [TypeVar_open]
      show sizeOf (list (_ :: _)) = _
      dsimp only [sizeOf]
      rw [_sizeOf_1, _sizeOf_1]
      simp only
      rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_2, ← _sizeOf_2, rev (A'.TypeVar_open _ _), rev A',
          A'.TypeVar_open_sizeOf]
      have h := (list A's').TypeVar_open_sizeOf (a := a) (n := n)
      dsimp only [sizeOf] at h
      rw [TypeVar_open, _sizeOf_1, _sizeOf_1] at h
      simp only at h
      rw [← _sizeOf_2, ← _sizeOf_2, Nat.add_comm, Nat.add_comm (m := _sizeOf_2 A's')] at h
      rw [Nat.add_one_inj.mp h]
  | listApp A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _),
        rev (B.TypeVar_open _ _), rev A', rev B, A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | prod A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
  | sum A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
where
  rev : ∀ a : «Type», a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]

theorem Type_open_var {T: «Type»} : T.TypeVar_open a n = T.Type_open (var (TypeVar.free a)) n := by
  induction T using rec_uniform generalizing n <;> aesop (rule_sets := [topen])

theorem TypeVar_open_comm (A : «Type»)
  : m ≠ n → (A.TypeVar_open a m).TypeVar_open a' n = (A.TypeVar_open a' n).TypeVar_open a m := by
  induction A using rec_uniform generalizing m n <;> aesop (add simp TypeVar_open)

theorem TypeVar_open_eq_Type_open_var : TypeVar_open A a n = A.Type_open (.var a) n := by
  induction A using rec_uniform generalizing n <;> aesop (add simp [TypeVar_open, Type_open])

theorem TypeVar_close_eq_of_not_mem_freeTypeVars
  : a ∉ freeTypeVars A → A.TypeVar_close a n = A := by
  induction A using rec_uniform generalizing n <;> aesop (add simp [freeTypeVars, TypeVar_close])

theorem TypeVar_subst_id_of_not_mem_freeTypeVars
  : a ∉ freeTypeVars A → A.TypeVar_subst a B = A := by
  induction A using rec_uniform <;> aesop (add simp [freeTypeVars, TypeVar_subst])

theorem TypeVar_subst_intro_of_not_mem_freeTypeVars {A: «Type»}: a ∉ A.freeTypeVars → (A.TypeVar_open a n).TypeVar_subst a B = A.Type_open B n := by
  induction A using «Type».rec_uniform generalizing B n <;>
    aesop (add norm TypeVar_subst, norm TypeVar_open, norm Type_open, norm freeTypeVars, norm TypeVar_open)

theorem TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars
  : a ∉ freeTypeVars A → (A.TypeVar_open a n).TypeVar_close a n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [freeTypeVars, TypeVar_open, TypeVar_close],
      safe List.map_eq_id_of_eq_id_of_mem)

theorem TypeVar_open_not_mem_freeTypeVars_preservation_of_ne
  : a ≠ a' → a ∉ freeTypeVars A → a ∉ (A.TypeVar_open a' n).freeTypeVars := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, freeTypeVars], safe cases TypeVar)

set_option maxHeartbeats 2000000 in
theorem TypeVar_open_inj_of_not_mem_freeTypeVars (aninA : a ∉ freeTypeVars A)
  (aninB : a ∉ freeTypeVars B) (eq : A.TypeVar_open a n = B.TypeVar_open a n) : A = B := by
  induction A using rec_uniform generalizing B n <;>
    induction B using rec_uniform <;> aesop
    (add simp [TypeVar_open, freeTypeVars], safe cases TypeVar, 10% List.eq_of_map_eq_map_of_inj)

theorem not_mem_freeTypeVars_TypeVar_close : a ∉ (TypeVar_close A a n).freeTypeVars := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_close, freeTypeVars], safe cases TypeVar)

theorem not_mem_freeTypeVars_TypeVar_open_intro
  : a ∉ freeTypeVars A → a ≠ a' → a ∉ (A.TypeVar_open a' n).freeTypeVars := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, freeTypeVars], safe cases TypeVar)

theorem not_mem_freeTypeVars_Type_open_intro
  : a ∉ freeTypeVars A → a ∉ freeTypeVars B → a ∉ (A.Type_open B n).freeTypeVars := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [Type_open, freeTypeVars], safe cases TypeVar)

theorem not_mem_freeTypeVars_TypeVar_open_drop
  : a ∉ (TypeVar_open A a' n).freeTypeVars → a ∉ A.freeTypeVars := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, freeTypeVars], safe cases TypeVar)

namespace TypeVarLocallyClosed

theorem weaken {A : «Type»} : A.TypeVarLocallyClosed m → A.TypeVarLocallyClosed (m + n)
  | var_free => var_free
  | var_bound h => var_bound <| Nat.lt_add_right _ h
  | lam A'lc => by
    have := A'lc.weaken (n := n)
    rw [Nat.add_assoc, Nat.add_comm (n := 1), ← Nat.add_assoc] at this
    exact this.lam
  | app A'lc Blc => app A'lc.weaken Blc.weaken
  | «forall» A'lc => by
    have := A'lc.weaken (n := n)
    rw [Nat.add_assoc, Nat.add_comm (n := 1), ← Nat.add_assoc] at this
    exact this.forall
  | arr A'lc Blc => arr A'lc.weaken Blc.weaken
  | list A'lc => list (A'lc · · |>.weaken)
  | listApp A'lc Blc => listApp A'lc.weaken Blc.weaken
  | prod A'lc => prod A'lc.weaken
  | sum A'lc => sum A'lc.weaken

theorem strengthen {A : «Type»}
  : A.TypeVarLocallyClosed (n + 1) → (A.TypeVar_open a n).TypeVarLocallyClosed n := by
  induction A using rec_uniform
    generalizing n <;> aesop
    (add simp TypeVar_open, 20% cases TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed,
      20% apply [Nat.lt_of_le_of_ne, Nat.le_of_lt_succ])

theorem Type_open_drop (h : m < n) (Aoplc : (Type_open A B m).TypeVarLocallyClosed n)
  : A.TypeVarLocallyClosed n := by match A with
  | .var _ =>
    rw [Type_open] at Aoplc
    split at Aoplc
    · case isTrue h' =>
      rw [← h']
      exact var_bound h
    · case isFalse h' => exact Aoplc
  | .lam .. =>
    rw [Type_open] at Aoplc
    let .lam A'oplc := Aoplc
    exact lam <| A'oplc.Type_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .app A' B =>
    rw [Type_open] at Aoplc
    let .app A'oplc Boplc := Aoplc
    exact app (A'oplc.Type_open_drop h) (Boplc.Type_open_drop h)
  | .forall .. =>
    rw [Type_open] at Aoplc
    let .forall A'oplc := Aoplc
    exact «forall» <| A'oplc.Type_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .arr .. =>
    rw [Type_open] at Aoplc
    let .arr A'oplc Boplc := Aoplc
    exact arr (A'oplc.Type_open_drop h) (Boplc.Type_open_drop h)
  | .list A's =>
    rw [Type_open] at Aoplc
    match h' : A's with
    | [] => exact .list fun _ => (nomatch ·)
    | A' :: A's' =>
      apply list
      intro A'' A''in
      let .list A'oplc := Aoplc
      match A''in with
      | .head _ => exact A'oplc (A''.Type_open _ _) (.head _) |>.Type_open_drop h
      | .tail _ A''inA's' =>
        have := list <| fun A''' A'''in => A'oplc A''' <| .tail _ A'''in
        rw [← Type_open] at this
        let .list A's'lc := this.Type_open_drop h
        exact A's'lc A'' A''inA's'
  | .listApp A' B =>
    rw [Type_open] at Aoplc
    let .listApp A'oplc Boplc := Aoplc
    exact listApp (A'oplc.Type_open_drop h) (Boplc.Type_open_drop h)
  | .prod A' =>
    rw [Type_open] at Aoplc
    let .prod A'oplc := Aoplc
    exact prod <| A'oplc.Type_open_drop h
  | .sum A' =>
    rw [Type_open] at Aoplc
    let .sum A'oplc := Aoplc
    exact sum <| A'oplc.Type_open_drop h
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · apply Nat.le_of_lt
    apply List.sizeOf_lt_of_mem
    have : A's = A' :: A's' := by assumption
    cases this
    exact A''in
  · have : A's = A' :: A's' := by assumption
    cases this
    simp_arith

theorem TypeVar_open_drop {A : «Type»} (h : m < n)
  (Aoplc : (A.TypeVar_open a m).TypeVarLocallyClosed n) : A.TypeVarLocallyClosed n := by
  match A with
  | .var _ =>
    rw [TypeVar_open] at Aoplc
    split at Aoplc
    · case isTrue h' =>
      rw [← h']
      exact var_bound h
    · case isFalse h' => exact Aoplc
  | .lam .. =>
    rw [TypeVar_open] at Aoplc
    let .lam A'oplc := Aoplc
    exact lam <| A'oplc.TypeVar_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .app A' B =>
    rw [TypeVar_open] at Aoplc
    let .app A'oplc Boplc := Aoplc
    exact app (A'oplc.TypeVar_open_drop h) (Boplc.TypeVar_open_drop h)
  | .forall .. =>
    rw [TypeVar_open] at Aoplc
    let .forall A'oplc := Aoplc
    exact «forall» <| A'oplc.TypeVar_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .arr .. =>
    rw [TypeVar_open] at Aoplc
    let .arr A'oplc Boplc := Aoplc
    exact arr (A'oplc.TypeVar_open_drop h) (Boplc.TypeVar_open_drop h)
  | .list A's =>
    rw [TypeVar_open] at Aoplc
    match h' : A's with
    | [] => exact .list fun _ => (nomatch ·)
    | A' :: A's' =>
      apply list
      intro A'' A''in
      let .list A'oplc := Aoplc
      match A''in with
      | .head _ => exact A'oplc (A''.TypeVar_open _ _) (.head _) |>.TypeVar_open_drop h
      | .tail _ A''inA's' =>
        have := list <| fun A''' A'''in => A'oplc A''' <| .tail _ A'''in
        rw [← TypeVar_open] at this
        let .list A's'lc := this.TypeVar_open_drop h
        exact A's'lc A'' A''inA's'
  | .listApp A' B =>
    rw [TypeVar_open] at Aoplc
    let .listApp A'oplc Boplc := Aoplc
    exact listApp (A'oplc.TypeVar_open_drop h) (Boplc.TypeVar_open_drop h)
  | .prod A' =>
    rw [TypeVar_open] at Aoplc
    let .prod A'oplc := Aoplc
    exact prod <| A'oplc.TypeVar_open_drop h
  | .sum A' =>
    rw [TypeVar_open] at Aoplc
    let .sum A'oplc := Aoplc
    exact sum <| A'oplc.TypeVar_open_drop h
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · apply Nat.le_of_lt
    apply List.sizeOf_lt_of_mem
    have : A's = A' :: A's' := by assumption
    cases this
    exact A''in
  · have : A's = A' :: A's' := by assumption
    cases this
    simp_arith

theorem TypeVar_open_eq {A : «Type»} (Alc : A.TypeVarLocallyClosed n) : A.TypeVar_open a n = A := by
  match A with
  | var (.free _) => rw [TypeVar_open, if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      cases h
      let .var_bound nltn := Alc
      nomatch Nat.ne_of_lt nltn
    · case isFalse => rfl
  | .lam .. => let .lam A'lc := Alc; rw [TypeVar_open, A'lc.TypeVar_open_eq]
  | .app .. =>
    let .app A'lc Blc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq, Blc.TypeVar_open_eq]
  | .forall .. =>
    let .forall A'lc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq]
  | .arr .. =>
    let .arr A'lc Blc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq, Blc.TypeVar_open_eq]
  | .list A's =>
    match h : A's with
    | [] => rw [TypeVar_open]; rfl
    | A' :: A's' =>
      let .list A'slc := Alc
      rw [TypeVar_open]
      apply (Type.list.injEq _ _).mpr
      show (_ :: _) = _
      apply (List.cons.injEq _ _ _ _).mpr
      constructor
      · exact A'slc A' (.head _) |>.TypeVar_open_eq
      · have := TypeVar_open_eq (A := .list A's') (a := a) (n := n) <| .list ?h
        rw [TypeVar_open] at this
        apply Type.list.inj this
        intro A'' A''in
        exact A'slc A'' <| .tail _ A''in
  | .listApp .. =>
    let .listApp A'lc Blc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq, Blc.TypeVar_open_eq]
  | .prod .. => let .prod A'lc := Alc; rw [TypeVar_open, A'lc.TypeVar_open_eq]
  | .sum .. => let .sum A'lc := Alc; rw [TypeVar_open, A'lc.TypeVar_open_eq]

theorem Type_open_id : TypeVarLocallyClosed A n → A.Type_open B n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [Type_open], safe cases TypeVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)

theorem TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed A n → (A.TypeVar_close a n).TypeVar_open a n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, TypeVar_close], 40% cases TypeVarLocallyClosed,
      safe List.map_eq_id_of_eq_id_of_mem)

theorem Type_open_var_TypeVar_close_id
  : TypeVarLocallyClosed A n → (A.TypeVar_close a n).Type_open (.var a) n = A := by
  rw [← TypeVar_open_eq_Type_open_var]
  exact TypeVar_open_TypeVar_close_id

theorem Type_open_TypeVar_open_comm
  : TypeVarLocallyClosed B n → m ≠ n →
    (Type_open A B m).TypeVar_open a n = (A.TypeVar_open a n).Type_open B m := by
  induction A using rec_uniform generalizing m n <;> aesop
    (add simp [Type_open, TypeVar_open], 40% TypeVar_open_eq, safe weaken)

theorem Type_open_TypeVar_open_eq
  : TypeVarLocallyClosed B n → (Type_open A B n).TypeVar_open a n = A.Type_open B n := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [Type_open, TypeVar_open], 40% TypeVar_open_eq, safe weaken)

theorem Type_open_intro (Alc : A.TypeVarLocallyClosed n) (Blc : B.TypeVarLocallyClosed n)
  : (Type_open A B m).TypeVarLocallyClosed n := by
  induction Alc generalizing m <;> aesop
    (add simp Type.Type_open, safe constructors TypeVarLocallyClosed, 40% weaken)

theorem Type_open_dec (Alc : TypeVarLocallyClosed A (n + 1)) (Blc : B.TypeVarLocallyClosed n)
  : (Type_open A B n).TypeVarLocallyClosed n := by
  match A with
  | .var (.bound _) =>
    rw [Type_open]
    split
    · case _ => exact Blc
    · case _ h =>
      let .var_bound lt := Alc
      exact var_bound <| Nat.lt_of_le_of_ne (Nat.le_of_lt_succ lt) <|
        Ne.symm (h <| TypeVar.bound.injEq .. |>.mpr ·)
  | .var (.free _) =>
    rw [Type_open]
    exact var_free
  | .lam .. =>
    rw [Type_open]
    let .lam A'lc := Alc
    exact lam <| A'lc.Type_open_dec Blc.weaken
  | .app .. =>
    rw [Type_open]
    let .app A'lc B'lc := Alc
    exact app (A'lc.Type_open_dec Blc) (B'lc.Type_open_dec Blc)
  | .forall .. =>
    rw [Type_open]
    let .forall A'lc := Alc
    exact «forall» <| A'lc.Type_open_dec Blc.weaken
  | .arr .. =>
    rw [Type_open]
    let .arr A'lc B'lc := Alc
    exact arr (A'lc.Type_open_dec Blc) (B'lc.Type_open_dec Blc)
  | .list .. =>
    let .list Aslc := Alc
    rw [Type_open, List.mapMem_eq_map]
    exact list fun A' mem => by
      let ⟨A'', mem', eq⟩ := List.mem_map.mp mem
      cases eq
      exact Aslc A'' mem' |>.Type_open_dec Blc
  | .listApp .. =>
    rw [Type_open]
    let .listApp A'lc B'lc := Alc
    exact listApp (A'lc.Type_open_dec Blc) (B'lc.Type_open_dec Blc)
  | .prod .. =>
    rw [Type_open]
    let .prod A'lc := Alc
    exact prod <| A'lc.Type_open_dec Blc
  | .sum .. =>
    rw [Type_open]
    let .sum A'lc := Alc
    exact sum <| A'lc.Type_open_dec Blc

theorem Type_open_TypeVar_close_eq_TypeVar_subst
  : TypeVarLocallyClosed A n → (A.TypeVar_close a n).Type_open B n = A.TypeVar_subst a B := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_close, Type_open, TypeVar_subst], safe cases TypeVarLocallyClosed)

private
theorem Type_open_id' : TypeVarLocallyClosed A n → A = A.Type_open B n := (Type_open_id · |>.symm)

theorem Type_open_TypeVar_subst_dist
  : TypeVarLocallyClosed B' n → (Type_open A B n).TypeVar_subst a B' =
    (A.TypeVar_subst a B').Type_open (B.TypeVar_subst a B') n := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [Type_open, TypeVar_subst], 40% Type_open_id', 40% weaken)

theorem TypeVar_close_inc {A: «Type»} (Alc: A.TypeVarLocallyClosed n): (A.TypeVar_close a n).TypeVarLocallyClosed (n + 1) := by
  induction A using «Type».rec_uniform generalizing n <;> aesop
    (add norm Type.TypeVar_close, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed, unsafe weaken)

theorem TypeVar_subst {A B: «Type»} (Alc: A.TypeVarLocallyClosed n) (Blc: B.TypeVarLocallyClosed n): (A.TypeVar_subst a B).TypeVarLocallyClosed n := by
  induction Alc <;> aesop (add norm Type.TypeVar_subst, norm weaken, safe TypeVarLocallyClosed)

theorem modus_ponens_open {A B: «Type»} (lc: A.TypeVarLocallyClosed (n+1)) (mp: ∀a ∉ (I: List _), (A.TypeVar_open a n).TypeVarLocallyClosed n → (B.TypeVar_open a n).TypeVarLocallyClosed n): B.TypeVarLocallyClosed (n + 1) := by
  have ⟨a', notInI'⟩ := (I ++ B.freeTypeVars).exists_fresh
  have Alc := lc.strengthen (a:=a')
  have Blc := mp a' (by simp_all) Alc
  apply TypeVar_close_inc (a := a') at Blc
  rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Blc
  exact Blc

private
theorem of_aux : TypeVarLocallyClosed_aux A → A.TypeVarLocallyClosed := by
  intro lc
  match lc with
  | .var_free => exact .var_free
  | .lam Aoplc (I := I) =>
    let ⟨a, anin⟩ := I.exists_fresh
    exact .lam <| Aoplc a anin |> of_aux |>.weaken (n := 1) |>.TypeVar_open_drop Nat.one_pos
  | .app A'lc Blc => exact .app (of_aux A'lc) (of_aux Blc)
  | .forall Aoplc (I := I) =>
    let ⟨a, anin⟩ := I.exists_fresh
    exact .forall <| Aoplc a anin |> of_aux |>.weaken (n := 1) |>.TypeVar_open_drop Nat.one_pos
  | .arr A'lc Blc =>
    exact .arr (of_aux A'lc) (of_aux Blc)
  | .list Aslc =>
    apply TypeVarLocallyClosed.list
    intro A Amem
    exact Aslc A Amem |> of_aux
  | .listApp A'lc Blc => exact .listApp (of_aux A'lc) (of_aux Blc)
  | .prod A'lc => exact .prod (of_aux A'lc)
  | .sum A'lc => exact .sum (of_aux A'lc)

private
theorem aux_of : TypeVarLocallyClosed A → TypeVarLocallyClosed_aux A := by
  intro lcat
  match lcat with
  | .var_free => exact .var_free
  | .var_bound h => nomatch Nat.not_lt_zero _ h
  | .lam Alcat =>
    exact .lam (I := []) fun _ _ => Alcat.strengthen.aux_of
  | .app A'lcat Blcat =>
    exact .app A'lcat.aux_of Blcat.aux_of
  | .forall Alcat =>
    exact .forall (I := []) fun _ _ => Alcat.strengthen.aux_of
  | .arr A'lcat Blcat =>
    exact .arr A'lcat.aux_of Blcat.aux_of
  | .list Aslcat =>
    apply TypeVarLocallyClosed_aux.list
    intro A Amem
    exact Aslcat A Amem |>.aux_of
  | .listApp A'lcat Blcat => exact .listApp A'lcat.aux_of Blcat.aux_of
  | .prod A'lcat => exact .prod A'lcat.aux_of
  | .sum A'lcat => exact .sum A'lcat.aux_of

-- thank you matthew!!!
theorem aux_iff : (TypeVarLocallyClosed_aux A ↔ A.TypeVarLocallyClosed) := ⟨of_aux, aux_of⟩

end TypeVarLocallyClosed


theorem subst_open_var {T A: «Type»} (neq: x ≠ y) (lc: A.TypeVarLocallyClosed n): (T.TypeVar_open y n).TypeVar_subst x A = (T.TypeVar_subst x A).TypeVar_open y n := sorry


theorem subst_close_var {T A: «Type»} (neq: x ≠ y) (fresh: y ∉ A.freeTypeVars): (T.TypeVar_close y n).TypeVar_subst x A = (T.TypeVar_subst x A).TypeVar_close y n := sorry


theorem subst_fresh {A T : «Type»} (fresh: a ∉ A.freeTypeVars) : a ∉ (T.TypeVar_subst a A |>.freeTypeVars) := sorry


theorem subst_fresh' {A T: «Type»} (freshA: a ∉ A.freeTypeVars) (freshT: a ∉ T.freeTypeVars) : a ∉ (T.TypeVar_subst a' A |>.freeTypeVars) := sorry -- TODO by induction on T

end «Type»

namespace Kinding

theorem TypeVarLocallyClosed_of : [[Δ ⊢ A : K]] → A.TypeVarLocallyClosed 0 := fun Aki =>
  match A, Aki with
  | _, var .. => .var_free
  | .lam K A', .lam A'opki (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'opki a anin |>.TypeVarLocallyClosed_of
    exact .lam <| this.weaken.TypeVar_open_drop <| Nat.lt_succ_self _
  | .app A' B, .app A'opki Bopki =>
    .app A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .forall K A', .scheme A'opki (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'opki a anin |>.TypeVarLocallyClosed_of
    exact .forall <| this.weaken.TypeVar_open_drop <| Nat.lt_succ_self _
  | .arr A' B, .arr A'opki Bopki =>
    .arr A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .list A', Aki =>
    let .list A'opki (A := A'') := Aki
    .list fun A''' A'''in => by
      rw [List.map_singleton_flatten] at A'''in
      let ⟨i, mem, A'''eq⟩ := Std.Range.mem_of_mem_map A'''in
      cases A'''eq
      exact A'opki i mem |>.TypeVarLocallyClosed_of
  | .listApp A' B, .listApp A'opki Bopki =>
    .listApp A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .prod A', .prod A'opki => .prod A'opki.TypeVarLocallyClosed_of
  | .sum A', .sum A'opki => .sum A'opki.TypeVarLocallyClosed_of
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  rw [List.map_singleton_flatten]
  apply Nat.le_of_lt
  exact List.sizeOf_lt_of_mem A'''in

theorem not_mem_freeTypeVars_of (Aki : [[Δ ⊢ A : K]]) (aninΔ : [[a ∉ dom(Δ)]])
  : a ∉ A.freeTypeVars := by match Aki with
  | .var a'inΔ =>
    rw [Type.freeTypeVars]
    apply List.not_mem_singleton.mpr
    intro aeqa'
    cases aeqa'
    nomatch aninΔ a'inΔ.TypeVarInDom_of
  | .lam I A'opki | .scheme I A'opki =>
    let ⟨a', a'nin⟩ := a :: I |>.exists_fresh
    let ⟨a'nea, a'ninI⟩ := List.not_mem_cons.mp a'nin
    rw [Type.freeTypeVars]
    exact Type.not_mem_freeTypeVars_TypeVar_open_drop <|
      A'opki a' a'ninI |>.not_mem_freeTypeVars_of (List.not_mem_cons.mpr ⟨a'nea.symm, aninΔ⟩)
  | .app A'ki Bki | .arr A'ki Bki | .listApp A'ki Bki =>

    rw [Type.freeTypeVars]
    exact List.not_mem_append'.mpr ⟨
      A'ki.not_mem_freeTypeVars_of aninΔ,
      Bki.not_mem_freeTypeVars_of aninΔ
    ⟩
  | .list Aski =>
    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_singleton_flatten, List.map_map]
    apply List.not_mem_flatten.mpr
    intro as mem
    let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
    cases eq
    exact Aski i mem' |>.not_mem_freeTypeVars_of aninΔ
  | .prod A'ki | .sum A'ki =>
    rw [Type.freeTypeVars]
    exact A'ki.not_mem_freeTypeVars_of aninΔ
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  rw [List.map_singleton_flatten]
  apply Nat.le_of_lt
  exact List.sizeOf_lt_of_mem <| Std.Range.mem_map_of_mem mem'

theorem Type_open_preservation {A : «Type»}
  (Aki : Kinding [[(Δ, a : K, Δ')]] (A.TypeVar_open a n) K') (aninfvA : a ∉ A.freeTypeVars)
  (Bki : [[Δ ⊢ B : K]]) : Kinding [[(Δ, (Δ' [B / a]))]] (A.Type_open B n) K' := sorry

open Environment TypeVarInEnvironment in
theorem weakening_r' (kT: [[ Δ, Δ'' ⊢ T: K ]]) (fresh: ∀ a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom): [[ Δ, Δ', Δ'' ⊢ T: K ]] := by
  generalize Δ_eq: Δ.append Δ'' = Δ_ at kT
  induction kT generalizing Δ Δ' Δ''
  case var a K Δ_ hIn =>
    subst Δ_
    constructor
    case a =>
    induction Δ' generalizing Δ Δ''
    . case empty => simp_all [empty_append]
    . case typeExt Δ' a' K' ih =>
      specialize @ih Δ [[ (ε , a' : K') , Δ'' ]]
      simp_all [append_type_assoc]
      apply ih (by aesop (add norm typeVarDom))
      apply append_elim at hIn
      cases hIn
      . case inl hIn =>
        apply weakening_r
        . simp_all
        . by_cases (a = a')
          . case pos eq =>
            -- contradiction
            aesop (add norm typeVarDom, norm TypeVarInDom, safe forward TypeVarInDom_of)
          . case neg neq =>
            constructor <;> simp_all [TypeVarNe]
      . case inr hIn =>
        simp_all [TypeVarInEnvironment.weakening_l]
    . case termExt Δ' x' T ih =>
      specialize @ih Δ [[ (ε , x' : T) , Δ'' ]]
      simp_all [append_term_assoc]
      apply ih (by aesop (add norm typeVarDom))
      apply TypeVarInEnvironment.append_elim at hIn
      cases hIn
      . case inl hIn =>
        apply TypeVarInEnvironment.weakening_r
        . simp_all
        . constructor; simp_all
      . case inr hIn =>
        simp_all [TypeVarInEnvironment.weakening_l]
  case lam Δ_ K1 T K2 I kT ih =>
    subst Δ_
    apply Kinding.lam (I := I ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom)
    intro a notIn
    specialize @ih a (by simp_all) Δ (Δ''.typeExt a K1)
    simp_all [append]
  case scheme Δ_ K1 T K2 I kT ih =>
    subst Δ_
    have ⟨a, notIn⟩ := (I ++ T.freeTypeVars ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom).exists_fresh
    apply Kinding.scheme (I := I ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom)
    intro a notIn
    specialize @ih a (by simp_all) Δ (Δ''.typeExt a K1)
    simp_all [append]
  all_goals aesop (add safe constructors Kinding) (config := { enableSimp := false })


theorem weakening_r (kT: [[ Δ ⊢ T: K ]]) (fresh: ∀ a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom): [[ Δ, Δ' ⊢ T: K ]] := by
  apply Kinding.weakening_r' (Δ'' := Environment.empty) <;> simp_all [Environment.append]

theorem weakening : [[Δ, Δ'' ⊢ A : K]] → [[⊢ Δ, Δ', Δ'']] → [[Δ, Δ', Δ'' ⊢ A : K]] := sorry

theorem subst'  (kT: [[ Δ, a: K, Δ' ⊢ T: K' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kA: [[ Δ ⊢ A: K ]]): [[ (Δ , Δ'[A/a]) ⊢ T[A/a] : K' ]] := by
  generalize Δ'eq: (Δ.typeExt a K).append Δ' = Δ_ at kT
  induction kT generalizing Δ Δ' a A K <;> simp_all [Type.TypeVar_subst]
  case var a' K' Δ_ kIn =>
    subst Δ_
    by_cases (a = a')
    . case pos eq =>
      simp_all
      subst a'
      -- 1. by wf we know a ∉ Δ'.typeVarDom
      have fresh := wf.append_typeVar_fresh_r (a := a) (by constructor)
      -- 2. then by uniqueness we know from kIn that K' = K
      have eq := kIn.unique (K':=K) (by
        apply TypeVarInEnvironment.weakening_r fresh
        constructor
      )
      subst K'
      -- 3. then wts Δ, Δ'[S] ⊢ A: K, by weakening kA we are done
      apply weakening_r
      . case kT => assumption
      . case fresh =>
        apply EnvironmentWellFormedness.append_typeVar_fresh_l at wf
        simp_all [Environment.typeVarDom_TypeVar_subst , Environment.typeVarDom]
    . case neg neq =>
      simp_all
      -- 1. by kIn we know a': K' is either in (Δ, a: K) or Δ'
      apply TypeVarInEnvironment.append_elim at kIn
      constructor; case a =>
      cases kIn
      . case inl kIn =>
        -- 2a. If a': K' ∈ Δ, a: K, we also know that a': K' ∉ dom(Δ')
        obtain ⟨notInΔ', kIn⟩ := kIn
        -- 3a. and by a ≠ a' we know a': K' ∈ Δ.
        --     wts. a': K' ∈ Δ, Δ'[S], by weakening and subst_noop we are done
        apply TypeVarInEnvironment.weakening_r
        . simp_all [Environment.typeVarDom_TypeVar_subst, Environment.TypeVarNotInDom, Environment.TypeVarInDom, Environment.typeVarDom]
        . cases kIn <;> simp_all
      . case inr kIn =>
        -- 2b. If a': K' ∈ Δ', similarly by weakening and subst_noop we are done
        apply TypeVarInEnvironment.weakening_l
        simp_all [TypeVarInEnvironment.TypeVar_subst]
  case lam Δ_ K1 T K2 I kind ih =>
    subst Δ_
    apply Kinding.lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    specialize @ih a' (by simp_all) Δ a K (Δ'.typeExt a' K1) A
    simp_all [Environment.append]
    rw [<- Type.subst_open_var (by aesop) (kA.TypeVarLocallyClosed_of)]
    apply ih
    constructor
    . assumption
    . simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
  case scheme Δ_ K1 T K2 I kind ih =>
    subst Δ_
    apply Kinding.scheme (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a' notIn
    specialize @ih a' (by simp_all) Δ a K (Δ'.typeExt a' K1) A
    simp_all [Environment.append]
    rw [<- Type.subst_open_var (by aesop) (kA.TypeVarLocallyClosed_of)]
    apply ih
    constructor
    . assumption
    . simp_all [Environment.typeVarDom, Environment.typeVarDom_append, Environment.TypeVarNotInDom, Environment.TypeVarInDom]
  case list n Δ_ T_i K_i kind ih =>
    subst Δ_
    constructor
    simp_all
    aesop (add safe constructors Kinding)
  all_goals aesop (add safe constructors Kinding) (config := { enableSimp := false })

-- NOTE this is also provable. Difference with subst' is that we don't do substitution on Environment.
-- Check branch before merge for proof.
theorem subst2' (kT: [[ Δ, a: K, Δ' ⊢ T: K' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kA: [[ Δ ⊢ A: K ]]): [[ (Δ , Δ') ⊢ T[A/a] : K' ]] := by sorry

theorem subst  (kT: [[ Δ, a: K ⊢ T: K' ]]) (wf: [[ ⊢ Δ, a: K ]]) (kA: [[ Δ ⊢ A: K ]]): [[ Δ ⊢ T[A/a]: K' ]] :=
 by apply subst' (Δ' := Environment.empty) <;> assumption

-- NOTE provable by subst but might not be necessary
theorem lam_intro_ex_k : ∀a, a ∉ A.freeTypeVars → a ∉ Δ.typeVarDom → [[ Δ, a : K1 ⊢ A^a: K2 ]] → [[ Δ ⊢ (λ a : K1. A) : K1 ↦ K2 ]] := sorry

-- NOTE provable by subst but might not be necessary
theorem forall_intro_ex_k : ∀a, a ∉ A.freeTypeVars → a ∉ Δ.typeVarDom → [[ Δ, a : K1 ⊢ A^a: K2 ]] → [[ Δ ⊢ (∀ a : K1. A) : K2 ]] := sorry

-- TODO might not be necessary. (required by some kind of exchange lemma?)
theorem det : [[ Δ ⊢ A: K ]] → [[ Δ ⊢ A: K' ]] → K = K' := by
  intro k
  induction k generalizing K'
  . case var => aesop (add safe cases Kinding, safe TypeVarInEnvironment.unique)
  . case lam Δ K1 A K2 I kindA ih =>
    intro k
    cases k
    case lam K2' I' kindA' =>
    simp
    have ⟨a, notIn⟩ := (I ++ I').exists_fresh
    apply ih a (by aesop)
    apply kindA' a (by aesop)
  . case app =>
    rename_i ihA ihB
    intro k
    cases k
    rename_i kB kA
    apply ihA at kA
    apply ihB at kB
    simp_all
  all_goals sorry -- TODO It's obviously provable, but very tedious


theorem inv_list (k: [[ Δ ⊢ { </ A@i // i in [:n] /> } : L K ]]): ∀i ∈ [0:n], [[ Δ ⊢ A@i : K ]] := by
  generalize Teq : (Type.list ([0:n].map fun i => [A i]).flatten) = T at k
  cases k <;> simp_all
  . case list n_ A_ k =>
    simp_all [List.map_singleton_flatten]
    have neq: n = n_ := by
      apply congrArg (f:= List.length) at Teq
      simp_all [List.length_map, Std.Range.length_toList]
    simp_all [List.map_singleton_flatten, Std.Range.mem_toList_of_mem]


theorem inv_list' (k: [[ Δ ⊢ { </ A@i // i in [:n] /> } : K ]]): ∃ K', K = Kind.list K' ∧ ∀i ∈ [0:n], [[ Δ ⊢ A@i : K' ]] := by
  generalize Teq : (Type.list ([0:n].map fun i => [A i]).flatten) = T at k
  cases k <;> simp_all
  . case list n_ A_ K_ k =>
    simp_all [List.map_singleton_flatten]
    have neq: n = n_ := by
      apply congrArg (f:= List.length) at Teq
      simp_all [List.length_map, Std.Range.length_toList]
    simp_all [List.map_singleton_flatten, Std.Range.mem_toList_of_mem]

theorem unit : [[Δ ⊢ ⊗ { } : *]] := by
  have := list (Δ := Δ) (A := fun _ => .list []) (K := .star) (n := 0) (fun _ => nomatch ·)
  rw [List.map_singleton_flatten, Std.Range.toList, if_neg (nomatch ·),
      if_neg (Nat.not_lt_of_le (Nat.le_refl _))] at this
  exact prod this

theorem prj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp [«Type».TypeVar_open]
  apply arr
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
      exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
      exact A₀ki.weakening (Δwf.typeVarExt anin) (Δ' := .typeExt .empty a _) (Δ'' := .empty)

theorem inj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
      exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem concat_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  (A₂ki : [[Δ ⊢ A₂ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply arr
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
        exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₂ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
        exact A₂ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem elim_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  (A₂ki : [[Δ ⊢ A₂ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0 : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp [«Type».TypeVar_open]
  apply scheme (I := a :: Δ.typeVarDom)
  intro aₜ aₜnin
  let aₜnea := List.ne_of_not_mem_cons aₜnin
  simp [«Type».TypeVar_open]
  apply arr
  · apply arr
    · apply sum
      apply listApp
      · exact var <| .typeVarExt .head aₜnea.symm
      · let A₀lc := A₀ki.TypeVarLocallyClosed_of
        rw [A₀lc.weaken (n := 1) |>.TypeVar_open_eq, A₀lc.TypeVar_open_eq]
        exact A₀ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
          Δwf.typeVarExt anin |>.typeVarExt aₜnin
    · exact var .head
  · apply arr
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₁lc := A₁ki.TypeVarLocallyClosed_of
          rw [A₁lc.weaken (n := 1) |>.TypeVar_open_eq, A₁lc.TypeVar_open_eq]
          exact A₁ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
            Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₂lc := A₂ki.TypeVarLocallyClosed_of
          rw [A₂lc.weaken (n := 1) |>.TypeVar_open_eq, A₂lc.TypeVar_open_eq]
          exact A₂ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
            Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head

local instance : Inhabited «Type» where
  default := .list []
in
theorem ind_evidence (Δwf : [[⊢ Δ]])
  (Aki : [[Δ ⊢ A : L K]])
  (Bᵣki : ∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀,
    [[Δ, aₗ : *, aₜ : K, aₚ : L K, aᵢ : L K, aₙ : L K ⊢ Bᵣ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1^aₙ : *]])
  (Bₗki : ∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, [[Δ, aᵢ : L K, aₙ : L K ⊢ Bₗ^aᵢ#1^aₙ : *]])
  : [[Δ ⊢ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → aₗ$4 → (aₘ$5 aₚ$2) → aₘ$5 aₙ$0) → (aₘ$0 { }) → aₘ$0 A : *]] := by
  apply scheme Δ.typeVarDom
  intro aₘ aₘnin
  let Δaₘwf := Δwf.typeVarExt aₘnin (K := K.list.arr .star)
  simp [Type.TypeVar_open]
  let ⟨aₗ, aₗnin⟩ := I₀.exists_fresh
  let ⟨aₜ, aₜnin⟩ := aₗ :: I₀ |>.exists_fresh
  let ⟨aₚ, aₚnin⟩ := aₜ :: aₗ :: I₀ |>.exists_fresh
  let ⟨aᵢ, aᵢnin⟩ := aₚ :: aₜ :: aₗ :: I₀ |>.exists_fresh
  let ⟨aₙ, aₙnin⟩ := aᵢ :: aₚ :: aₜ :: aₗ :: I₀ |>.exists_fresh
  let Bᵣlc := Bᵣki _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin
    |>.TypeVarLocallyClosed_of.weaken (n := 5)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.base _)
  let ⟨aᵢ, aᵢnin⟩ := I₁ |>.exists_fresh
  let ⟨aₙ, aₙnin⟩ := aᵢ :: I₁ |>.exists_fresh
  let Bₗlc := Bₗki _ aᵢnin _ aₙnin |>.TypeVarLocallyClosed_of.weaken (n := 2)
    |>.TypeVar_open_drop (Nat.lt.step <| .base _) |>.TypeVar_open_drop (Nat.lt.base _)
  rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_eq, Bᵣlc.TypeVar_open_eq,
      Bₗlc.weaken (n := 3).TypeVar_open_eq]
  apply arr
  · apply scheme <| I₀ ++ aₘ :: Δ.typeVarDom
    intro aₗ aₗnin
    let ⟨aₗninI₀, aₗninΔ⟩ := List.not_mem_append'.mp aₗnin
    let Δaₘaₗwf := Δaₘwf.typeVarExt aₗninΔ (K := .star)
    let aₘneaₗ := List.ne_of_not_mem_cons aₗninΔ
    symm at aₘneaₗ
    simp [Type.TypeVar_open]
    rw [Bₗlc.weaken (n := 2).TypeVar_open_eq]
    apply scheme <| aₗ :: I₀ ++ aₗ :: aₘ :: Δ.typeVarDom
    intro aₜ aₜnin
    let ⟨aₜninI₀, aₜninΔ⟩ := List.not_mem_append'.mp aₜnin
    let Δaₘaₗaₜwf := Δaₘaₗwf.typeVarExt aₜninΔ (K := K)
    let aₗneaₜ := List.ne_of_not_mem_cons aₜninI₀
    let aₘneaₜ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₜninΔ
    symm at aₗneaₜ aₘneaₜ
    simp [Type.TypeVar_open]
    rw [Bₗlc.weaken (n := 1).TypeVar_open_eq]
    apply scheme <| aₜ :: aₗ :: I₀ ++ aₜ :: aₗ :: aₘ :: Δ.typeVarDom
    intro aₚ aₚnin
    let ⟨aₚninI₀, aₚninΔ⟩ := List.not_mem_append'.mp aₚnin
    let Δaₘaₗaₜaₚwf := Δaₘaₗaₜwf.typeVarExt aₚninΔ (K := K.list)
    let aₗneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₚninI₀
    let aₘneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| aₚninΔ
    symm at aₗneaₚ aₘneaₚ
    simp [Type.TypeVar_open]
    rw [Bₗlc.TypeVar_open_eq]
    apply scheme <| aₚ :: aₜ :: aₗ :: I₀ ++ I₁ ++ aₚ :: aₜ :: aₗ :: aₘ :: Δ.typeVarDom
    intro aᵢ aᵢnin
    let ⟨aᵢninI₀I₁, aᵢninΔ⟩ := List.not_mem_append'.mp aᵢnin
    let ⟨aᵢninI₀, aᵢninI₁⟩ := List.not_mem_append'.mp aᵢninI₀I₁
    let aₚneaᵢ := List.ne_of_not_mem_cons aᵢninI₀
    let Δaₘaₗaₜaₚaᵢwf := Δaₘaₗaₜaₚwf.typeVarExt aᵢninΔ (K := K.list)
    let aₗneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| aᵢninI₀
    let aₘneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aᵢninΔ
    symm at aₚneaᵢ aₗneaᵢ aₘneaᵢ
    simp [Type.TypeVar_open]
    apply scheme <|
      aᵢ :: aₚ :: aₜ :: aₗ :: I₀ ++ aᵢ :: I₁ ++ aᵢ :: aₚ :: aₜ :: aₗ :: aₘ :: Δ.typeVarDom
    intro aₙ aₙnin
    let ⟨aₙninI₀I₁, aₙninΔ⟩ := List.not_mem_append'.mp aₙnin
    let ⟨aₙninI₀, aₙninI₁⟩ := List.not_mem_append'.mp aₙninI₀I₁
    let Δaₘaₗaₜaₚaᵢaₙwf := Δaₘaₗaₜaₚaᵢwf.typeVarExt aₙninΔ (K := K.list)
    let aₚneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninI₀
    let aₗneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₙninI₀
    let aₘneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| aₙninΔ
    symm at aₚneaₙ aₗneaₙ aₘneaₙ
    simp [Type.TypeVar_open]
    apply arr <| Bᵣki _ aₗninI₀ _ aₜninI₀ _ aₚninI₀ _ aᵢninI₀ _ aₙninI₀ |>.weakening Δaₘaₗaₜaₚaᵢaₙwf
      (Δ := Δ)
      (Δ' := .typeExt .empty ..)
      (Δ'' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
    apply arr <| Bₗki _ aᵢninI₁ _ aₙninI₁ |>.weakening Δaₘaₗaₜaₚaᵢaₙwf
      (Δ := Δ)
      (Δ' := .typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
      (Δ'' := .typeExt (.typeExt .empty ..) ..)
    · apply arr
      · exact var <|
          .typeVarExt (.typeVarExt (.typeVarExt (.typeVarExt .head aₗneaₜ) aₗneaₚ) aₗneaᵢ) aₗneaₙ
      · apply arr
        · apply app
          · exact var <| .typeVarExt (.typeVarExt (.typeVarExt
               (.typeVarExt (.typeVarExt .head aₘneaₗ) aₘneaₜ) aₘneaₚ) aₘneaᵢ) aₘneaₙ
          · exact var <| .typeVarExt (.typeVarExt .head aₚneaᵢ) aₚneaₙ
        · apply app
          · exact var <| .typeVarExt (.typeVarExt (.typeVarExt
               (.typeVarExt (.typeVarExt .head aₘneaₗ) aₘneaₜ) aₘneaₚ) aₘneaᵢ) aₘneaₙ
          · exact var .head
  · apply arr
    · apply app
      · exact var .head
      · rw [← Std.Range.map_get!_eq (as := []), Std.Range.map, ← List.map_singleton_flatten,
            ← Std.Range.map]
        exact list fun _ => (nomatch ·)
    · apply app
      · exact var .head
      · exact Aki.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) Δaₘwf

end Kinding

-- TODO this is also a weird place for EnvironmentWellFormedness lemma, but the proof here depends on Kinding lemma.
namespace EnvironmentWellFormedness

open Environment in
theorem subst (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kA: [[ Δ ⊢ A: K ]]): [[ ⊢ Δ, Δ'[A/a] ]] := by
  induction Δ' generalizing Δ a K A <;> simp_all [Environment.append]
  . case empty =>
    cases wf
    assumption
  . case typeExt Δ' a' K' ih =>
    cases wf
    case typeVarExt wf notIn =>
    constructor
    . case a => apply ih <;> assumption
    . case a =>
      clear ih K' kA
      simp_all [TypeVarNotInDom, TypeVarInDom]
      induction Δ' <;> simp_all [TypeVar_subst, append, typeVarDom] <;> cases wf <;> simp_all
  . case termExt Δ' a' T ih =>
    cases wf
    case termVarExt wf notIn kind =>
    constructor
    . case a => apply ih <;> assumption
    . case a =>
      clear ih kind
      simp_all [TermVarNotInDom, TermVarInDom]
      induction Δ' <;> simp_all [TypeVar_subst, append, typeVarDom, termVarDom] <;> cases wf <;> aesop
    . case a => apply Kinding.subst' (K := K) <;> simp_all

end EnvironmentWellFormedness

namespace TypeEquivalence

def symm : [[Δ ⊢ A ≡ B]] → [[Δ ⊢ B ≡ A]]
  | refl => refl
  | lamAppL => lamAppR
  | lamAppR => lamAppL
  | listAppL => listAppR
  | listAppR => listAppL
  | lam I h => lam I fun a mem => (h a mem).symm
  | app h₁ h₂ => app h₁.symm h₂.symm
  | scheme I h => scheme I fun a mem => (h a mem).symm
  | arr h₁ h₂ => arr h₁.symm h₂.symm
  | list h => list fun i mem => (h i mem).symm
  | listApp h₁ h₂ => listApp h₁.symm h₂.symm
  | prod h => prod h.symm
  | sum h => sum h.symm

def trans : [[Δ ⊢ A₀ ≡ A₁]] → [[Δ ⊢ A₁ ≡ A₂]] → [[Δ ⊢ A₀ ≡ A₂]] := sorry

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
