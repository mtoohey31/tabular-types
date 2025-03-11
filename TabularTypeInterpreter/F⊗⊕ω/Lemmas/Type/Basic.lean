import Mathlib.Tactic
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type

namespace TabularTypeInterpreter.«F⊗⊕ω».«Type»

@[elab_as_elim]
def rec_uniform {motive : «Type» → Prop} (var : ∀ a : TypeVar, motive (var a))
  (lam : ∀ K A, motive A → motive (lam K A)) (app : ∀ A B, motive A → motive B → motive (app A B))
  («forall» : ∀ K A, motive A → motive («forall» K A))
  (arr : ∀ A B, motive A → motive B → motive (arr A B))
  (list : ∀ As, (∀ A ∈ As, motive A) → motive (list As))
  (listApp : ∀ A B, motive A → motive B → motive (listApp A B))
  (prod : ∀ A, motive A → motive (prod A)) (sum : ∀ A, motive A → motive (sum A)) (A : «Type»)
  : motive A :=
  rec (motive_1 := motive) var lam app «forall» arr list listApp prod sum nofun
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
    | [] => exact .list nofun
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
    | [] => exact .list nofun
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

theorem TypeVar_open_id : TypeVarLocallyClosed A n → A.TypeVar_open a n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)
    (add simp Type_open, safe cases TypeVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)

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
    (add simp [Type_open, TypeVar_open], 40% TypeVar_open_id, safe weaken)

theorem Type_open_TypeVar_open_eq
  : TypeVarLocallyClosed B n → (Type_open A B n).TypeVar_open a n = A.Type_open B n := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp [Type_open, TypeVar_open], 40% TypeVar_open_id, safe weaken)

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

theorem TypeVar_subst_drop {A: «Type»} (Alc: (A.TypeVar_subst a T).TypeVarLocallyClosed n): A.TypeVarLocallyClosed n := by
  induction A using Type.rec_uniform generalizing n <;>
    aesop (add norm Type.TypeVar_subst, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

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


-- NOTE only this is needed
theorem subst_open_var {T A: «Type»} (neq: x ≠ y) (lc: A.TypeVarLocallyClosed n): (T.TypeVar_open y n).TypeVar_subst x A = (T.TypeVar_subst x A).TypeVar_open y n := sorry


theorem subst_close_var {T A: «Type»} (neq: x ≠ y) (fresh: y ∉ A.freeTypeVars): (T.TypeVar_close y n).TypeVar_subst x A = (T.TypeVar_subst x A).TypeVar_close y n := sorry


theorem subst_fresh {A T : «Type»} (fresh: a ∉ A.freeTypeVars) : a ∉ (T.TypeVar_subst a A |>.freeTypeVars) := sorry


theorem subst_fresh' {A T: «Type»} (freshA: a ∉ A.freeTypeVars) (freshT: a ∉ T.freeTypeVars) : a ∉ (T.TypeVar_subst a' A |>.freeTypeVars) := sorry -- TODO by induction on T, wait is the a a' part right?

theorem freeTypeVars_TypeVar_open {T: «Type»} : a ∈ T.freeTypeVars -> a ∈ (T.TypeVar_open a' n).freeTypeVars := by
  induction T using rec_uniform generalizing n <;> aesop (add simp [freeTypeVars, TypeVar_open])

namespace TabularTypeInterpreter.«F⊗⊕ω».«Type»
