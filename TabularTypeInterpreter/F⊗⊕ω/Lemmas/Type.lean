import Aesop
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type

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

theorem TypeVar_open_comm (A : «Type»)
  : m ≠ n → (A.TypeVar_open a m).TypeVar_open a' n = (A.TypeVar_open a' n).TypeVar_open a m := by
  induction A using rec_uniform generalizing m n <;> aesop (add simp TypeVar_open)

theorem TypeVar_open_eq_Type_open_var : TypeVar_open A a n = A.Type_open (.var a) n := by
  induction A using rec_uniform generalizing n <;> aesop (add simp [TypeVar_open, Type_open])

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

theorem TypeVar_open_id : TypeVarLocallyClosed A n → A.TypeVar_open a n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)

theorem Type_open_id : TypeVarLocallyClosed A n → A.Type_open a n = A := by
  induction A using rec_uniform generalizing n <;> aesop
    (add simp Type_open, safe cases TypeVarLocallyClosed, safe List.map_eq_id_of_eq_id_of_mem)

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

-- theorem foo
--   : TypeVar_open A' a n = Type_open A B m → a ∉ A'.freeTypeVars → A.TypeVarLocallyClosed (m + 1) →
--     B.TypeVarLocallyClosed → A' = (A.TypeVar_open a n).Type_open B m := by
--   intro eq aninA' Alc Blc
--   match A', A with
--   | .var .., .var .. => sorry
--   | .lam .., .lam .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let ⟨eq₀, eq₁⟩ := lam.inj eq
--     cases eq₀
--     rw [freeTypeVars] at aninA'
--     let .lam Alc := Alc
--     rw [foo eq₁ aninA' Alc Blc]
--   | .app .., .app .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let ⟨eq₀, eq₁⟩ := app.inj eq
--     rw [freeTypeVars] at aninA'
--     let ⟨aninA'', aninB'⟩ := List.not_mem_append'.mp aninA'
--     let .app A''lc B'lc := Alc
--     rw [foo eq₀ aninA'' A''lc Blc, foo eq₁ aninB' B'lc Blc]
--   | .forall .., .forall .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let ⟨eq₀, eq₁⟩ := forall.inj eq
--     cases eq₀
--     rw [freeTypeVars] at aninA'
--     let .forall Alc := Alc
--     rw [foo eq₁ aninA' Alc Blc]
--   | .arr .., .arr .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let ⟨eq₀, eq₁⟩ := arr.inj eq
--     rw [freeTypeVars] at aninA'
--     let ⟨aninA'', aninB'⟩ := List.not_mem_append'.mp aninA'
--     let .arr A''lc B'lc := Alc
--     rw [foo eq₀ aninA'' A''lc Blc, foo eq₁ aninB' B'lc Blc]
--   | .list .., .list .. => sorry
--   | .listApp .., .listApp .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let ⟨eq₀, eq₁⟩ := listApp.inj eq
--     rw [freeTypeVars] at aninA'
--     let ⟨aninA'', aninB'⟩ := List.not_mem_append'.mp aninA'
--     let .listApp A''lc B'lc := Alc
--     rw [foo eq₀ aninA'' A''lc Blc, foo eq₁ aninB' B'lc Blc]
--   | .prod .., .prod .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let eq' := prod.inj eq
--     rw [freeTypeVars] at aninA'
--     let .prod A''lc := Alc
--     rw [foo eq' aninA' A''lc Blc]
--   | .sum .., .sum .. =>
--     rw [TypeVar_open, Type_open] at eq ⊢
--     let eq' := sum.inj eq
--     rw [freeTypeVars] at aninA'
--     let .sum A''lc := Alc
--     rw [foo eq' aninA' A''lc Blc]

  -- induction A' using rec_uniform generalizing A n <;>
  --   induction A using rec_uniform <;> aesop
  --   (add simp [TypeVar_open, Type_open, freeTypeVars], safe cases TypeVar, 10% List.eq_of_map_eq_map_of_inj)

end TypeVarLocallyClosed

theorem TypeVar_close_eq_of_not_mem_freeTypeVars
  : a ∉ freeTypeVars A → A.TypeVar_close a n = A := by
  induction A using rec_uniform generalizing n <;> aesop (add simp [freeTypeVars, TypeVar_close])

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

-- theorem bar (aninA : a ∉ freeTypeVars A) (mnen : m ≠ n)
--   (eq : A.TypeVar_open a m = TypeVar_open B a n) : A = B.TypeVar_open a m := by
--   rw [← TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA (n := n)] at eq

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
  all_goals (simp; try simp_arith)
  rw [List.map_singleton_flatten]
  apply Nat.le_of_lt
  exact List.sizeOf_lt_of_mem A'''in

theorem Type_open_preservation {A : «Type»}
  (Aki : Kinding [[(Δ, a : K, Δ')]] (A.TypeVar_open a n) K') (aninfvA : a ∉ A.freeTypeVars)
  (Bki : [[Δ ⊢ B : K]]) : Kinding [[(Δ, (Δ' [B / a]))]] (A.Type_open B n) K' := sorry

theorem weakening : [[Δ, Δ'' ⊢ A : K]] → [[⊢ Δ, Δ', Δ'']] → [[Δ, Δ', Δ'' ⊢ A : K]] := sorry

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
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem inj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
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
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply arr
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
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
        rw [A₀lc.weaken (n := 1) |>.TypeVar_open_id, A₀lc.TypeVar_open_id]
        exact A₀ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
          Δwf.typeVarExt anin |>.typeVarExt aₜnin
    · exact var .head
  · apply arr
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₁lc := A₁ki.TypeVarLocallyClosed_of
          rw [A₁lc.weaken (n := 1) |>.TypeVar_open_id, A₁lc.TypeVar_open_id]
          exact A₁ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
            Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₂lc := A₂ki.TypeVarLocallyClosed_of
          rw [A₂lc.weaken (n := 1) |>.TypeVar_open_id, A₂lc.TypeVar_open_id]
          exact A₂ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
            Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head

theorem ind_evidence (Δwf : [[⊢ Δ]])
  (Bᵣki : [[Δ, aₗ : *, aₜ : K, aₚ : L K, aᵢ : L K, aₙ : L K ⊢ Bᵣ^aₙ^aᵢ^aₚ^aₜ^aₗ : *]])
  (Bₗki : [[Δ, aᵢ : L K, aₙ : L K ⊢ Bₗ^aₙ^aᵢ : *]])
  : [[Δ ⊢ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → aₗ$4 → aₘ$5 aₚ$2 → aₘ$5 aₙ$0) → aₘ$5 { } → aₘ$5 A : *]] := sorry

theorem id : [[Δ ⊢ λ a : K. a$0 : K ↦ K]] := by
  apply lam []
  intro a anin
  rw [Type.TypeVar_open, if_pos rfl]
  exact var .head

end Kinding

namespace TypeEquivalence

private
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

end TabularTypeInterpreter.«F⊗⊕ω»
