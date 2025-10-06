import Aesop
import TabularTypes.«F⊗⊕ω».Lemmas.Environment
import TabularTypes.«F⊗⊕ω».Lemmas.Type
import TabularTypes.«F⊗⊕ω».Semantics.Term

namespace TabularTypes.«F⊗⊕ω»

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

theorem multi_app_snoc_eq : multi_app (Fs ++ [F]) E = F.app (multi_app Fs E) := by
  induction Fs generalizing E with
  | nil => rw [List.nil_append, multi_app, multi_app, multi_app]
  | cons F' Fs' ih => rw [List.cons_append, multi_app, multi_app, ih]

@[simp]
theorem TypeVar_open_sizeOf : sizeOf (TypeVar_open E x n) = sizeOf E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TypeVar_open, safe List.sizeOf_map_eq_of_eq_id_of_mem)

@[simp]
theorem TermVar_open_sizeOf : sizeOf (TermVar_open E x n) = sizeOf E := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp TermVar_open, safe List.sizeOf_map_eq_of_eq_id_of_mem)

theorem TypeVar_open_TermVar_subst_comm {E: Term} : (E.TermVar_open y n).TypeVar_subst x A = (E.TypeVar_subst x A).TermVar_open y n := by
  induction E using rec_uniform generalizing n <;> simp_all [TermVar_open, TypeVar_subst]

theorem TermVar_subst_intro_of_not_mem_freeTermVars {A: Term}: a ∉ A.freeTermVars → (A.TermVar_open a n).TermVar_subst a B = A.Term_open B n := by
  induction A using rec_uniform generalizing B n <;>
    aesop (add simp [TermVar_subst, TermVar_open, Term_open, freeTermVars, TermVar_open])

theorem TypeVar_subst_intro_of_not_mem_freeTypeVars {A: Term}: a ∉ A.freeTypeVars → (A.TypeVar_open a n).TypeVar_subst a B = A.Type_open B n := by
  induction A using rec_uniform generalizing B n <;>
    simp_all [TypeVar_subst, TypeVar_open, Type_open, freeTypeVars, TypeVar_open, Type.TypeVar_subst_intro_of_not_mem_freeTypeVars]

@[simp]
theorem TypeVar_open_multi_app : TypeVar_open (multi_app Fs E) a n =
    multi_app (Fs.map (TypeVar_open · a n)) (TypeVar_open E a n) := by
  induction Fs generalizing E with
  | nil =>
    rw [List.map_nil, multi_app, multi_app]
  | cons F Fs' ih => rw [List.map_cons, multi_app, multi_app, ih, TypeVar_open]

@[simp]
theorem TermVar_open_multi_app : TermVar_open (multi_app Fs E) x n =
    multi_app (Fs.map (TermVar_open · x n)) (TermVar_open E x n) := by
  induction Fs generalizing E with
  | nil =>
    rw [List.map_nil, multi_app, multi_app]
  | cons F Fs' ih => rw [List.map_cons, multi_app, multi_app, ih, TermVar_open]

theorem TermVar_open_comm
  : m ≠ n → TermVar_open (TermVar_open E x m) x' n = TermVar_open (TermVar_open E x' n) x m := by
  induction E using rec_uniform generalizing m n <;> aesop (add simp TermVar_open)

theorem TermVar_multi_open_comm : n ≤ m → (TermVar_open E x m).TermVar_multi_open x' n =
    (E.TermVar_multi_open x' n).TermVar_open x m := by
  intro nlem
  match n with
  | 0 => rw [TermVar_multi_open, TermVar_multi_open]
  | n' + 1 =>
    rw [TermVar_multi_open, TermVar_multi_open, TermVar_open_comm (Ne.symm (Nat.ne_of_lt nlem)),
        TermVar_multi_open_comm <| Nat.le_trans Nat.le.refl.step nlem]

theorem TypeVar_open_comm
  : m ≠ n → TypeVar_open (TypeVar_open E a m) a' n = TypeVar_open (TypeVar_open E a' n) a m := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp TypeVar_open, 20% Type.TypeVar_open_comm)

theorem TypeVar_multi_open_comm : n ≤ m → (TypeVar_open E a m).TypeVar_multi_open a' n =
    (E.TypeVar_multi_open a' n).TypeVar_open a m := by
  intro nlem
  match n with
  | 0 => rw [TypeVar_multi_open, TypeVar_multi_open]
  | n' + 1 =>
    rw [TypeVar_multi_open, TypeVar_multi_open, TypeVar_open_comm (Ne.symm (Nat.ne_of_lt nlem)),
        TypeVar_multi_open_comm <| Nat.le_trans Nat.le.refl.step nlem]

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

theorem Type_open_TypeVar_open_comm : Type.TypeVarLocallyClosed A m → m ≠ n →
    (Type_open E A n).TypeVar_open a m = (TypeVar_open E a m).Type_open A n := by
  induction E using rec_uniform generalizing m n <;> aesop
    (add simp [TypeVar_open, Type_open], safe cases TypeVarLocallyClosed,
      20% [TypeVarLocallyClosed.TypeVar_open_id, Eq.symm, Type.TypeVarLocallyClosed.weaken,
           Type.Type_open_TypeVar_open_comm])

theorem Type_open_TypeVar_multi_open_comm : Type.TypeVarLocallyClosed A → m ≤ n →
    (Type_open E A n).TypeVar_multi_open a m = (E.TypeVar_multi_open a m).Type_open A n := by
  intro Alc mlen
  match m with
  | 0 => rw [TypeVar_multi_open, TypeVar_multi_open]
  | m' + 1 =>
    let Alc' := Alc.weaken (n := m')
    rw [Nat.zero_add] at Alc'
    rw [TypeVar_multi_open, TypeVar_multi_open, Type_open_TypeVar_open_comm Alc' (Nat.ne_of_lt mlen),
        Type_open_TypeVar_multi_open_comm Alc <| Nat.le_trans Nat.le.refl.step mlen]

namespace TermVarLocallyClosed

theorem TermVar_open_id
  : TermVarLocallyClosed E n → E.TermVar_open x n = E := by
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

theorem Term_open_TermVar_open_comm : TermVarLocallyClosed F m → m ≠ n →
    (Term_open E F n).TermVar_open x m = (TermVar_open E x m).Term_open F n := by
  induction E using rec_uniform generalizing m n
  case var =>
    intro Flc mnen
    rw [Term_open]
    split
    · case isTrue h =>
      cases h
      rw [TermVar_open, if_neg (mnen <| TermVar.bound.inj ·), Term_open, if_pos rfl,
          Flc.TermVar_open_id]
    · case isFalse h =>
      rw [TermVar_open]
      split
      · case isTrue h' =>
        cases h'
        rw [Term_open, if_neg nofun]
      · case isFalse h' => rw [Term_open, if_neg h]
  case lam ih =>
    intro Flc mnen
    rw [Term_open, TermVar_open, TermVar_open, Term_open,
        ih (Flc.weaken (n := 1)) (mnen <| Nat.add_one_inj.mp ·)]
  all_goals aesop
      (add simp [TermVar_open, Term_open], safe cases TermVarLocallyClosed,
        20% [TermVarLocallyClosed.TermVar_open_id, Eq.symm, TermVarLocallyClosed.weaken,
             Term.Term_open_TermVar_open_comm])

theorem Term_open_TermVar_multi_open_comm : TermVarLocallyClosed F → m ≤ n →
    (Term_open E F n).TermVar_multi_open a m = (E.TermVar_multi_open a m).Term_open F n := by
  intro Alc mlen
  match m with
  | 0 => rw [TermVar_multi_open, TermVar_multi_open]
  | m' + 1 =>
    let Alc' := Alc.weaken (n := m')
    rw [Nat.zero_add] at Alc'
    rw [TermVar_multi_open, TermVar_multi_open, Term_open_TermVar_open_comm Alc' (Nat.ne_of_lt mlen),
        Term_open_TermVar_multi_open_comm Alc <| Nat.le_trans Nat.le.refl.step mlen]

theorem TypeVar_open_TermVar_open_comm
  : (TermVar_open E x n).TypeVar_open a m = (E.TypeVar_open a m).TermVar_open x n := by
  induction E using rec_uniform generalizing m n <;> aesop (add simp [TermVar_open, TypeVar_open])

theorem Type_open_TermVar_open_comm
  : (TermVar_open E x n).Type_open A m = (E.Type_open A m).TermVar_open x n := by
  induction E using rec_uniform generalizing m n <;> aesop (add simp [TermVar_open, Type_open])

theorem TypeVar_open_TermVar_multi_open_comm : (TypeVar_open E a n).TermVar_multi_open x m =
    (E.TermVar_multi_open x m).TypeVar_open a n := by
  match m with
  | 0 => rw [TermVar_multi_open, TermVar_multi_open]
  | n' + 1 =>
    rw [TermVar_multi_open, TermVar_multi_open, ← TypeVar_open_TermVar_open_comm,
        TypeVar_open_TermVar_multi_open_comm]

theorem TermVar_open_TypeVar_multi_open_comm : (TermVar_open E x n).TypeVar_multi_open a m =
    (E.TypeVar_multi_open a m).TermVar_open x n := by
  match m with
  | 0 => rw [TypeVar_multi_open, TypeVar_multi_open]
  | n' + 1 =>
    rw [TypeVar_multi_open, TypeVar_multi_open, TypeVar_open_TermVar_open_comm,
        TermVar_open_TypeVar_multi_open_comm]

theorem TypeVar_multi_open_TermVar_multi_open_comm
  : (TypeVar_multi_open E a n).TermVar_multi_open x m =
    (E.TermVar_multi_open x m).TypeVar_multi_open a n := by
  match m with
  | 0 => rw [TermVar_multi_open, TermVar_multi_open]
  | m' + 1 =>
    rw [TermVar_multi_open, TermVar_multi_open, ← TermVar_open_TypeVar_multi_open_comm,
        TypeVar_multi_open_TermVar_multi_open_comm]

theorem Type_multi_open_TermVar_open_comm : (Type_multi_open E A n).TermVar_open x m =
    (TermVar_open E x m).Type_multi_open A n := by
  match n with
  | 0 => rw [Type_multi_open, Type_multi_open]
  | n' + 1 =>
    rw [Type_multi_open, Type_multi_open, Type_open_TermVar_open_comm,
        Type_multi_open_TermVar_open_comm]

theorem Type_multi_open_TermVar_multi_open_comm : (Type_multi_open E A n).TermVar_multi_open x m =
    (TermVar_multi_open E x m).Type_multi_open A n := by
  match m with
  | 0 => rw [TermVar_multi_open, TermVar_multi_open]
  | m' + 1 =>
    rw [TermVar_multi_open, TermVar_multi_open, Type_multi_open_TermVar_open_comm,
        Type_multi_open_TermVar_multi_open_comm]

theorem Term_open_TypeVar_open_comm : TypeVarLocallyClosed F m →
    (Term_open E F n).TypeVar_open a m = (TypeVar_open E a m).Term_open F n := by
  induction E using rec_uniform generalizing m n
  case var =>
    intro Flc
    rw [Term_open]
    split
    · case isTrue h =>
      cases h
      rw [Flc.TypeVar_open_id, TypeVar_open, Term_open, if_pos rfl]
    · case isFalse h => rw [TypeVar_open, Term_open, if_neg h]
  case typeLam ih =>
    intro Flc
    rw [Term_open, TypeVar_open, TypeVar_open, Term_open, ih (Flc.weaken (n := 1))]
  all_goals aesop
      (add simp [TypeVar_open, Term_open], safe cases TypeVarLocallyClosed,
        20% [TypeVarLocallyClosed.TypeVar_open_id, Eq.symm, TypeVarLocallyClosed.weaken])

theorem Term_multi_open_TypeVar_open_comm (Flc : ∀ i < n, TypeVarLocallyClosed (F i) m)
  : (Term_multi_open E F n).TypeVar_open a m = (TypeVar_open E a m).Term_multi_open F n := by
  match n with
  | 0 => rw [Term_multi_open, Term_multi_open]
  | n' + 1 =>
    rw [Term_multi_open, Term_multi_open, ← Term_open_TypeVar_open_comm (Flc _ Nat.le.refl),
        Term_multi_open_TypeVar_open_comm (Flc · <| Nat.lt_add_right 1 ·)]

theorem Term_multi_open_TypeVar_multi_open_comm (Flc : ∀ i < n, TypeVarLocallyClosed (F i))
  : (Term_multi_open E F n).TypeVar_multi_open a m =
    (TypeVar_multi_open E a m).Term_multi_open F n := by
  match m with
  | 0 => rw [TypeVar_multi_open, TypeVar_multi_open]
  | m' + 1 =>
    let Flc' := (Flc · · |>.weaken (n := m'))
    rw [Nat.zero_add] at Flc'
    rw [TypeVar_multi_open, TypeVar_multi_open, Term_multi_open_TypeVar_open_comm Flc',
        Term_multi_open_TypeVar_multi_open_comm Flc]

theorem not_mem_freeTypeVars_TypeVar_open_intro
  : a ∉ freeTypeVars E → a ≠ a' → a ∉ (TypeVar_open E a' n).freeTypeVars := by
  induction E using rec_uniform generalizing n
  case lam ih =>
    intro anin ane
    rw [TypeVar_open, freeTypeVars]
    rw [freeTypeVars] at anin
    let ⟨aninA, aninE⟩ := List.not_mem_append'.mp anin
    exact List.not_mem_append'.mpr ⟨
      Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ane,
      ih aninE ane
    ⟩
  case typeApp ih =>
    intro anin ane
    rw [TypeVar_open, freeTypeVars]
    rw [freeTypeVars] at anin
    let ⟨aninE, aninA⟩ := List.not_mem_append'.mp anin
    exact List.not_mem_append'.mpr ⟨
      ih aninE ane,
      Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ane,
    ⟩
  all_goals aesop
    (add simp [TypeVar_open, freeTypeVars], safe cases TypeVar,
      60% Type.not_mem_freeTypeVars_TypeVar_open_intro)

theorem not_mem_freeTypeVars_Type_open_intro
  : a ∉ freeTypeVars E → a ∉ Type.freeTypeVars A → a ∉ (Type_open E A n).freeTypeVars := by
  induction E using rec_uniform generalizing n
  case lam ih =>
    intro aninE aninA
    rw [Type_open, freeTypeVars]
    rw [freeTypeVars] at aninE
    let ⟨aninA', aninE'⟩ := List.not_mem_append'.mp aninE
    exact List.not_mem_append'.mpr ⟨
      Type.not_mem_freeTypeVars_Type_open_intro aninA' aninA,
      ih aninE' aninA
    ⟩
  case typeApp ih =>
    intro aninE aninA
    rw [Type_open, freeTypeVars]
    rw [freeTypeVars] at aninE
    let ⟨aninE', aninA'⟩ := List.not_mem_append'.mp aninE
    exact List.not_mem_append'.mpr ⟨
      ih aninE' aninA,
      Type.not_mem_freeTypeVars_Type_open_intro aninA' aninA
    ⟩
  all_goals aesop
    (add simp [Type_open, freeTypeVars], safe cases TypeVar)

theorem not_mem_freeTypeVars_TypeVar_multi_open_intro (aninE : a ∉ freeTypeVars E)
  (anea' : ∀ i < n, a ≠ a' i) : a ∉ (E.TypeVar_multi_open a' n).freeTypeVars := by
  match n with
  | 0 =>
    rw [TypeVar_multi_open]
    exact aninE
  | n' + 1 =>
    rw [TypeVar_multi_open]
    exact not_mem_freeTypeVars_TypeVar_multi_open_intro
      (not_mem_freeTypeVars_TypeVar_open_intro aninE <| anea' _ Nat.le.refl)
      (anea' · <| Nat.lt_add_right _ ·)

theorem not_mem_freeTypeVars_TermVar_open_intro (aninE : a ∉ freeTypeVars E)
  : a ∉ (E.TermVar_open x n).freeTypeVars := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp [TermVar_open, freeTypeVars], safe cases TypeVar)

theorem not_mem_freeTypeVars_TermVar_multi_open_intro (aninE : a ∉ freeTypeVars E)
  : a ∉ (E.TermVar_multi_open x n).freeTypeVars := by
  match n with
  | 0 =>
    rw [TermVar_multi_open]
    exact aninE
  | n' + 1 =>
    rw [TermVar_multi_open]
    exact not_mem_freeTypeVars_TermVar_multi_open_intro <|
      not_mem_freeTypeVars_TermVar_open_intro aninE

theorem not_mem_freeTermVars_Type_open_intro
  : x ∉ freeTermVars E → x ∉ freeTermVars (Type_open E A n) := by
  induction E using rec_uniform generalizing n <;> aesop (add simp [Type_open, freeTermVars])

theorem not_mem_freeTermVars_Type_multi_open_intro (xninE : x ∉ freeTermVars E)
  : x ∉ freeTermVars (Type_multi_open E A n) := by
  match n with
  | 0 =>
    rw [Type_multi_open]
    exact xninE
  | n' + 1 =>
    rw [Type_multi_open]
    exact not_mem_freeTermVars_Type_multi_open_intro <| not_mem_freeTermVars_Type_open_intro xninE

theorem not_mem_freeTermVars_TermVar_open_intro
  : x ∉ freeTermVars E → x ≠ x' → x ∉ (TermVar_open E x' n).freeTermVars := by
  induction E using rec_uniform generalizing n
  all_goals aesop
    (add simp [TermVar_open, freeTermVars], safe cases TypeVar,
      60% Type.not_mem_freeTypeVars_TypeVar_open_intro)

theorem not_mem_freeTermVars_Term_open_intro
  : x ∉ freeTermVars E → x ∉ freeTermVars F → x ∉ (Term_open E F n).freeTermVars := by
  induction E using rec_uniform generalizing n
  all_goals aesop
    (add simp [Term_open, freeTermVars], safe cases TypeVar,
      60% Type.not_mem_freeTypeVars_TypeVar_open_intro)

theorem not_mem_freeTermVars_TermVar_multi_open_intro (aninE : a ∉ freeTermVars E)
  (anea' : ∀ i < n, a ≠ a' i) : a ∉ (E.TermVar_multi_open a' n).freeTermVars := by
  match n with
  | 0 =>
    rw [TermVar_multi_open]
    exact aninE
  | n' + 1 =>
    rw [TermVar_multi_open]
    exact not_mem_freeTermVars_TermVar_multi_open_intro
      (not_mem_freeTermVars_TermVar_open_intro aninE <| anea' _ Nat.le.refl)
      (anea' · <| Nat.lt_add_right _ ·)

theorem TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars
  : a ∉ freeTypeVars E → (TypeVar_open E a n).TypeVar_subst a A = E.Type_open A n := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp [freeTypeVars, TypeVar_open, TypeVar_subst, Type_open],
      40% Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars)

theorem TermVar_open_TermVar_subst_eq_Term_open_of_not_mem_freeTermVars
  : x ∉ freeTermVars E → (TermVar_open E x n).TermVar_subst x F = E.Term_open F n := by
  induction E using rec_uniform generalizing n <;> aesop
    (add simp [freeTermVars, TermVar_open, TermVar_subst, Term_open])

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

open Std

local instance : Inhabited Term where
  default := .prodIntro []
in
local instance : Inhabited «Type» where
  default := .list [] none
in
theorem prodIntro' {b : Bool} (wf: [[ ⊢ Δ ]])
  (EstyAs : ∀ EA ∈ List.zip Es As, let (E, A) := EA; [[Δ ⊢ E : A]]) (h : Es.length ≠ 0 ∨ b)
  (length_eq : Es.length = As.length)
  : Typing Δ (.prodIntro Es) (.prod (.list As (Option.someIf .star b))) := by
  rw (occs := .pos [1]) [← Range.map_get!_eq (as := Es)]
  rw [← Range.map_get!_eq (as := As), ← length_eq]
  apply Typing.prodIntro wf _ (by rw [NatNe, BoolId]; exact h)
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
  default := .list [] none
in
local instance : Inhabited Kind where
  default := .star
in
theorem sumElim' (EtyA : Typing Δ E (.sum (.list As (Option.someIf .star b))))
  (FstyAsarrB : ∀ FA ∈ List.zip Fs As, let (F, A) := FA; [[Δ ⊢ F : A → B]])
  (Bki : [[Δ ⊢ B : *]]) (length_eq : Fs.length = As.length) : Typing Δ (.sumElim E Fs) B := by
  rw [← Range.map_get!_eq (as := Fs)]
  apply Typing.sumElim (A := As.get!)
  · rw [length_eq, Range.map_get!_eq]
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

theorem unit (Δwf : [[⊢ Δ]]) : [[Δ ⊢ () : ⊗ { : * }]] := by
  apply Typing.prodIntro' Δwf _ (.inr rfl) rfl
  intro EA mem
  rw [List.zip_nil_left] at mem
  nomatch mem

theorem singleton (EtyA : [[Δ ⊢ E : A]]) : [[Δ ⊢ (E) : ⊗ {A}]] := by
  rw [← Option.someIf_false]
  apply prodIntro' EtyA.WellFormedness_of _ (.inl (by rw [List.length_singleton]; nofun)) rfl
  intro EA mem
  rw [List.zip_cons_cons, List.zip_nil_left] at mem
  let (_, _) := EA
  let .head .. := mem
  exact EtyA

theorem pair (EtyA : [[Δ ⊢ E : A]]) (FtyB : [[Δ ⊢ F : B]]) : [[Δ ⊢ (E, F) : ⊗ {A, B}]] := by
  rw [← Option.someIf_false]
  apply prodIntro' EtyA.WellFormedness_of _ (.inl (by simp [List.length])) rfl
  intro EA mem
  rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_nil_left] at mem
  let (_, _) := EA
  match mem with
  | .head .. => exact EtyA
  | .tail _ (.head ..) => exact FtyB

theorem quadruple (E₀tyA₀ : [[Δ ⊢ E₀ : A₀]]) (E₁tyA₁ : [[Δ ⊢ E₁ : A₁]]) (E₂tyA₂ : [[Δ ⊢ E₂ : A₂]])
  (E₃tyA₃ : [[Δ ⊢ E₃ : A₃]]) : [[Δ ⊢ (E₀, E₁, E₂, E₃) : ⊗ {A₀, A₁, A₂, A₃}]] := by
  rw [← Option.someIf_false]
  apply prodIntro' E₀tyA₀.WellFormedness_of _ (.inl (by simp [List.length])) rfl
  intro EA mem
  rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons,
      List.zip_nil_left] at mem
  let (_, _) := EA
  match mem with
  | .head .. => exact E₀tyA₀
  | .tail _ (.head ..) => exact E₁tyA₁
  | .tail _ (.tail _ (.head ..)) => exact E₂tyA₂
  | .tail _ (.tail _ (.tail _ (.head ..))) => exact E₃tyA₃

theorem explode (Ety : [[Δ ⊢ E : ⊕ { : * }]]) (Aki : [[Δ ⊢ A : *]]) : [[Δ ⊢ case E { } : A]] := by
  rw [← Option.someIf_true] at Ety
  apply sumElim' Ety _ Aki rfl
  intro _ mem
  rw [List.zip_nil_left] at mem
  nomatch mem

theorem multi_app (Ety : [[Δ ⊢ E : A@0]]) (Fty : ∀ m < n, [[Δ ⊢ ! </ F@i // i in [:m] /> E : A@m]] →
    [[Δ ⊢ ! </ F@i // i in [:m+1] /> E : A@m.succ]])
  : [[Δ ⊢ ! </ F@i // i in [:n] /> E : A@n]] := by induction n with
  | zero => rwa [Range.map, Range.toList, if_neg nofun, List.map_nil, Term.multi_app]
  | succ m ih => exact Fty _ Nat.le.refl <| ih <| (Fty · <| Nat.lt_add_right 1 ·)

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
    exact ih i (by simp_all [Range.mem_of_mem_toList])
  . case prodElim Δ E n As b i EtyAs In ih =>
    simp [List.map_singleton_flatten] at ih
    cases ih; case prod ih => cases ih; case list ih =>
    exact ih (As i) (Range.mem_map_of_mem In)
  . case sumIntro i n Δ E As In EtyA Aki h ih =>
    constructor
    constructor
    intro A AInAs
    simp [List.map_singleton_flatten] at AInAs
    obtain ⟨j, AInAs, A_eq⟩ := AInAs
    subst A_eq
    exact Aki j (by simp_all [Range.mem_of_mem_toList]) |>.TypeVarLocallyClosed_of
  . case sumElim Δ E n As Fs B EtyA FtyAB Bki ih1 ih2 =>
    exact Bki.TypeVarLocallyClosed_of
  . case equiv Δ E A B EtyA eqAB ih =>
    exact eqAB.preserve_lc.1 ih

theorem TermTypeVarLocallyClosed_of (EtyA : [[Δ ⊢ E : A]]) : E.TypeVarLocallyClosed := by
  induction EtyA with
  | var => exact .var
  | lam I E'ty ih =>
    let ⟨x, xnin⟩ := I.exists_fresh
    cases E'ty _ xnin |>.WellFormedness_of
    case _ _ _ Aki =>
    exact .lam Aki.TypeVarLocallyClosed_of <| ih _ xnin |>.TermVar_open_drop
  | app _ _ E'ih Fih => exact .app E'ih Fih
  | typeLam I E'ty ih =>
    let ⟨a, anin⟩ := I.exists_fresh
    exact .typeLam <| ih _ anin |>.weaken |>.TypeVar_open_drop Nat.zero_lt_one
  | typeApp _ Bki ih => exact .typeApp ih Bki.TypeVarLocallyClosed_of
  | prodIntro _ _ _ ih =>
    apply Term.TypeVarLocallyClosed.prodIntro
    intro E mem
    rcases Range.mem_of_mem_map mem with ⟨i, imem, rfl⟩
    exact ih _ imem
  | prodElim _ _ ih => exact .prodElim ih
  | sumIntro _ _ _ _ ih => exact .sumIntro ih
  | sumElim _ _ _ Eih Fih =>
    apply Term.TypeVarLocallyClosed.sumElim Eih
    intro E mem
    rcases Range.mem_of_mem_map mem with ⟨i, imem, rfl⟩
    exact Fih _ imem
  | equiv _ _ ih => exact ih

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
  | prodIntro _ _ _ ih =>
    exact .prodIntro fun E mem => by
      let ⟨i, mem', eq⟩ := Range.mem_of_mem_map mem
      cases eq
      exact ih i mem'
  | prodElim _ _ ih => exact .prodElim ih
  | sumIntro _ _ _ _ ih => exact .sumIntro ih
  | sumElim _ _ _ ih₀ ih₁ =>
    exact .sumElim ih₀ fun i mem => by
      let ⟨i, mem', eq⟩ := Range.mem_of_mem_map mem
      cases eq
      exact ih₁ i mem'
  | equiv Ety' _ ih => exact ih

open Environment in
theorem weakening (h: [[Δ, Δ'' ⊢ E : A]]) (wf: [[⊢ Δ, Δ', Δ'']]): [[Δ, Δ', Δ'' ⊢ E : A]] := by
  generalize Δ_eq : [[ Δ, Δ'' ]] = Δ_ at h
  induction h generalizing Δ Δ'' <;> subst Δ_eq
  case var x T wf' h =>
    refine .var wf ?_
    exact h.weakening <| Environment.append_assoc.subst wf |>.weakening.append_termVar_fresh_l
  case lam T E A I h ih =>
    refine .lam (I := I ++ Δ.termVarDom ++ Δ'.termVarDom ++ Δ''.termVarDom) fun x nin => ?_
    repeat1' rw [append_termExt_assoc]
    refine ih x (by simp_all) ?_ rfl
    simp [append]
    have TkiStar := match h x (by simp_all) |>.WellFormedness_of with |.termVarExt _ _ h => h |>.weakening wf
    exact .termVarExt wf (by simp_all [TermVarNotInDom, TermVarInDom, termVarDom_append]) TkiStar
  case typeLam K E A I EtyA ih =>
    refine .typeLam (I := I ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom) (λ a nin => ?_)
    repeat1' rw [append_typeExt_assoc]
    refine ih a (by simp_all) ?_ rfl
    simp [append]
    exact .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom_append])
  case sumIntro i n E A iltn h EtyA AkiStar ih =>
    exact .sumIntro iltn (ih wf rfl) (λ i' i'ltn => AkiStar i' i'ltn |>.weakening wf) h
  case equiv E A B h AB ih =>
    have EtyA := ih wf rfl
    exact EtyA.equiv <| AB.weakening wf.EnvironmentTypeWellFormedness_of
  all_goals try aesop (add safe constructors Kinding, unsafe constructors Typing, safe forward Kinding.weakening) (config := { enableSimp := false })

open Environment in
theorem Kinding_of (EtyA : [[Δ ⊢ E : A]]) : [[ Δ ⊢ A: * ]] := by
  induction EtyA
  . case var wf xinΔ => exact xinΔ.Kinding_of wf
  . case lam Δ A E B I EtyB ih =>
    have ⟨x, xnin⟩ := I ++ Δ.termVarDom |>.exists_fresh
    let .termVarExt wf _ AkiStar := EtyB x (by simp_all) |>.WellFormedness_of
    exact .arr AkiStar <| ih x (by simp_all) |>.TermVar_drop (Δ'' := [[(ε)]])
  . case app ih1 _ =>
    let .arr _ BkiStar := ih1
    exact BkiStar
  . case typeLam Δ K E A I EtyA ih =>
    exact .scheme (I ++ Δ.typeVarDom) (λ a anin => ih a (by simp_all))
  . case typeApp Δ E K A B EtyA BkiK ih =>
    let .scheme I AkiStar := ih
    have ⟨a, anin⟩ := I ++ Δ.typeVarDom ++ A.freeTypeVars |>.exists_fresh
    specialize AkiStar a (by simp_all)
    rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars (a := a) (by simp_all)]
    exact AkiStar.subst (.typeVarExt EtyA.WellFormedness_of (by simp_all [TypeVarNotInDom, TypeVarInDom])) BkiK
  . case prodIntro Δ n E A b wf EtyA h ih => exact .prod <| .list ih h
  . case prodElim Δ E n A _ i EtyA iltn ih =>
    let .prod h := ih; have AkiStar := h.inv_list.left; clear h
    exact AkiStar i iltn
  . case sumIntro AkiStar h _ => exact .sum <| .list AkiStar h
  . case sumElim BkiStar _ _ =>
    exact BkiStar
  . case equiv Δ E A B EtyA eqAB ih =>
    exact eqAB.TypeEquivalenceS_of ih.TypeVarLocallyClosed_of EtyA.WellFormedness_of
      |>.preservation.mp ih

open Environment in
theorem inv_arr' (Ety: [[Δ ⊢ λ x? : T. E : C ]]) (eqC: [[ Δ ⊢ C ≡ A → B ]])
  : [[ Δ ⊢ T ≡ A ]] ∧ (∃(I: List _), ∀x ∉ I, [[ Δ, x: T ⊢ E^x : B ]]) := by
  generalize T_eq : [[ λ x? : T. E ]] = T_ at Ety
  induction Ety <;> cases T_eq
  . case lam.refl Δ B' I EtyB' _ =>
    have ⟨wf, TkiStar, B'kiStar⟩: _ ∧ _ ∧ _ := (
      have ⟨x, xnin⟩ := I.exists_fresh
      have .termVarExt wf _ TkiStar := EtyB' x xnin |>.WellFormedness_of
      have B'kiStar := EtyB' x xnin |>.Kinding_of.TermVar_drop (Δ'' := [[(ε)]])
      ⟨wf, TkiStar, B'kiStar⟩
    )
    have ⟨eTA, eB'B⟩ := EqSmallStep.of_Equivalence eqC (TkiStar.arr B'kiStar) wf |>.inj_arr
      (.arr TkiStar B'kiStar) wf
    refine ⟨eTA.Equivalence_of, ?_⟩
    refine ⟨I, λ x xnin => ?_⟩
    refine .equiv (EtyB' x (by simp_all)) ?_
    exact eB'B.Equivalence_of.weakening_term' (Δ' := [[(ε)]])
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqC) rfl

theorem inv_arr (Ety: [[Δ ⊢ λ x? : T. E : A → B ]])
  : [[ Δ ⊢ T ≡ A ]] ∧ (∃(I: List _), ∀x ∉ I, [[ Δ, x: T ⊢ E^x : B ]]) := Ety.inv_arr' .refl

open Environment in
theorem inv_forall' (Ety: [[Δ ⊢ Λ a? : K. E : T ]]) (eqT: [[ Δ ⊢ T ≡ ∀ a?: K'. A ]])
  : K = K' ∧ (∃(I: List _), ∀a ∉ I, [[ Δ, a: K ⊢ E^a : A^a ]]) := by
  generalize T_eq : [[ Λ a? : K. E ]] = T_ at Ety
  induction Ety <;> cases T_eq
  . case typeLam.refl Δ A' I EtyA' _ =>
    have wf := (
      have ⟨a, xnin⟩ := I.exists_fresh
      let .typeVarExt wf _ := EtyA' a xnin |>.WellFormedness_of
      wf
    )
    have A'kiStar := Kinding.scheme I (λ a nin => EtyA' a nin |>.Kinding_of)
    have ⟨eqKK', I', eA'A⟩ := EqSmallStep.of_Equivalence eqT A'kiStar wf |>.inj_forall A'kiStar wf
    refine ⟨eqKK', ?_⟩
    have .scheme I'' A'kiStar := A'kiStar
    refine ⟨I ++ I', λ a anin => ?_⟩
    refine .equiv (EtyA' a (by simp_all)) ?_
    exact eA'A a (by simp_all) |>.Equivalence_of
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqT) rfl

theorem inv_forall (Ety: [[Δ ⊢ Λ a? : K. E : ∀ a?: K'. A ]])
  : K = K' ∧ (∃(I: List _), ∀a ∉ I, [[ Δ, a: K ⊢ E^a : A^a ]]) := Ety.inv_forall' .refl

theorem inv_prod' (Ety: [[ Δ ⊢ (</ E@i // i in [:n] />) : T ]])
  (eqT: TypeEquivalence Δ T (.prod (.list ([:n'].map fun i => A i) K?)))
  : n = n' ∧ [[ </ Δ ⊢ E@i : A@i // i in [:n] /> ]] ∧ ∃ b, Option.someIf .star b = K? ∧ (n ≠ 0 ∨ b) := by
  generalize T_eq : [[ (</ E@i // i in [:n] />) ]] = T_ at Ety
  induction Ety <;> try cases T_eq
  . case prodIntro Δ n_ E_ A_ b wf EtyA h ih =>
    clear ih
    injection T_eq with eq
    have eqnn_ := Std.Range.length_eq_of_mem_eq eq; simp at eqnn_; subst n_
    have eqEE_ := Std.Range.eq_of_mem_of_map_eq eq; clear eq
    let ki := (Typing.prodIntro wf EtyA h).Kinding_of
    let .prod ki' := ki
    have ⟨eqn'n, eA_A, K?eq⟩ := EqSmallStep.of_Equivalence eqT
      (by exact .prod (.list (λ i iltn => EtyA i iltn |>.Kinding_of) h)) wf |>.inj_prod ki wf
      |>.inj_list ki' wf
    subst n'
    refine ⟨rfl, λ x xin => ?_, _, K?eq, h⟩
    simp_all
    refine .equiv (EtyA x xin) ?_
    exact eA_A x xin |>.Equivalence_of
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqT) rfl

theorem inv_prod
  (Ety: Typing Δ [[(</ E@i // i in [:n] />)]] (.prod (.list ([:n'].map fun i => A i) K?)))
  : n = n' ∧ [[ </ Δ ⊢ E@i : A@i // i in [:n] /> ]] ∧ ∃ b, Option.someIf .star b = K? ∧ (n ≠ 0 ∨ b) :=
  Ety.inv_prod' .refl

theorem inv_sum' (Ety: [[ Δ ⊢ ι n E : T ]])
  (eqT: TypeEquivalence Δ T (.sum (.list ([:n'].map fun i => A i) K?)))
  : n ∈ [0:n'] ∧ [[ Δ ⊢ E : A@n ]] ∧ ∃ b, Option.someIf .star b = K? ∧ (n' ≠ 0 ∨ b) := by
  generalize T_eq : [[ ι n E ]] = T_ at Ety
  induction Ety <;> cases T_eq
  . case sumIntro.refl n_ Δ A' _ A'kiStar h nin EtyA' ih =>
    clear ih
    have wf := EtyA'.WellFormedness_of
    let ki := (Typing.sumIntro nin EtyA' A'kiStar h).Kinding_of
    let .sum ki' := ki
    have ⟨eqn'n_, eA'A, K?eq⟩ := EqSmallStep.of_Equivalence eqT (K := [[ * ]])
      (by exact .sum (.list (λ i iltn => A'kiStar i iltn) h)) wf |>.inj_sum ki wf
      |>.inj_list ki' wf
    subst n_
    exact ⟨nin, .equiv EtyA' <| eA'A n nin |>.Equivalence_of, _, K?eq, h⟩
  . case equiv.refl _ _ _ eqA'B' _ ih => exact ih (eqA'B'.trans eqT) rfl

theorem inv_sum (Ety: Typing Δ [[ι n E]] (.sum (.list ([:n'].map fun i => A i) K?)))
  : n ∈ [0:n'] ∧ [[ Δ ⊢ E : A@n ]] ∧ ∃ b, Option.someIf .star b = K? ∧ (n' ≠ 0 ∨ b) :=
  Ety.inv_sum' .refl

end Typing

end TabularTypes.«F⊗⊕ω»
