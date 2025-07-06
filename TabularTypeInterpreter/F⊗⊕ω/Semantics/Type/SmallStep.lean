import Lott.Elab.ImpliesJudgement
import Lott.Elab.NotJudgement
import TabularTypeInterpreter.Data.List
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Equivalence
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Basic

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax A " = " B : Type.Eq

def Type.Eq := _root_.Eq (α := «Type»)

judgement_syntax A " ≠ " B : Type.Ne

def Type.Ne := _root_.Ne (α := «Type»)

open Std

judgement_syntax "value " A : Type.IsValue

judgement Type.IsValue where

─────── var {a : TypeVarId}
value a

∀ a ∉ I, value A^a
∀ A', A = A' a$0 ⇒ ¬lc_ A'
────────────────────────── lam (I : List TypeVarId)
value λ a : K. A

∀ a ∉ I, value A^a
────────────────── «forall» (I : List TypeVarId)
value ∀ a : K. A

value A
value B
─────────── arr
value A → B

</ value A@i // i in [:n] />
────────────────────────────── list
value {</ A@i // i in [:n] />}

value A
───────── prod
value ⊗ A

value A
───────── sum
value ⊕ A

value A
───────── varApp {a : TypeVarId}
value a A

value A₀ A₁
value B
─────────────── appApp
value (A₀ A₁) B

value ∀ a : K. A
value B
──────────────────── forallApp
value (∀ a : K. A) B

∀ K, A ≠ λ a : K. a$0
value A
───────────────────── listAppVar {a : TypeVarId}
value A ⟦a⟧

∀ K, A ≠ λ a : K. a$0
value A
value B₀ B₁
───────────────────── listAppApp
value A ⟦B₀ B₁⟧

∀ K, A ≠ λ a : K. a$0
value A
value ∀ a : K. B
───────────────────── listAppForall
value A ⟦∀ a : K. B⟧

judgement_syntax Δ " ⊢ " A " -> " B : SmallStep

judgement SmallStep where

Δ ⊢ A : K₁ ↦ K₂
∀ a ∉ I, value A a
──────────────────────── eta (I : List TypeVarId)
Δ ⊢ λ a : K₁. A a$0 -> A

Δ ⊢ λ a : K₁. A : K₁ ↦ K₂
Δ ⊢ B : K₁
value λ a : K₁. A
value B
─────────────────────────── lamApp
Δ ⊢ (λ a : K₁. A) B -> A^^B

∀ K, A ≠ λ a : K. a$0
Δ ⊢ A : K₁ ↦ K₂
value A
</ value B@i // i in [:n] />
────────────────────────────────────────────────────────────── listAppList
Δ ⊢ A ⟦{</ B@i // i in [:n] />}⟧ -> {</ A B@i // i in [:n] />}

Δ ⊢ A : L K
value A
─────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ -> A

∀ K', A₀ ≠ λ a : K'. a$0
Δ ⊢ A₁ : K₁ ↦ K₂
value A₀
value A₁ ⟦B⟧
────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦A₁ ⟦B⟧⟧ -> (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧

∀ a ∉ I, Δ, a : K ⊢ A^a -> A'^a
─────────────────────────────── lam (I : List TypeVarId)
Δ ⊢ λ a : K. A -> λ a : K. A'

Δ ⊢ A -> A'
─────────────── appl
Δ ⊢ A B -> A' B

value A
Δ ⊢ B -> B'
─────────────── appr
Δ ⊢ A B -> A B'

∀ a ∉ I, Δ, a : K ⊢ A^a -> A'^a
─────────────────────────────── «forall» (I : List TypeVarId)
Δ ⊢ ∀ a : K. A -> ∀ a : K. A'

Δ ⊢ A -> A'
─────────────────── arrl
Δ ⊢ A → B -> A' → B

value A
Δ ⊢ B -> B'
─────────────────── arrr
Δ ⊢ A → B -> A → B'

</ value A₀@i // i in [:m] />
Δ ⊢ A₁ -> A₁'
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────── list
Δ ⊢ {</ A₀@i // i in [:m] />, A₁, </ A₂@j // j in [:n] />} -> {</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] />}

Δ ⊢ A -> A'
─────────────────── listAppl
Δ ⊢ A ⟦B⟧ -> A' ⟦B⟧

value A
Δ ⊢ B -> B'
─────────────────── listAppr
Δ ⊢ A ⟦B⟧ -> A ⟦B'⟧

Δ ⊢ A -> A'
─────────────── prod
Δ ⊢ ⊗ A -> ⊗ A'

Δ ⊢ A -> A'
─────────────── sum
Δ ⊢ ⊕ A -> ⊕ A'

judgement_syntax Δ " ⊢ " A " ->* " B : MultiSmallStep

judgement MultiSmallStep where

─────────── refl
Δ ⊢ A ->* A

Δ ⊢ A₀ -> A₁
Δ ⊢ A₁ ->* A₂
───────────── step
Δ ⊢ A₀ ->* A₂

judgement_syntax Δ " ⊢ " A " ->" n "* " B : IndexedSmallStep

judgement IndexedSmallStep where

─────────── refl
Δ ⊢ A ->0* A

Δ ⊢ A₀ -> A₁
Δ ⊢ A₁ ->n* A₂
──────────────────── step
Δ ⊢ A₀ ->(n + 1)* A₂

judgement_syntax Δ " ⊢ " A " <->* " B : EqSmallStep

judgement EqSmallStep where

──────────── refl
Δ ⊢ A <->* A

Δ ⊢ A -> B
──────────── step
Δ ⊢ A <->* B

Δ ⊢ B <->* A
──────────── symm
Δ ⊢ A <->* B

Δ ⊢ A₀ <->* A₁
Δ ⊢ A₁ <->* A₂
────────────── trans
Δ ⊢ A₀ <->* A₂

attribute [refl] MultiSmallStep.refl EqSmallStep.refl

@[symm]
theorem EqSmallStep.symm' {Δ} A B : [[Δ ⊢ A <->* B]] → [[Δ ⊢ B <->* A]] := symm

namespace Type.IsValue

theorem id : [[value λ a : K. a$0]] :=
  lam [] (fun _ _ => by rw [TypeVar_open, if_pos rfl]; exact var) nofun

theorem list_inversion (h : [[value {</ A@i // i in [:n] />}]]) : ∀ i ∈ [:n], [[value A@i]] := by
  generalize Aseq : [:n].map _ = As at h
  let .list Asv := h
  let lengths_eq : ([:n].map _).length = _ := by rw [Aseq]
  rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at lengths_eq
  cases lengths_eq
  intro i mem
  rw [Range.eq_of_mem_of_map_eq Aseq i mem]
  exact Asv i mem

theorem listAppl_inversion : [[value A ⟦B⟧]] → [[value A]]
  | listAppVar _ Av => Av
  | listAppApp _ Av _ => Av
  | listAppForall _ Av _ => Av

theorem TypeVarLocallyClosed_of (v : IsValue A) : TypeVarLocallyClosed A := by
  induction v
  case lam A' _ I _ _ ih =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    specialize ih a aninI
    apply TypeVarLocallyClosed.TypeVar_close_inc at ih
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at ih
    exact .lam ih
  case «forall» A' _ I _ ih =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    specialize ih a aninI
    apply TypeVarLocallyClosed.TypeVar_close_inc at ih
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at ih
    exact .forall ih
  case list ih =>
    apply TypeVarLocallyClosed.list
    intro A' mem
    rcases Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
    exact ih _ mem'
  all_goals aesop (add simp Type_open, safe constructors TypeVarLocallyClosed, unsafe cases IsValue)

theorem TypeVar_subst_var (v : IsValue A)
  : IsValue (A.TypeVar_subst a (.var (.free a'))) := by
  match A, v with
  | .var _, var =>
    rw [TypeVar_subst]
    split <;> exact var
  | .lam .., lam I A'v h =>
    rename_i A'
    rw [TypeVar_subst]
    apply lam <| a :: I
    · intro a'' a''nin
      let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''nin
      rw [TypeVar_open_TypeVar_subst_var_comm ane.symm]
      exact A'v a'' a''ninI |>.TypeVar_subst_var
    · intro A'' eq
      cases A'
      all_goals rw [TypeVar_subst] at eq
      case a.var => split at eq <;> nomatch eq
      case a.app _ A''' =>
        injection eq with eq' eq''
        cases eq'
        cases A'''
        all_goals rw [TypeVar_subst] at eq''
        case var =>
          split at eq''
          · case isTrue h' =>
            cases h'
            nomatch eq''
          · case isFalse h' =>
            cases eq''
            exact (h _ rfl <| ·.TypeVar_subst_drop)
        all_goals nomatch eq''
      all_goals nomatch eq
  | .app .., varApp B'v =>
    rw [TypeVar_subst, TypeVar_subst]
    split <;> exact varApp B'v.TypeVar_subst_var
  | .app .., appApp A'v B'v =>
    rw [TypeVar_subst]
    let A'v' := A'v.TypeVar_subst_var (a := a) (a' := a')
    rw [TypeVar_subst] at A'v' ⊢
    exact appApp A'v' B'v.TypeVar_subst_var
  | .app .., forallApp A'v B'v =>
    rw [TypeVar_subst]
    let A'v' := A'v.TypeVar_subst_var (a := a) (a' := a')
    rw [TypeVar_subst] at A'v' ⊢
    exact forallApp A'v' B'v.TypeVar_subst_var
  | .forall .., «forall» I A'v =>
    rw [TypeVar_subst]
    apply «forall» <| a :: I
    intro a'' a''nin
    let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''nin
    rw [TypeVar_open_TypeVar_subst_var_comm ane.symm]
    exact A'v a'' a''ninI |>.TypeVar_subst_var
  | .arr .., arr A'v B'v =>
    rw [TypeVar_subst]
    exact arr A'v.TypeVar_subst_var B'v.TypeVar_subst_var
  | .list .., list A'v =>
    rw [TypeVar_subst, List.mapMem_eq_map, List.map_map, ← Range.map]
    apply list
    intro i mem
    simp
    exact A'v i mem |>.TypeVar_subst_var
  | .listApp .., listAppVar ne A'v =>
    rw [TypeVar_subst, TypeVar_subst]
    split <;> exact listAppVar (ne_preservation ne) A'v.TypeVar_subst_var
  | .listApp .., listAppApp ne A'v B'v =>
    rw [TypeVar_subst]
    let B'v' := B'v.TypeVar_subst_var (a := a) (a' := a')
    rw [TypeVar_subst] at B'v' ⊢
    exact listAppApp (ne_preservation ne) A'v.TypeVar_subst_var B'v'
  | .listApp .., listAppForall ne A'v B'v =>
    rw [TypeVar_subst]
    let B'v' := B'v.TypeVar_subst_var (a := a) (a' := a')
    rw [TypeVar_subst] at B'v' ⊢
    exact listAppForall (ne_preservation ne) A'v.TypeVar_subst_var B'v'
  | .prod .., prod A'v =>
    rw [TypeVar_subst]
    exact prod A'v.TypeVar_subst_var
  | .sum .., sum A'v =>
    rw [TypeVar_subst]
    exact sum A'v.TypeVar_subst_var
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  rw [← Range.map]
  exact Range.mem_map_of_mem mem
where
  ne_preservation {A a a'} (ne : ∀ K, A ≠ [[λ a : K. a$0]])
    : ∀ K, A.TypeVar_subst a (.var (.free a')) ≠ [[λ a : K. a$0]] := by
    intro K eq
    specialize ne K
    cases A
    all_goals rw [TypeVar_subst] at eq
    case var => split at eq <;> nomatch eq
    case lam K A' =>
      rcases Type.lam.inj eq with ⟨rfl, eq'⟩
      cases A'
      all_goals rw [TypeVar_subst] at eq'
      case var =>
        split at eq'
        · case isTrue => nomatch eq'
        · case isFalse =>
          cases eq'
          nomatch ne
      all_goals nomatch eq'
    all_goals nomatch eq

theorem TypeVar_open_swap (v : IsValue (TypeVar_open A a)) (aninA : a ∉ A.freeTypeVars)
  : IsValue (TypeVar_open A a') := by
  have : TypeVar_open A a' = TypeVar_subst (TypeVar_open A a) a (.var a') := by
    rw [Type_open_var, Type_open_var, TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
        TypeVar_subst_id_of_not_mem_freeTypeVars aninA, TypeVar_subst, if_pos rfl]
  rw [this]
  exact TypeVar_subst_var v

theorem not_step (v : IsValue A) : ¬[[Δ ⊢ A -> B]] := by
  intro st
  cases v <;> try cases st
  · case lam.eta I Bav _ _ h =>
    let ⟨a, anin⟩ := I.exists_fresh
    let .app Blc _ := Bav a anin |>.TypeVarLocallyClosed_of
    nomatch h _ rfl Blc
  · case lam.lam I v' _ _ I' st' =>
    let ⟨a, anin⟩ := I ++ I' |>.exists_fresh
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
    apply v' a aninI |>.not_step
    exact st' a aninI'
  · case «forall» I v' _ I' st' =>
    let ⟨a, anin⟩ := I ++ I' |>.exists_fresh
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
    apply v' a aninI |>.not_step
    exact st' a aninI'
  · case arr.arrl v' _ _ st' => exact not_step v' st'
  · case arr.arrr _ v' _ _ st' => exact not_step v' st'
  · case list n _ v' =>
    generalize Aseq : [:n].map _ = As at st
    let .list A₀v A₁st (m := m) := st
    let lengths_eq : List.length ([:_].map _) = _ := by rw [Aseq]
    rw [List.length_map, Range.length_toList, Nat.sub_zero, List.length_append, List.length_cons,
        List.length_map, Range.length_toList, Nat.sub_zero, List.length_map, Range.length_toList,
        Nat.sub_zero] at lengths_eq
    cases lengths_eq
    apply v' m ⟨Nat.zero_le _, Nat.lt_add_of_pos_right (Nat.succ_pos _), Nat.mod_one _⟩ |>.not_step
    rcases List.append_eq_map_iff.mp Aseq.symm with ⟨As₀, As₁, eq, eq', eq''⟩
    rcases List.map_eq_cons_iff.mp eq'' with ⟨m', _, rfl, rfl, eq''⟩
    let lengths_eq' : List.length (List.map ..) = _ := by rw [eq']
    rw [List.length_map, List.length_map, Range.length_toList] at lengths_eq'
    cases lengths_eq'
    rw [← Range.toList_append (Nat.zero_le _) (Nat.le_add_right _ _)] at eq
    match List.append_eq_append_iff.mp eq with
    | .inl h =>
      rcases h with ⟨_, eq''', eq''''⟩
      let lengths_eq'' : List.length As₀ = _ := by rw [eq''']
      rw [List.length_append, Range.length_toList, Nat.sub_zero] at lengths_eq''
      cases List.eq_nil_of_length_eq_zero <|
        Nat.add_right_eq_self.mp lengths_eq''.symm
      rw [List.nil_append, Range.toList,
          if_pos (Nat.lt_add_of_pos_right (Nat.succ_pos _))] at eq''''
      injection eq'''' with eq''''
      cases eq''''
      exact A₁st
    | .inr h =>
      rcases h with ⟨_, eq''', eq''''⟩
      let lengths_eq'' : List.length ([:_].toList) = _ := by rw [eq''']
      rw [List.length_append, Range.length_toList, Nat.sub_zero] at lengths_eq''
      cases List.eq_nil_of_length_eq_zero <|
        Nat.add_right_eq_self.mp lengths_eq''.symm
      rw [List.nil_append, Range.toList,
          if_pos (Nat.lt_add_of_pos_right (Nat.succ_pos _))] at eq''''
      injection eq'''' with eq''''
      cases eq''''
      exact A₁st
  · case prod v' _ st' => exact not_step v' st'
  · case sum v' _ st' => exact not_step v' st'
  · case varApp.appl st' => exact not_step var st'
  · case varApp.appr v' _ _ st' => exact not_step v' st'
  · case appApp.appl v' _ _ st' => exact not_step v' st'
  · case appApp.appr v' _ _ st' => exact not_step v' st'
  · case forallApp.appl v' _ _ st' => exact not_step v' st'
  · case forallApp.appr v' _ _ st' => exact not_step v' st'
  · case listAppVar.listAppId K' ne _ _ _ => nomatch ne K'
  · case listAppVar.listAppl v' _ st' => exact not_step v' st'
  · case listAppVar.listAppr st' => exact not_step var st'
  · case listAppApp.listAppId K' ne _ _ _ => nomatch ne K'
  · case listAppApp.listAppl v' _ _ st' => exact not_step v' st'
  · case listAppApp.listAppr v' _ _ st' => exact not_step v' st'
  · case listAppForall.listAppId K' ne _ _ _ => nomatch ne K'
  · case listAppForall.listAppl v' _ _ st' => exact not_step v' st'
  · case listAppForall.listAppr v' _ _ st' => exact not_step v' st'
termination_by sizeOf A
decreasing_by
  all_goals try (
    rename A = _ => eq
    cases eq
    simp_arith
  )
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  apply Range.mem_map_of_mem
  rename_i eq _ _ _ _ _ _ _
  cases eq
  exact ⟨Nat.zero_le _, Nat.lt_add_of_pos_right (Nat.succ_pos _), Nat.mod_one _⟩

end Type.IsValue

local
instance : Inhabited «Type» where
  default := .list []

namespace SmallStep

theorem list' (A₀v : ∀ A ∈ A₀, A.IsValue) (A₁st : [[Δ ⊢ A₁ -> A₁']])
  : SmallStep Δ (.list (A₀ ++ A₁ :: A₂)) (.list (A₀ ++ A₁' :: A₂)) := by
  rw [← Range.map_get!_eq (as := A₀), ← Range.map_get!_eq (as := A₂)]
  exact list (fun i mem => A₀v (A₀.get! i) <| List.get!_mem mem.upper) A₁st

theorem preserve_not_mem_freeTypeVars (st : [[Δ ⊢ A -> B]]) (aninA : a ∉ A.freeTypeVars)
  : a ∉ B.freeTypeVars := by
  induction st
  case lamApp =>
    simp [Type.freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    exact Type.not_mem_freeTypeVars_Type_open_intro aninA' aninB'
  case lam I _ ih =>
    rw [Type.freeTypeVars] at aninA ⊢
    let ⟨a', a'nin⟩ := a :: I |>.exists_fresh
    let ⟨a'ne, a'ninI⟩ := List.not_mem_cons.mp a'nin
    exact Type.not_mem_freeTypeVars_TypeVar_open_drop <|
      ih a' a'ninI (Type.not_mem_freeTypeVars_TypeVar_open_intro aninA a'ne.symm)
  case «forall» I _ ih =>
    rw [Type.freeTypeVars] at aninA ⊢
    let ⟨a', a'nin⟩ := a :: I |>.exists_fresh
    let ⟨a'ne, a'ninI⟩ := List.not_mem_cons.mp a'nin
    exact Type.not_mem_freeTypeVars_TypeVar_open_drop <|
      ih a' a'ninI (Type.not_mem_freeTypeVars_TypeVar_open_intro aninA a'ne.symm)
  all_goals aesop (add simp [Type.freeTypeVars])

theorem preserve_lc : [[Δ ⊢ A -> B]] → A.TypeVarLocallyClosed → B.TypeVarLocallyClosed
  | eta I _ Bav, _ =>
    let ⟨a, anin⟩ := I.exists_fresh
    let .app Bv _ := Bav a anin |>.TypeVarLocallyClosed_of
    Bv
  | lamApp .., .app (.lam A'lc) B'lc => A'lc.Type_open_dec B'lc
  | listAppList .., .listApp A'lc (.list B'lc) => by
    apply Type.TypeVarLocallyClosed.list
    intro B' mem
    rcases Range.mem_of_mem_map mem with ⟨i, mem', rfl⟩
    exact .app A'lc <| B'lc _ <| Range.mem_map_of_mem mem'
  | listAppId .., .listApp _ B'lc => B'lc
  | listAppComp .., .listApp A₀lc (.listApp A₁lc B'lc) =>
    .listApp (.lam (.app A₀lc.weaken (.app A₁lc.weaken (.var_bound Nat.one_pos)))) B'lc
  | lam I A'st (A' := A''), .lam A'lc => by
    let ⟨a, anin⟩ := A''.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA'', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A''lc := A'st a aninI |>.preserve_lc A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A''lc
    exact .lam A''lc
  | appl A'st, .app A'lc B'lc => .app (A'st.preserve_lc A'lc) B'lc
  | appr _ B'st, .app A'lc B'lc => .app A'lc (B'st.preserve_lc B'lc)
  | .forall I A'st (A' := A''), .forall A'lc => by
    let ⟨a, anin⟩ := A''.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA'', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A''lc := A'st a aninI |>.preserve_lc A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A''lc
    exact .forall A''lc
  | arrl A'st, .arr A'lc B'lc => .arr (A'st.preserve_lc A'lc) B'lc
  | arrr _ B'st, .arr A'lc B'lc => .arr A'lc (B'st.preserve_lc B'lc)
  | list _ A'st, .list A'lc => by
    apply Type.TypeVarLocallyClosed.list
    intro A' mem
    match List.mem_append.mp mem with
    | .inl mem' => exact A'lc _ <| List.mem_append.mpr <| .inl mem'
    | .inr (.head _) => exact A'st.preserve_lc <| A'lc _ <| List.mem_append.mpr <| .inr <| .head ..
    | .inr (.tail _ mem') => exact A'lc _ <| List.mem_append.mpr <| .inr <| mem'.tail _
  | listAppl A'st, .listApp A'lc B'lc => .listApp (A'st.preserve_lc A'lc) B'lc
  | listAppr _ B'st, .listApp A'lc B'lc => .listApp A'lc (B'st.preserve_lc B'lc)
  | prod A'st, .prod A'lc => .prod <| A'st.preserve_lc A'lc
  | sum A'st, .sum A'lc => .sum <| A'st.preserve_lc A'lc

theorem preserve_lc_rev : [[Δ ⊢ A -> B]] → B.TypeVarLocallyClosed → A.TypeVarLocallyClosed
  | eta .., Blc => .lam <| .app Blc.weaken <| .var_bound Nat.one_pos
  | lamApp _ _ _ B'v .., Blc =>
    .app (.lam (Blc.weaken (n := 1).Type_open_drop Nat.one_pos)) B'v.TypeVarLocallyClosed_of
  | listAppList _ A'v .., .list Blc' => by
    refine .listApp A'v.TypeVarLocallyClosed_of <| .list ?_
    intro _ mem
    rcases Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
    let .app _ B'lc := Blc' _ <| Range.mem_map_of_mem mem'
    exact B'lc
  | listAppId .., A'lc => .listApp (.lam (.var_bound Nat.one_pos)) A'lc
  | listAppComp _ _ A₀v A₁B'v, .listApp (.lam (.app A₀lc (.app A₁lc _))) B'lc =>
    let .listApp A₁lc _ := A₁B'v.TypeVarLocallyClosed_of
    .listApp A₀v.TypeVarLocallyClosed_of <| .listApp A₁lc B'lc
  | lam I A'st (A := A'), .lam A'lc => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A'lc := A'st a aninI |>.preserve_lc_rev A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact .lam A'lc
  | appl A'st, .app A'lc B'lc => .app (A'st.preserve_lc_rev A'lc) B'lc
  | appr _ B'st, .app A'lc B'lc => .app A'lc (B'st.preserve_lc_rev B'lc)
  | .forall I A'st (A := A'), .forall A'lc => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A'lc := A'st a aninI |>.preserve_lc_rev A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact .forall A'lc
  | arrl A'st, .arr A'lc B'lc => .arr (A'st.preserve_lc_rev A'lc) B'lc
  | arrr _ B'st, .arr A'lc B'lc => .arr A'lc (B'st.preserve_lc_rev B'lc)
  | list _ A'st, .list A'lc => by
    apply Type.TypeVarLocallyClosed.list
    intro A' mem
    match List.mem_append.mp mem with
    | .inl mem' => exact A'lc _ <| List.mem_append.mpr <| .inl mem'
    | .inr (.head _) =>
      exact A'st.preserve_lc_rev <| A'lc _ <| List.mem_append.mpr <| .inr <| .head ..
    | .inr (.tail _ mem') => exact A'lc _ <| List.mem_append.mpr <| .inr <| mem'.tail _
  | listAppl A'st, .listApp A'lc B'lc => .listApp (A'st.preserve_lc_rev A'lc) B'lc
  | listAppr _ B'st, .listApp A'lc B'lc => .listApp A'lc (B'st.preserve_lc_rev B'lc)
  | prod A'st, .prod A'lc => .prod <| A'st.preserve_lc_rev A'lc
  | sum A'st, .sum A'lc => .sum <| A'st.preserve_lc_rev A'lc

open «Type» in
theorem TypeVar_subst_var (Ast : [[Δ, a : K, Δ' ⊢ A -> B]]) (a'ninΔ : [[a' ∉ dom(Δ)]])
  (aninΔ' : [[a ∉ dom(Δ')]] := by nofun) (a'ninΔ' : [[a' ∉ dom(Δ')]] := by nofun)
  : [[Δ, a' : K, Δ' ⊢ A[a' / a] -> B[a' / a] ]] := by match Ast with
  | eta I Bki Bav (K₂ := K₂) =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, if_neg nofun]
    apply eta (a :: I) _ (K₂ := K₂)
    · intro a'' a''nin
      let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''nin
      let Bav' := Bav a'' a''ninI |>.TypeVar_subst_var (a := a) (a' := a')
      rw [TypeVar_subst, TypeVar_subst, if_neg (ane.symm <| TypeVar.free.inj ·)] at Bav'
      exact Bav'
    · exact Bki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | lamApp A'ki B'ki A'v B'v =>
    rw [TypeVar_subst, TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free]
    let A'v' := A'v.TypeVar_subst_var (a := a) (a' := a')
    let A'ki' := A'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
    rw [TypeVar_subst] at A'v' A'ki' ⊢
    exact lamApp A'ki' (B'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ') A'v' B'v.TypeVar_subst_var
  | listAppList ne A'ki A'v B'v (K₁ := K₁) (K₂ := K₂) =>
    rename_i A' _ B'
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, List.mapMem_eq_map, List.mapMem_eq_map,
        List.map_map, List.map_map, ← Range.map, ← Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = (B' i).TypeVar_subst a (.var a')
      simp
    ), Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = (A'.TypeVar_subst a (.var a')).app ((B' i).TypeVar_subst a (.var a'))
      simp [TypeVar_subst]
    )]
    exact listAppList (ne_preservation ne) (A'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ')
      A'v.TypeVar_subst_var (B'v · · |>.TypeVar_subst_var)
  | listAppId A'ki A'v =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, if_neg nofun]
    exact listAppId (A'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ') A'v.TypeVar_subst_var
  | listAppComp ne A₁ki A₀v A₁B'v =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst,
        TypeVar_subst]
    apply Type.IsValue.TypeVar_subst_var at A₁B'v
    rw [TypeVar_subst] at A₁B'v
    exact listAppComp (ne_preservation ne) (A₁ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ')
      A₀v.TypeVar_subst_var A₁B'v
  | lam I A'v =>
    rw [TypeVar_subst, TypeVar_subst]
    apply lam <| a :: a' :: I
    intro a'' a''nin
    let ⟨ane, a''nina'I⟩ := List.not_mem_cons.mp a''nin
    let ⟨a'ne, a''ninI⟩ := List.not_mem_cons.mp a''nina'I
    rw [TypeVar_open_TypeVar_subst_var_comm ane.symm, TypeVar_open_TypeVar_subst_var_comm ane.symm]
    specialize A'v a'' a''ninI
    rw [← Environment.append] at A'v ⊢
    apply A'v.TypeVar_subst_var a'ninΔ _ _
    all_goals rw [Environment.TypeVarNotInDom, Environment.TypeVarInDom, Environment.typeVarDom]
    · exact List.not_mem_cons.mpr ⟨ane.symm, aninΔ'⟩
    · exact List.not_mem_cons.mpr ⟨a'ne.symm, a'ninΔ'⟩
  | appl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact appl <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | appr A'v B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact appr A'v.TypeVar_subst_var <| B'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | .forall I A'v =>
    rw [TypeVar_subst, TypeVar_subst]
    apply «forall» <| a :: a' :: I
    intro a'' a''nin
    let ⟨ane, a''nina'I⟩ := List.not_mem_cons.mp a''nin
    let ⟨a'ne, a''ninI⟩ := List.not_mem_cons.mp a''nina'I
    rw [TypeVar_open_TypeVar_subst_var_comm ane.symm, TypeVar_open_TypeVar_subst_var_comm ane.symm]
    specialize A'v a'' a''ninI
    rw [← Environment.append] at A'v ⊢
    apply A'v.TypeVar_subst_var a'ninΔ _ _
    all_goals rw [Environment.TypeVarNotInDom, Environment.TypeVarInDom, Environment.typeVarDom]
    · exact List.not_mem_cons.mpr ⟨ane.symm, aninΔ'⟩
    · exact List.not_mem_cons.mpr ⟨a'ne.symm, a'ninΔ'⟩
  | arrl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact arrl <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | arrr A'v B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact arrr A'v.TypeVar_subst_var <| B'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | list A₀v A₁st =>
    rw [TypeVar_subst, List.mapMem_eq_map, List.map_append, List.map_cons, List.map_map,
        List.map_map, ← Range.map, ← Range.map, TypeVar_subst, List.mapMem_eq_map, List.map_append,
        List.map_cons, List.map_map, List.map_map, ← Range.map, ← Range.map]
    apply list _ <| A₁st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
    intro i mem
    simp
    exact A₀v i mem |>.TypeVar_subst_var
  | listAppl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact listAppl <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | listAppr A'v B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact listAppr A'v.TypeVar_subst_var <| B'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | prod A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact prod <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | sum A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact sum <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| List.mem_append.mpr <| .inr <| .head _
where
  ne_preservation {A a a'} : (∀ K, A ≠ [[λ a : K. a$0]]) →
    ∀ K, A.TypeVar_subst a (.var (.free a')) ≠ [[λ a : K. a$0]] :=
    IsValue.TypeVar_subst_var.ne_preservation

theorem TypeVar_open_swap (Ast : [[Δ, a' : K ⊢ A^a' -> A']]) (Alc : A.TypeVarLocallyClosed 1)
  (a'ninA : a' ∉ A.freeTypeVars) (aninΔ : [[a ∉ dom(Δ)]]) : [[Δ, a : K ⊢ A^a -> (\a'^A')^a]] := by
  have : A.TypeVar_open a = (A.TypeVar_open a').TypeVar_subst a' (.var a) := by
    rw [Type.Type_open_var, Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars a'ninA, Type.TypeVar_subst, if_pos rfl]
  rw [this]
  let Aoplc := Alc.Type_open_dec .var_free (B := .var a')
  rw [← Type.Type_open_var] at Aoplc
  have : (A'.TypeVar_close a').TypeVar_open a = A'.TypeVar_subst a' (.var a) := by
    rw [Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst <|
          Ast.preserve_lc Aoplc]
  rw [this]
  exact Ast.TypeVar_subst_var aninΔ nofun nofun (Δ' := .empty)

theorem weakening (ΔΔ'Δ''wf : [[⊢ Δ, Δ', Δ'']]) : [[Δ, Δ'' ⊢ A -> B]] → [[Δ, Δ', Δ'' ⊢ A -> B]]
  | eta I A'ki A'av => eta I (A'ki.weakening ΔΔ'Δ''wf) A'av
  | lamApp A'ki B'ki A'v B'v => lamApp (A'ki.weakening ΔΔ'Δ''wf) (B'ki.weakening ΔΔ'Δ''wf) A'v B'v
  | listAppList ne A'ki A'v B'v => listAppList ne (A'ki.weakening ΔΔ'Δ''wf) A'v B'v
  | listAppId A'ki A'v => listAppId (A'ki.weakening ΔΔ'Δ''wf) A'v
  | listAppComp ne A₁ki A₀v A₁B'v => listAppComp ne (A₁ki.weakening ΔΔ'Δ''wf) A₀v A₁B'v
  | lam I A'st (K := K) => by
    apply lam <| I ++ [[Δ, Δ', Δ'']].typeVarDom
    intro a anin
    let ⟨aninI, aninΔΔ'Δ''⟩ := List.not_mem_append'.mp anin
    specialize A'st a aninI
    let ΔΔ'Δ''awf := ΔΔ'Δ''wf.typeVarExt aninΔΔ'Δ'' (K := K)
    rw [← Environment.append] at ΔΔ'Δ''awf ⊢
    rw [← Environment.append] at A'st ΔΔ'Δ''awf ⊢
    exact A'st.weakening ΔΔ'Δ''awf
  | appl A'st => appl <| A'st.weakening ΔΔ'Δ''wf
  | appr A'v B'st => appr A'v <| B'st.weakening ΔΔ'Δ''wf
  | «forall» I A'st (K := K) => by
    apply «forall» <| I ++ [[Δ, Δ', Δ'']].typeVarDom
    intro a anin
    let ⟨aninI, aninΔΔ'Δ''⟩ := List.not_mem_append'.mp anin
    specialize A'st a aninI
    let ΔΔ'Δ''awf := ΔΔ'Δ''wf.typeVarExt aninΔΔ'Δ'' (K := K)
    rw [← Environment.append] at ΔΔ'Δ''awf ⊢
    rw [← Environment.append] at A'st ΔΔ'Δ''awf ⊢
    exact A'st.weakening ΔΔ'Δ''awf
  | arrl A'st => arrl <| A'st.weakening ΔΔ'Δ''wf
  | arrr A'v B'st => arrr A'v <| B'st.weakening ΔΔ'Δ''wf
  | list A₀v A₁st => list A₀v <| A₁st.weakening ΔΔ'Δ''wf
  | listAppl A'st => listAppl <| A'st.weakening ΔΔ'Δ''wf
  | listAppr A'v B'st => listAppr A'v <| B'st.weakening ΔΔ'Δ''wf
  | prod A'st => prod <| A'st.weakening ΔΔ'Δ''wf
  | sum A'st => sum <| A'st.weakening ΔΔ'Δ''wf
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem Environment_TypeVar_subst_swap : [[Δ, Δ'[B / a] ⊢ A -> A']] → [[Δ, Δ'[B' / a] ⊢ A -> A']]
  | eta I A'ki A'av => eta I A'ki.Environment_TypeVar_subst_swap A'av
  | lamApp A'ki B'ki A'v B'v => lamApp A'ki.Environment_TypeVar_subst_swap B'ki.Environment_TypeVar_subst_swap A'v B'v
  | listAppList ne A'ki A'v B'v => listAppList ne A'ki.Environment_TypeVar_subst_swap A'v B'v
  | listAppId A'ki A'v => listAppId A'ki.Environment_TypeVar_subst_swap A'v
  | listAppComp ne A₁ki A₀v A₁B'v => listAppComp ne A₁ki.Environment_TypeVar_subst_swap A₀v A₁B'v
  | lam I A'st => by
    apply lam I
    intro a' a'nin
    specialize A'st a' a'nin
    rw [← Environment.append, ← Environment.TypeVar_subst] at A'st ⊢
    exact A'st.Environment_TypeVar_subst_swap
  | appl A'st => appl A'st.Environment_TypeVar_subst_swap
  | appr A'v B'st => appr A'v B'st.Environment_TypeVar_subst_swap
  | «forall» I A'st => by
    apply «forall» I
    intro a' a'nin
    specialize A'st a' a'nin
    rw [← Environment.append, ← Environment.TypeVar_subst] at A'st ⊢
    exact A'st.Environment_TypeVar_subst_swap
  | arrl A'st => arrl A'st.Environment_TypeVar_subst_swap
  | arrr A'v B'st => arrr A'v B'st.Environment_TypeVar_subst_swap
  | list A₀v A₁st => list A₀v A₁st.Environment_TypeVar_subst_swap
  | listAppl A'st => listAppl A'st.Environment_TypeVar_subst_swap
  | listAppr A'v B'st => listAppr A'v B'st.Environment_TypeVar_subst_swap
  | prod A'st => prod A'st.Environment_TypeVar_subst_swap
  | sum A'st => sum A'st.Environment_TypeVar_subst_swap
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem TypeVar_drop_of_not_mem_freeTypeVars (aninA : a ∉ A.freeTypeVars)
  (st : [[Δ, a : K, Δ' ⊢ A -> B]]) : [[Δ, Δ' ⊢ A -> B]] := by
  cases st <;> simp [Type.freeTypeVars] at aninA
  · case eta I A'av A'ki => exact eta I (A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA) A'av
  · case lamApp A'v B'v A'ki B'ki =>
    let ⟨aninA', aninB'⟩ := aninA
    apply lamApp (A'ki.TypeVar_drop_of_not_mem_freeTypeVars _)
      (B'ki.TypeVar_drop_of_not_mem_freeTypeVars aninB') A'v B'v
    simp [Type.freeTypeVars]
    exact aninA'
  · case listAppList ne A'v B'v A'ki =>
    exact listAppList ne (A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA.left) A'v B'v
  · case listAppId A'v A'ki => exact listAppId (A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA) A'v
  · case listAppComp ne A₀v A₁B'v A₁ki =>
    exact listAppComp ne (A₁ki.TypeVar_drop_of_not_mem_freeTypeVars aninA.right.left) A₀v A₁B'v
  · case lam I A'st =>
    apply lam <| a :: I
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'st a' a'ninI
    rw [← Environment.append] at A'st ⊢
    apply A'st.TypeVar_drop_of_not_mem_freeTypeVars <|
      Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  · case appl A'st => exact appl <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case appr A'v B'st => exact appr A'v <| B'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right
  · case «forall» I A'st =>
    apply «forall» <| a :: I
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'st a' a'ninI
    rw [← Environment.append] at A'st ⊢
    apply A'st.TypeVar_drop_of_not_mem_freeTypeVars <|
      Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  · case arrl A'st => exact arrl <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case arrr A'v B'st => exact arrr A'v <| B'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right
  · case list A₀v A₁st =>
    exact list A₀v <| A₁st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right.left
  · case listAppl A'st => exact listAppl <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case listAppr A'v B'st =>
    exact listAppr A'v <| B'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right
  · case prod A'st => exact prod <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA
  · case sum A'st => exact sum <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA
termination_by sizeOf A
decreasing_by
  all_goals (
    rename A = _ => eq
    cases eq
    simp_arith
  )
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem deterministic : [[Δ ⊢ A -> B]] → [[Δ ⊢ A -> C]] → B = C
  | .eta .., .eta .. => rfl
  | .eta I _ Bav, .lam I' A'st => by
    let ⟨a, anin⟩ := I ++ I' |>.exists_fresh
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
    specialize Bav a aninI
    specialize A'st a aninI'
    let .app Blc _ := Bav.TypeVarLocallyClosed_of
    rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl, Blc.TypeVar_open_id] at A'st
    nomatch Bav.not_step A'st
  | .lamApp _ _ A'v B'v, st => match st with
    | .appl A'st => nomatch A'v.not_step A'st
    | .appr _ B'st => nomatch B'v.not_step B'st
    | .lamApp _ _ _ _ => rfl
  | .listAppList ne _ A'v B'v (n := n), st => by
    generalize Bseq : [:n].map _ = Bs at st
    match st with
    | .listAppList .. =>
      let lengths_eq : ([:n].map _).length = _ := by rw [Bseq]
      rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList,
          Nat.sub_zero, Nat.sub_zero] at lengths_eq
      cases lengths_eq
      apply Type.list.injEq .. |>.mpr
      rw [Range.map, Range.map]
      apply Range.map_eq_of_eq_of_mem
      intro i mem
      apply Type.app.injEq .. |>.mpr ⟨rfl, _⟩
      exact Range.eq_of_mem_of_map_eq Bseq i mem
    | .listAppId _ _ (K := K) => nomatch ne K
    | .listAppl A'st => nomatch A'v.not_step A'st
    | .listAppr _ B'st =>
      cases Bseq
      nomatch Type.IsValue.not_step (.list B'v) B'st
  | .listAppId _ B'v (K := K), st => match st with
    | .listAppList ne _ _ _ => nomatch ne K
    | .listAppId _ _ => rfl
    | .listAppComp ne _ _ _ => nomatch ne K
    | .listAppl A'st => nomatch Type.IsValue.not_step .id A'st
    | .listAppr _ B'st => nomatch B'v.not_step B'st
  | .listAppComp ne A₁ki A₀v A₁Bv, st => match st with
    | .listAppId _ _ (K := K') => nomatch ne K'
    | .listAppComp _ A₁ki' .. => by
      cases A₁ki.arr_deterministic A₁ki'
      rfl
    | .listAppl A₀st => nomatch A₀v.not_step A₀st
    | .listAppr _ A₁Bst => nomatch A₁Bv.not_step A₁Bst
  | .lam I' A'st, .eta I _ Bav => by
    let ⟨a, anin⟩ := I ++ I' |>.exists_fresh
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
    specialize Bav a aninI
    specialize A'st a aninI'
    let .app Blc _ := Bav.TypeVarLocallyClosed_of
    rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl, Blc.TypeVar_open_id] at A'st
    nomatch Bav.not_step A'st
  | .lam I A'st, .lam I' A''st => by
    rename_i A' A''
    let ⟨a, anin⟩ := A'.freeTypeVars ++ A''.freeTypeVars ++ I ++ I' |>.exists_fresh
    let ⟨aninA'A''I, aninI'⟩ := List.not_mem_append'.mp anin
    let ⟨aninA'A'', aninI⟩ := List.not_mem_append'.mp aninA'A''I
    let ⟨aninA', aninA''⟩ := List.not_mem_append'.mp aninA'A''
    exact Type.lam.injEq .. |>.mpr ⟨
      rfl,
      Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA'' <|
        A'st a aninI |>.deterministic <| A''st a aninI'
    ⟩
  | .appl A'st, st => match st with
    | .appl A'st' => Type.app.injEq .. |>.mpr ⟨A'st.deterministic A'st', rfl⟩
    | .appr A'v _ => nomatch A'v.not_step A'st
    | .lamApp _ _ A'v _ => nomatch A'v.not_step A'st
  | .appr A'v B'st, st => match st with
    | .appl A'st => nomatch A'v.not_step A'st
    | .appr _ B'st' => Type.app.injEq .. |>.mpr ⟨rfl, B'st.deterministic B'st'⟩
    | .lamApp _ _ _ B'v => nomatch B'v.not_step B'st
  | .forall I A'st, .forall I' A''st => by
    rename_i A' A''
    let ⟨a, anin⟩ := A'.freeTypeVars ++ A''.freeTypeVars ++ I ++ I' |>.exists_fresh
    let ⟨aninA'A''I, aninI'⟩ := List.not_mem_append'.mp anin
    let ⟨aninA'A'', aninI⟩ := List.not_mem_append'.mp aninA'A''I
    let ⟨aninA', aninA''⟩ := List.not_mem_append'.mp aninA'A''
    exact Type.forall.injEq .. |>.mpr ⟨
      rfl,
      Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA'' <|
        A'st a aninI |>.deterministic <| A''st a aninI'
    ⟩
  | .arrl A'st, st => match st with
    | .arrl A'st' => Type.arr.injEq .. |>.mpr ⟨A'st.deterministic A'st', rfl⟩
    | .arrr A'v _ => nomatch A'v.not_step A'st
  | .arrr A'v B'st, st => match st with
    | .arrl A'st => nomatch A'v.not_step A'st
    | .arrr _ B'st' => Type.arr.injEq .. |>.mpr ⟨rfl, B'st.deterministic B'st'⟩
  | .list A₀v A₁st (m := m) (n := n), st => by
    generalize A'seq : _ ++ _ :: _ = A's at st
    let .list A₀v' A₁st' (m := m') (n := n') := st
    apply Type.list.injEq .. |>.mpr
    match Nat.lt_trichotomy m m' with
    | .inl mlt =>
      exfalso
      apply Type.IsValue.not_step _ A₁st
      convert A₀v' m ⟨Nat.zero_le _, mlt, Nat.mod_one _⟩
      match List.append_eq_append_iff.mp A'seq with
      | .inl h =>
        rcases h with ⟨A''s, eq₀, eq₁⟩
        let lengths_eq : List.length ([:_].map _) = _ := by rw [eq₀]
        rw [List.length_append, List.length_map, List.length_map, Range.length_toList,
            Range.length_toList, Nat.sub_zero, Nat.sub_zero] at lengths_eq
        have : m < m + A''s.length := by
          rwa [lengths_eq] at mlt
        rcases List.exists_cons_of_length_pos <| Nat.pos_of_lt_add_right this with ⟨_, _, rfl⟩
        rw [List.cons_append] at eq₁
        rw [Range.map, Range.map, ← Range.map_append (Nat.zero_le _) mlt.le] at eq₀
        let eq₀' := And.right <| List.append_inj eq₀ <| by
          rw [List.length_map, List.length_map, Range.length_toList]
        rw [← Range.map, Range.map_eq_cons_of_lt mlt] at eq₀'
        rcases List.cons.inj eq₀' with ⟨rfl, _⟩
        exact List.cons.inj eq₁ |>.left
      | .inr h =>
        rcases h with ⟨A''s, eq₀, eq₁⟩
        let lengths_eq : List.length ([:_].map _) = _ := by rw [eq₀]
        rw [List.length_append, List.length_map, List.length_map, Range.length_toList,
            Range.length_toList, Nat.sub_zero, Nat.sub_zero] at lengths_eq
        nomatch Nat.not_le.mpr mlt <| Nat.le_of_add_right_le <| Nat.le_of_eq lengths_eq.symm
    | .inr (.inl meq) =>
      cases meq
      cases List.append_eq_append_iff.mp A'seq
      all_goals (
        case _ h =>
        rcases h with ⟨A''s, eq₀, eq₁⟩
        let lengths_eq : List.length ([:_].map _) = _ := by rw [eq₀]
        rw [List.length_append, List.length_map, List.length_map, Range.length_toList,
            Nat.sub_zero] at lengths_eq
        cases List.eq_nil_of_length_eq_zero <| Nat.add_eq_left.mp lengths_eq.symm
        rw [List.append_nil] at eq₀
        rw [List.nil_append] at eq₁
        rcases List.cons.inj eq₁ with ⟨rfl, eq₁'⟩
        refine List.append_eq_append ?_ <| List.cons.injEq .. |>.mpr ⟨A₁st.deterministic A₁st', ?_⟩
        all_goals simp [eq₀, eq₁']
      )
    | .inr (.inr m'lt) =>
      exfalso
      apply Type.IsValue.not_step _ A₁st'
      convert A₀v m' ⟨Nat.zero_le _, m'lt, Nat.mod_one _⟩
      match List.append_eq_append_iff.mp A'seq with
      | .inl h =>
        rcases h with ⟨A''s, eq₀, eq₁⟩
        let lengths_eq : List.length ([:_].map _) = _ := by rw [eq₀]
        rw [List.length_append, List.length_map, List.length_map, Range.length_toList,
            Range.length_toList, Nat.sub_zero, Nat.sub_zero] at lengths_eq
        nomatch Nat.not_le.mpr m'lt <| Nat.le_of_add_right_le <| Nat.le_of_eq lengths_eq.symm
      | .inr h =>
        rcases h with ⟨A''s, eq₀, eq₁⟩
        let lengths_eq : List.length ([:_].map _) = _ := by rw [eq₀]
        rw [List.length_append, List.length_map, List.length_map, Range.length_toList,
            Range.length_toList, Nat.sub_zero, Nat.sub_zero] at lengths_eq
        have : m' < m' + A''s.length := by
          rwa [lengths_eq] at m'lt
        rcases List.exists_cons_of_length_pos <| Nat.pos_of_lt_add_right this with ⟨_, _, rfl⟩
        rw [List.cons_append] at eq₁
        rw [Range.map, Range.map, ← Range.map_append (Nat.zero_le _) m'lt.le] at eq₀
        let eq₀' := And.right <| List.append_inj eq₀ <| by
          rw [List.length_map, List.length_map, Range.length_toList]
        rw [← Range.map, Range.map_eq_cons_of_lt m'lt] at eq₀'
        rcases List.cons.inj eq₀' with ⟨rfl, _⟩
        exact List.cons.inj eq₁ |>.left
  | .listAppl A'st, st => match st with
    | .listAppList _ _ A'v _ => nomatch A'v.not_step A'st
    | .listAppId _ B'v => nomatch Type.IsValue.not_step .id A'st
    | .listAppComp _ _ A'v _ => nomatch A'v.not_step A'st
    | .listAppl A'st' => Type.listApp.injEq .. |>.mpr ⟨A'st.deterministic A'st', rfl⟩
    | .listAppr A'v _ => nomatch A'v.not_step A'st
  | .listAppr A'v B'st, st => match st with
    | .listAppList _ _ _ B'v => nomatch Type.IsValue.not_step (.list B'v) B'st
    | .listAppId _ B'v => nomatch B'v.not_step B'st
    | .listAppComp _ _ _ B'v => nomatch B'v.not_step B'st
    | .listAppl A'st => nomatch A'v.not_step A'st
    | .listAppr _ B'st' => Type.listApp.injEq .. |>.mpr ⟨rfl, B'st.deterministic B'st'⟩
  | .prod st, .prod st' => Type.prod.injEq .. |>.mpr <| st.deterministic st'
  | .sum st, .sum st' => Type.sum.injEq .. |>.mpr <| st.deterministic st'
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| List.mem_append.mpr <| .inr <| .head _
  · rename (_ : «Type») = _ => eq
    cases eq
    exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| List.mem_append.mpr <| .inr <| .head _

theorem progress (Aki : [[Δ ⊢ A : K]]) : A.IsValue ∨ ∃ B, [[Δ ⊢ A -> B]] := match A, Aki with
  | .var _, .var _ => .inl .var
  | .lam K A', .lam I A'ki => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    match progress <| A'ki a aninI with
    | .inl A'v =>
      by_cases ∃ A'', A' = [[A'' a$0]] ∧ A''.TypeVarLocallyClosed
      · case pos h =>
        rcases h with ⟨A'', rfl, A''lc⟩
        specialize A'ki a aninI
        rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl, A''lc.TypeVar_open_id] at A'ki
        let .app A''ki (.var .head) := A'ki
        simp [Type.freeTypeVars] at aninA'
        refine .inr ⟨
          _,
          .eta [] (A''ki.TypeVar_drop_of_not_mem_freeTypeVars aninA' (Δ' := .empty)) ?_
        ⟩
        intro a' _
        apply Type.IsValue.TypeVar_subst_var (a := a) (a' := a') at A'v
        simp [Type.TypeVar_open, A''lc.TypeVar_open_id, Type.TypeVar_subst,
              Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA'] at A'v
        exact A'v
      · case neg h =>
        refine .inl <| .lam [] (fun _ _ => A'v.TypeVar_open_swap aninA') ?_
        apply not_exists.mp at h
        intro A'' eq
        specialize h A''
        apply not_and_or.mp at h
        match h with
        | .inl ne => nomatch ne eq
        | .inr notlc => exact notlc
    | .inr ⟨A'', A'st⟩ =>
      refine .inr ⟨.lam K (A''.TypeVar_close a), .lam (↑a :: I ++ Δ.typeVarDom) ?_⟩
      intro a' a'nin
      let ⟨a'ninaI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
      let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'ninaI
      let A'lc := A'ki a aninI |>.TypeVarLocallyClosed_of
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst <|
            A'st.preserve_lc A'lc,
          ← Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA' (n := 0),
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst A'lc]
      apply TypeVar_subst_var A'st a'ninΔ nofun nofun (Δ' := .empty)
  | .app A' B', .app A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => by
        cases A'ki with
        | var => exact .inl <| .varApp B'v
        | lam I A''ki => exact .inr ⟨_, .lamApp (.lam I A''ki) B'ki A'v B'v⟩
        | app => exact .inl <| .appApp A'v B'v
        | scheme => exact .inl <| .forallApp A'v B'v
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .appr A'v B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .appl A'st⟩
  | .forall K A', .scheme I A'ki => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    match progress <| A'ki a aninI with
    | .inl A'v => exact .inl <| .forall A'.freeTypeVars fun _ _ => A'v.TypeVar_open_swap aninA'
    | .inr ⟨A'', A'st⟩ =>
      refine .inr ⟨.forall K (A''.TypeVar_close a), .forall (↑a :: I ++ Δ.typeVarDom) ?_⟩
      intro a' a'nin
      let ⟨a'ninaI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
      let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'ninaI
      let A'lc := A'ki a aninI |>.TypeVarLocallyClosed_of
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst <|
            A'st.preserve_lc A'lc,
          ← Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA' (n := 0),
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst A'lc]
      exact TypeVar_subst_var A'st a'ninΔ (Δ' := .empty)
  | .arr A' B', .arr A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => .inl <| .arr A'v B'v
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .arrr A'v B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .arrl A'st⟩
  | .list A's, Aki => by
    rw [← Range.map_get!_eq (as := A's)] at Aki
    rcases Aki.inv_list' with ⟨_, rfl, A'ki⟩
    clear Aki
    rw [← List.reverse_reverse A's] at *
    generalize A's'eq : A's.reverse = A's' at *
    match A's' with
    | [] =>
      have : [] = [:0].map fun i => (fun _ => default (α := «Type»)) i := by
        rw [Range.map_same_eq_nil]
      rw [List.reverse_nil, this]
      exact .inl <| .list nofun
    | A'' :: A's' =>
      rw [List.reverse_cons, List.length_append, List.length_singleton] at A'ki
      have := progress (A := .list A's'.reverse) <| by
        rw [← Range.map_get!_eq (as := A's'.reverse)]
        apply Kinding.list
        intro i mem
        have :  A's'.reverse.get! i = (A's'.reverse ++ [A'']).get! i := by
          simp [List.getElem?_append_left mem.upper]
        rw [this]
        exact A'ki i ⟨Nat.zero_le _, Nat.lt_succ_of_lt mem.upper, Nat.mod_one _⟩
      match this with
      | .inl h =>
        generalize A's''eq : A's'.reverse = A's'' at h
        let .list A's'v := h
        let lengths_eq : List.length (List.reverse _) = _ := by rw [A's''eq]
        rw [List.length_reverse, List.length_map, Range.length_toList, Nat.sub_zero] at lengths_eq
        cases lengths_eq
        let A''ki := A'ki A's'.reverse.length ⟨Nat.zero_le _, Nat.le.refl, Nat.mod_one _⟩
        simp at A''ki
        match progress A''ki with
        | .inl A'v =>
          left
          rw [List.reverse_cons, ← Range.map_get!_eq (as := _ ++ _)]
          apply Type.IsValue.list
          intro i mem
          simp
          rw [List.getElem?_append]
          split
          · case isTrue h =>
            rw [List.length_reverse] at h
            convert A's'v i ⟨Nat.zero_le _, h, Nat.mod_one _⟩
            rw [A's''eq]
            rw [List.getElem?_eq_getElem <| by rw [List.length_map, Range.length_toList]; exact h]
            simp
            rw [Range.getElem_toList h, Nat.zero_add]
          · case isFalse h =>
            rw [List.length_append, List.length_singleton] at mem
            cases Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp h) mem.upper
            rw [Nat.sub_self, List.getElem?_cons_zero, Option.getD]
            exact A'v
        | .inr ⟨A''', A''st⟩ =>
          right
          refine ⟨.list (A's'.reverse ++ [A''']), ?_⟩
          rw [List.reverse_cons]
          apply list' _ A''st
          intro _ mem
          rw [A's''eq] at mem
          rcases Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
          exact A's'v _ mem'
      | .inr ⟨A's'', A's'st⟩ =>
        right
        generalize A's'''eq : A's'.reverse = A's''' at A's'st
        cases A's'st
        case list m A₀ _ A₁' n A₂ A₀v A₁st =>
        refine ⟨[[{</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] />, A''}]], ?_⟩
        rw [List.reverse_cons, A's'''eq, List.append_assoc, List.cons_append]
        apply list' _ A₁st
        intro A₀ mem
        rcases Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
        exact A₀v _ mem'
  | .listApp A' B', .listApp A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => by
        by_cases ∃ K', A' = [[λ a : K'. a$0]]
        · case pos h =>
          rcases h with ⟨_, rfl⟩
          let .lam .. := A'ki
          exact .inr ⟨_, .listAppId B'ki B'v⟩
        · case neg ne =>
          apply not_exists.mp at ne
          cases B'ki with
          | var => exact .inl <| .listAppVar ne A'v
          | app => exact .inl <| .listAppApp ne A'v B'v
          | scheme => exact .inl <| .listAppForall ne A'v B'v
          | list => exact .inr ⟨_, .listAppList ne A'ki A'v B'v.list_inversion⟩
          | listApp B''ki => exact .inr ⟨_, .listAppComp ne B''ki A'v B'v⟩
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .listAppr A'v B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .listAppl A'st⟩
  | .prod A', .prod A'ki => match progress A'ki with
    | .inl A'v => .inl <| .prod A'v
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .prod A'stB'⟩
  | .sum A', .sum A'ki => match progress A'ki with
    | .inl A'v => .inl <| .sum A'v
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .sum A'stB'⟩
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  all_goals (
    let eq : List.reverse (List.reverse _) = _ := by rw [A's'eq]
    rw [List.reverse_reverse] at eq
    rw [eq, List.reverse_cons]
  )
  · apply Nat.lt_of_add_lt_add_right (n := 1)
    rw [List.sizeOf_append]
    simp_arith
  · apply Nat.le_of_add_le_add_right (b := 1)
    rw [List.sizeOf_append]
    simp_arith

theorem preservation : [[Δ ⊢ A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ B : K]]
  | .eta I _ Bav, .lam I' Baki => by
    let ⟨a, anin⟩ := B.freeTypeVars ++ I ++ I' |>.exists_fresh
    let ⟨aninBI, aninI'⟩ := List.not_mem_append'.mp anin
    let ⟨aninB, aninI⟩ := List.not_mem_append'.mp aninBI
    specialize Bav a aninI
    let .app Blc _ := Bav.TypeVarLocallyClosed_of
    specialize Baki a aninI'
    simp [Type.TypeVar_open, Blc.TypeVar_open_id] at Baki
    let .app Bki (.var .head) := Baki
    exact Bki.TypeVar_drop_of_not_mem_freeTypeVars aninB (Δ' := .empty)
  | .lamApp _ _ A'v B'v (A := A'), .app (.lam I A'ki) B'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    A'ki a aninI |>.Type_open_preservation aninA' B'ki
  | .listAppList _ _ A'v B'v, .listApp A'ki B'ki =>
    let B'ki' := B'ki.inv_list
    .list (.app A'ki <| B'ki' · ·)
  | .listAppId _ A'v, .listApp (.lam I aki) A'ki => by
    let ⟨a, anin⟩ := I.exists_fresh
    specialize aki a anin
    rw [Type.TypeVar_open, if_pos rfl] at aki
    let .var .head := aki
    exact A'ki
  | .listAppComp _ A₁ki A₀v A₁B'v, .listApp A₀ki (.listApp A₁ki' Bki) => by
    cases A₁ki.arr_deterministic A₁ki'
    refine .listApp (.lam Δ.typeVarDom (fun a anin => ?_)) Bki
    rw [Type.TypeVar_open, A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id, Type.TypeVar_open,
        A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id, Type.TypeVar_open, if_pos rfl]
    apply Kinding.app (A₀ki.weakening_r _ (Δ' := .typeExt .empty ..)) _
    · rw [Environment.typeVarDom, Environment.typeVarDom]
      intro a mem
      let .head _ := mem
      exact anin
    · apply Kinding.app (A₁ki'.weakening_r _ (Δ' := .typeExt .empty ..)) <| .var .head
      rw [Environment.typeVarDom, Environment.typeVarDom]
      intro a mem
      let .head _ := mem
      exact anin
  | .lam I A'st, .lam I' A'ki => .lam (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation (A'st a aninI) <| A'ki a aninI'
  | .appl A'st, .app A'ki B'ki => .app (A'st.preservation A'ki) B'ki
  | .appr _ B'st, .app A'ki B'ki => .app A'ki <| B'st.preservation B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.preservation A'ki) B'ki
  | .arrr _ B'st, .arr A'ki B'ki => .arr A'ki <| B'st.preservation B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation (A'st a aninI) <| A'ki a aninI'
  | .list A₀v A₁st (m := m) (n := n), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rcases Aki.inv_list' with ⟨_, rfl, Aki'⟩
    apply Kinding.list
    intro i mem
    rw [List.length_append, Range.map, List.length_map, Range.length_toList, List.length_cons,
        Range.map, List.length_map, Range.length_toList, Nat.sub_zero, Nat.sub_zero] at mem
    simp
    rw [List.getElem?_append]
    split
    · case isTrue h =>
      simp [List.getElem?_eq_getElem h]
      rw [List.length_map, Range.length_toList, Nat.sub_zero] at h
      rw [Range.getElem_toList h, Nat.zero_add]
      simp [Range.length_toList] at Aki'
      specialize Aki' i mem
      rw [List.getElem?_append_left
            (by rw [List.length_map, Range.length_toList]; exact h)] at Aki'
      simp at Aki'
      rw [List.getElem?_eq_getElem (by rw [Range.length_toList]; exact h)] at Aki'
      simp [Range.getElem_toList h (l := 0), Nat.zero_add] at Aki'
      exact Aki'
    · case isFalse h =>
      simp [Range.length_toList]
      rw [List.getElem?_cons]
      split
      · case isTrue h' =>
        simp
        apply A₁st.preservation
        specialize Aki' m ⟨Nat.zero_le _, (by simp_arith [Range.length_toList]), Nat.mod_one _⟩
        simp at Aki'
        rw [List.getElem?_append_right
              (by rw [List.length_map, Range.length_toList]; exact Nat.le.refl)] at Aki'
        simp [Range.length_toList] at Aki'
        exact Aki'
      · case isFalse h' =>
        simp_arith
        let mle : m ≤ i := by
          apply Nat.not_lt.mp at h
          rw [List.length_map, Range.length_toList] at h
          exact h
        let ltn : i - m - 1 < n := by
          apply Nat.sub_lt_left_of_lt_add <| by
            apply Nat.le_sub_of_add_le
            rw [Nat.add_comm]
            apply Nat.succ_le_of_lt
            apply Nat.lt_of_le_of_ne mle
            intro meq
            rw [meq] at h'
            nomatch h' <| Nat.sub_self i
          apply Nat.sub_lt_left_of_lt_add mle
          rw [Nat.add_comm 1]
          exact mem.upper
        rw [List.getElem?_eq_getElem (by simp_arith [Range.length_toList]; exact ltn),
            Range.getElem_toList ltn]
        simp
        simp [Range.length_toList] at Aki'
        specialize Aki' i mem
        rw [List.getElem?_append_right
              (by simp_arith [List.length_map, Range.length_toList]; exact mle)] at Aki'
        simp at Aki'
        rw [List.getElem?_cons, if_neg (by rw [Range.length_toList]; exact h'), Range.length_toList,
            List.getElem?_eq_getElem (by simp_arith [Range.length_toList]; exact ltn)] at Aki'
        simp at Aki'
        rw [Range.getElem_toList ltn, Nat.zero_add] at Aki'
        exact Aki'
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.preservation A'ki) B'ki
  | .listAppr _ B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.preservation B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.preservation A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.preservation A'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

-- FALSE: Will have to change Kinding to satisfy this by requiring annotations on empty lists like
-- in the source. As far as I can tell, this is necessary for `preservation_rev`.
theorem _root_.TabularTypeInterpreter.«F⊗⊕ω».Kinding.deterministic
  : [[Δ ⊢ A : K₁]] → [[Δ ⊢ A : K₂]] → K₁ = K₂ := sorry

theorem preservation_rev : [[Δ ⊢ A -> B]] → [[Δ ⊢ B : K]] → [[Δ ⊢ A : K]]
  | .eta I Bki Bav, Bki' => by
    cases Bki.deterministic Bki'
    apply Kinding.lam Δ.typeVarDom
    intro a anin
    rw [Type.TypeVar_open, Type.TypeVar_open, if_pos rfl,
        Bki.TypeVarLocallyClosed_of.TypeVar_open_id]
    apply Kinding.app _ (.var .head)
    apply Bki'.weakening_r _ (Δ' := .typeExt .empty ..)
    intro _ mem
    rw [Environment.typeVarDom, Environment.typeVarDom] at mem
    let .head _ := mem
    exact anin
  | .lamApp (.lam I A'ki) B'ki _ _ (A := A'), Bki => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    cases A'ki a aninI |>.Type_open_preservation aninA' B'ki |>.deterministic Bki
    exact .app (.lam I A'ki) B'ki
  | .listAppList _ A'ki _ _ (K₂ := K₂) (n := n), ki => by
    rcases ki.inv_list' with ⟨_, rfl, ki'⟩
    match n with
    | 0 =>
      rw [Range.map_same_eq_nil]
      rw [Range.map_same_eq_nil] at ki
      convert Kinding.listApp A'ki .empty_list
      injection ki.deterministic <| .empty_list (K := K₂)
    | _ + 1 =>
      let .app A'ki' _ := ki' 0 ⟨Nat.zero_le _, Nat.add_one_pos _, Nat.mod_one _⟩
      cases A'ki.deterministic A'ki'
      apply Kinding.listApp A'ki
      apply Kinding.list
      intro i mem
      specialize ki' i mem
      let .app A'ki'' B'ki := ki'
      cases A'ki.deterministic A'ki''
      exact B'ki
  | .listAppId Bki _, Bki' => by
    cases Bki.deterministic Bki'
    exact .listApp .id Bki'
  | .listAppComp _ A₁ki A₀v A₁B'v (A₀ := A₀) (A₁ := A₁), .listApp (.lam I A₀A₁ki) B'ki => by
    let ⟨a, anin⟩ := A₀.freeTypeVars ++ A₁.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA₀A₁, aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninA₀, aninA₁⟩ := List.not_mem_append'.mp aninA₀A₁
    specialize A₀A₁ki a aninI
    simp [Type.TypeVar_open] at A₀A₁ki
    let .app A₀ki (.app A₁ki' (.var .head)) := A₀A₁ki
    rw [A₀v.TypeVarLocallyClosed_of.TypeVar_open_id] at A₀ki
    rw [A₁B'v.listAppl_inversion.TypeVarLocallyClosed_of.TypeVar_open_id] at A₁ki'
    apply (Kinding.TypeVar_drop_of_not_mem_freeTypeVars · aninA₁ (Δ' := .empty)) at A₁ki'
    cases A₁ki.deterministic A₁ki'
    exact A₀ki.TypeVar_drop_of_not_mem_freeTypeVars aninA₀ (Δ' := .empty) |>.listApp <|
      .listApp A₁ki B'ki
  | .lam I A'st, .lam I' A'ki => .lam (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation_rev (A'st a aninI) <| A'ki a aninI'
  | .appl A'st, .app A'ki B'ki => .app (A'st.preservation_rev A'ki) B'ki
  | .appr _ B'st, .app A'ki B'ki => .app A'ki <| B'st.preservation_rev B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.preservation_rev A'ki) B'ki
  | .arrr _ B'st, .arr A'ki B'ki => .arr A'ki <| B'st.preservation_rev B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation_rev (A'st a aninI) <| A'ki a aninI'
  | .list _ A₁st (m := m) (n := n), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rcases Aki.inv_list' with ⟨_, rfl, Aki'⟩
    apply Kinding.list
    intro i mem
    rw [List.length_append, Range.map, List.length_map, Range.length_toList, List.length_cons,
        Range.map, List.length_map, Range.length_toList, Nat.sub_zero, Nat.sub_zero] at mem
    simp
    rw [List.getElem?_append]
    split
    · case isTrue h =>
      simp [List.getElem?_eq_getElem h]
      rw [List.length_map, Range.length_toList, Nat.sub_zero] at h
      rw [Range.getElem_toList h, Nat.zero_add]
      simp [Range.length_toList] at Aki'
      specialize Aki' i mem
      rw [List.getElem?_append_left
            (by rw [List.length_map, Range.length_toList]; exact h)] at Aki'
      simp at Aki'
      rw [List.getElem?_eq_getElem (by rw [Range.length_toList]; exact h)] at Aki'
      simp [Range.getElem_toList h (l := 0), Nat.zero_add] at Aki'
      exact Aki'
    · case isFalse h =>
      simp [Range.length_toList]
      rw [List.getElem?_cons]
      split
      · case isTrue h' =>
        simp
        apply A₁st.preservation_rev
        specialize Aki' m ⟨Nat.zero_le _, (by simp_arith [Range.length_toList]), Nat.mod_one _⟩
        simp at Aki'
        rw [List.getElem?_append_right
              (by rw [List.length_map, Range.length_toList]; exact Nat.le.refl)] at Aki'
        simp [Range.length_toList] at Aki'
        exact Aki'
      · case isFalse h' =>
        simp_arith
        let mle : m ≤ i := by
          apply Nat.not_lt.mp at h
          rw [List.length_map, Range.length_toList] at h
          exact h
        let ltn : i - m - 1 < n := by
          apply Nat.sub_lt_left_of_lt_add <| by
            apply Nat.le_sub_of_add_le
            rw [Nat.add_comm]
            apply Nat.succ_le_of_lt
            apply Nat.lt_of_le_of_ne mle
            intro meq
            rw [meq] at h'
            nomatch h' <| Nat.sub_self i
          apply Nat.sub_lt_left_of_lt_add mle
          rw [Nat.add_comm 1]
          exact mem.upper
        rw [List.getElem?_eq_getElem (by simp_arith [Range.length_toList]; exact ltn),
            Range.getElem_toList ltn]
        simp
        simp [Range.length_toList] at Aki'
        specialize Aki' i mem
        rw [List.getElem?_append_right
              (by simp_arith [List.length_map, Range.length_toList]; exact mle)] at Aki'
        simp at Aki'
        rw [List.getElem?_cons, if_neg (by rw [Range.length_toList]; exact h'), Range.length_toList,
            List.getElem?_eq_getElem (by simp_arith [Range.length_toList]; exact ltn)] at Aki'
        simp at Aki'
        rw [Range.getElem_toList ltn, Nat.zero_add] at Aki'
        exact Aki'
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.preservation_rev A'ki) B'ki
  | .listAppr _ B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.preservation_rev B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.preservation_rev A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.preservation_rev A'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem Equivalence_of : [[Δ ⊢ A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ A ≡ B]]
  | .eta _ A'ki _, _ => .eta A'ki.TypeVarLocallyClosed_of
  | .lamApp .., .app (.lam I _) B'ki => .lamApp B'ki
  | .listAppList .., .listApp A'ki _ => .listAppList A'ki.TypeVarLocallyClosed_of
  | .listAppId _ _, .listApp (.lam I aki) A'ki => .listAppId A'ki
  | .listAppComp _ A₁ki .., .listApp A₀ki (.listApp _ B'ki) =>
    .listAppComp A₀ki.TypeVarLocallyClosed_of A₁ki
  | .lam I A'st, .lam I' A'ki => by
    refine .lam (I ++ I') ?_
    intro a anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
    exact A'st a aninI |>.Equivalence_of <| A'ki a aninI'
  | .appl A'st, .app A'ki B'ki => .app (A'st.Equivalence_of A'ki) .refl
  | .appr _ B'st, .app A'ki B'ki => .app .refl (B'st.Equivalence_of B'ki)
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.Equivalence_of A'ki) .refl
  | .arrr _ B'st, .arr A'ki B'ki => .arr .refl (B'st.Equivalence_of B'ki)
  | .forall I A'st, .scheme I' A'ki => by
    refine .scheme (I ++ I') ?_
    intro a anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp anin
    exact A'st a aninI |>.Equivalence_of <| A'ki a aninI'
  | .list _ A'st (m := m) (n := n), ki => by
    rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at ki ⊢
    rcases ki.inv_list' with ⟨_, rfl, A'ki⟩
    rw [List.length_append, Range.map.eq_def (r := [:m]), List.length_map, Range.length_toList,
        List.length_cons, Range.map.eq_def (r := [:n]), List.length_map, Range.length_toList,
        Nat.sub_zero, Nat.sub_zero, List.length_append, List.length_map, Range.length_toList,
        List.length_cons, List.length_map, Range.length_toList, Nat.sub_zero, Nat.sub_zero,
        ← Range.map, ← Range.map]
    apply TypeEquivalence.list
    intro i mem
    simp
    rw [List.getElem?_append]
    split
    · case isTrue h =>
      rw [List.getElem?_append_left h, List.getElem?_eq_getElem h]
      simp
      rw [List.length_map, Range.length_toList] at h
      rw [Range.getElem_toList h, Nat.zero_add]
      exact .refl
    · case isFalse h =>
      rw [List.getElem?_append_right (Nat.le_of_not_lt h)]
      rw [List.getElem?_cons]
      split
      · case isTrue h' =>
        simp
        rw [List.length_map] at h'
        rw [h', List.getElem?_cons_zero, Option.getD]
        apply A'st.Equivalence_of
        rw [List.length_append, List.length_map, Range.length_toList, List.length_cons,
            List.length_map, Range.length_toList] at A'ki
        specialize A'ki i mem
        simp at A'ki
        rw [List.getElem?_append_right (Nat.le_of_not_lt h), List.length_map, h',
            List.getElem?_cons_zero, Option.getD] at A'ki
        exact A'ki
      · case isFalse h' =>
        rw [List.getElem?_cons, if_neg h']
        exact .refl
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.Equivalence_of A'ki) .refl
  | .listAppr _ B'st, .listApp A'ki B'ki => .listApp .refl (B'st.Equivalence_of B'ki)
  | .prod A'st, .prod A'ki => .prod <| A'st.Equivalence_of A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.Equivalence_of A'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

-- Inversion

-- the conclusion should be the reflexive closure of st but we can use this weaker version.
theorem inv_arr (ArBst: [[ Δ ⊢ (A → B) -> T ]]): ∃ A' B', T = [[ (A' → B') ]] ∧ [[ Δ ⊢ A ->* A' ]] ∧ [[ Δ ⊢ B ->* B' ]] := by
  cases ArBst <;> aesop (add unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_forall (Ast: [[ Δ ⊢ (∀ a? : K. A) -> T ]]): ∃ A', T = [[∀ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a ->* A'^a ]] := by
  cases Ast ; aesop (add unsafe tactic guessI, unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_prod (Ast: [[ Δ ⊢ ⊗A -> T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ->* A' ]] := by
  cases Ast ; aesop (add unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_sum (Ast: [[ Δ ⊢ ⊕A -> T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ->* A' ]] := by
  cases Ast ; aesop (add unsafe constructors [MultiSmallStep, SmallStep])

private
theorem sandwich {f : Nat → α} (h : i < n) : [0:n].map (fun j => f j) =
  [:i].map (fun j => f j) ++
    f i :: [(i + 1) - (i + 1):n - (i + 1)].map (fun j => f (j + (i + 1))) := by
  rw [← List.singleton_append, Range.map_shift (Nat.le_refl _)]
  have : [f i] = List.map (fun j => f j) [i:i + 1] := by
    rw [Range.toList, if_pos (Nat.lt_succ_self _), Range.toList,
        if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map, List.map]
  rw [this]
  rw [Range.map_append (Nat.le_succ _) (Nat.succ_le_of_lt h),
      Range.map_append (Nat.zero_le _) (Nat.le_of_lt h)]

private
theorem sandwich' {α: Type} {nl nr : ℕ} {F1 F3: ℕ → α} {F2: α}:
  let G i := if i < nl then F1 i else if i = nl then F2 else F3 (i - nl - 1)
  [0:nl].map (λi => F1 i) ++ F2 :: [0:nr].map (λi => F3 i) = [0:nl + 1 + nr].map G := by
  intro G
  rw [sandwich (n := nl + 1 + nr) (i := nl) (by omega)]
  simp_all
  refine List.append_eq_append ?_ ?_
  . exact Std.Range.map_eq_of_eq_of_mem (λ i iltnl => by simp_all [Membership.mem])
  . refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
    refine Std.Range.map_eq_of_eq_of_mem (λ i iltnl => ?_)
    repeat' rw [if_neg (by omega)]
    exact congrArg _ (by omega)

macro "rwomega" equality:term : tactic => `(tactic | (have _eq : $equality := (by omega); rw [_eq]; try clear _eq))

theorem inv_list (Ast: [[ Δ ⊢ { </ A@i // i in [:n] /> } -> T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ Δ ⊢ A@i ->* B@i // i in [:n] /> ]] := by
  generalize T_eq : [[{ </ A@i // i in [:n] /> } ]] = T_ at Ast
  cases Ast <;> try cases T_eq
  . case list n₀ A₀i A₁ A₁' n₂ A₂i A₀V A₁st =>
    injection T_eq with eq
    have nlen: n = n₀ + 1 + n₂ := by
      apply congrArg List.length at eq
      rw [List.length_append, List.length_cons] at eq
      repeat' rw [List.length_map] at eq
      repeat' rw [Std.Range.length_toList] at eq
      omega
    refine ⟨(fun i => if i < n₀ then A₀i i else if i = n₀ then A₁' else A₂i (i - n₀ - 1)), ?_, λ i iltn => ?_⟩
    . simp; rw [nlen, ← sandwich']
    . have n₀ltn: n₀ < n := by omega
      rw [sandwich n₀ltn] at eq
      have ⟨A₀eq, A₁A₂eq⟩ := eq |> List.append_inj <| (by repeat1' rw [List.length_map])
      have A₀eq := Std.Range.eq_of_mem_of_map_eq A₀eq
      injection A₁A₂eq with A₁eq A₂eq
      have h: n - (n₀ + 1) = n₂ := by omega
      simp at A₂eq; rw [h] at A₂eq
      have A₂eq := Std.Range.eq_of_mem_of_map_eq A₂eq
      simp
      repeat' split
      . case _ iltn₀ =>
        rw [A₀eq i (by simp_all [Membership.mem])]
      . case _ _ ieqn₀ =>
        subst ieqn₀
        rw [A₁eq]
        exact .step A₁st .refl
      . case _ Niltn₀ Nieqn₀ =>
        specialize A₂eq (i - n₀ - 1) (by simp_all [Membership.mem] ; omega)
        rw [← A₂eq]
        rwomega i - n₀ - 1 + (n₀ + 1) = i

end SmallStep

namespace MultiSmallStep

theorem trans (A₀mst : [[Δ ⊢ A₀ ->* A₁]]) (A₁mst : [[Δ ⊢ A₁ ->* A₂]]) : [[Δ ⊢ A₀ ->* A₂]] := by
  induction A₀mst with
  | refl => exact A₁mst
  | step A₀st _ ih => exact step A₀st <| ih A₁mst

theorem est_of (st : [[Δ ⊢ A ->* B]]) : [[Δ ⊢ A <->* B]] := by
  induction st with
  | refl => exact .refl
  | step Ast _ ih => exact EqSmallStep.step Ast |>.trans ih

theorem preserve_lc (st : [[Δ ⊢ A ->* B]]) (Alc : A.TypeVarLocallyClosed) : B.TypeVarLocallyClosed := by
  induction st with
  | refl => exact Alc
  | step st _ ih => exact ih <| st.preserve_lc Alc

open «Type» in
theorem TypeVar_subst_var (Ast : [[Δ, a : K ⊢ A ->* B]]) (a'ninΔ : [[a' ∉ dom(Δ)]])
  : [[Δ, a' : K ⊢ A[a' / a] ->* B[a' / a] ]] := by
  induction Ast with
  | refl => rfl
  | step st _ ih => exact step (st.TypeVar_subst_var (Δ' := .empty) a'ninΔ) ih

theorem TypeVar_open_swap (Amst : [[Δ, a' : K ⊢ A^a' ->* A']]) (Alc : A.TypeVarLocallyClosed 1)
  (a'ninA : a' ∉ A.freeTypeVars) (aninΔ : [[a ∉ dom(Δ)]]) : [[Δ, a : K ⊢ A^a ->* (\a'^A')^a]] := by
  have : A.TypeVar_open a = (A.TypeVar_open a').TypeVar_subst a' (.var a) := by
    rw [Type.Type_open_var, Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars a'ninA, Type.TypeVar_subst, if_pos rfl]
  rw [this]
  let Aoplc := Alc.Type_open_dec .var_free (B := .var a')
  rw [← Type.Type_open_var] at Aoplc
  have : (A'.TypeVar_close a').TypeVar_open a = A'.TypeVar_subst a' (.var a) := by
    rw [Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst <|
          Amst.preserve_lc Aoplc]
  rw [this]
  exact Amst.TypeVar_subst_var aninΔ

theorem weakening (mst : [[Δ, Δ'' ⊢ A ->* B]]) (ΔΔ'Δ''wf : [[⊢ Δ, Δ', Δ'']])
  : [[Δ, Δ', Δ'' ⊢ A ->* B]] := by
  generalize Δ'''eq : [[Δ, Δ'']] = Δ''' at mst
  induction mst with
  | refl =>
    cases Δ'''eq
    rfl
  | step st _ ih =>
    cases Δ'''eq
    exact step (st.weakening ΔΔ'Δ''wf) ih

theorem Environment_TypeVar_subst_swap (mst : [[Δ, Δ'[B / a] ⊢ A ->* A']])
  : [[Δ, Δ'[B' / a] ⊢ A ->* A']] := by
  generalize Δ''eq : [[Δ, Δ'[B / a] ]] = Δ'' at mst
  induction mst with
  | refl =>
    cases Δ''eq
    rfl
  | step st _ ih =>
    cases Δ''eq
    exact step st.Environment_TypeVar_subst_swap ih

theorem preservation (Amst : [[Δ ⊢ A ->* B]]) (Aki : [[Δ ⊢ A : K]]) : [[Δ ⊢ B : K]] := by
  induction Amst with
  | refl => exact Aki
  | step Ast _ ih => exact ih <| Ast.preservation Aki

theorem EqSmallStep_of (Amst : [[Δ ⊢ A ->* B]]) : [[Δ ⊢ A <->* B]] := by
  induction Amst with
  | refl => rfl
  | step Ast _ ih => exact .trans (.step Ast) ih

theorem IndexedSmallStep_of (mst : [[Δ ⊢ A ->* B]]) : ∃ n, [[Δ ⊢ A ->n* B]] := by
  induction mst with
  | refl => exact ⟨_, .refl⟩
  | step st _ ih =>
    let ⟨_, ist⟩ := ih
    exact ⟨_, .step st ist⟩

theorem Equivalence_of (Amst : [[Δ ⊢ A ->* B]]) (Aki : [[Δ ⊢ A : K]]) : [[Δ ⊢ A ≡ B]] := by
  induction Amst with
  | refl => exact .refl
  | step Ast _ ih => exact .trans (Ast.Equivalence_of Aki) <| ih <| Ast.preservation Aki

theorem normalization (Aki : [[Δ ⊢ A : K]]) : ∃ B, B.IsValue ∧ [[Δ ⊢ A ->* B]] := sorry

theorem confluence (mst₀ : [[Δ ⊢ A ->* B₀]]) (mst₁ : [[Δ ⊢ A ->* B₁]])
  : ∃ C, [[Δ ⊢ B₀ ->* C]] ∧ [[Δ ⊢ B₁ ->* C]] := by
  induction mst₀ generalizing B₁ with
  | refl => exact ⟨_, mst₁, refl⟩
  | step st mst₀' ih => cases mst₁ with
    | refl => exact ⟨_, refl, step st mst₀'⟩
    | step st' mst₁' =>
      cases st.deterministic st'
      apply ih mst₁'

-- Shape Preservation
theorem preserve_shape_arr (ArBmst: [[ Δ ⊢ (A → B) ->* T ]]): ∃ A' B', T = [[ (A' → B') ]] ∧ [[ Δ ⊢ A ->* A' ]] ∧ [[ Δ ⊢ B ->* B' ]] := by
  generalize ArBeq : [[ A → B ]] = ArB at ArBmst
  induction ArBmst generalizing A B
  . case refl ArB =>
    exact ⟨A, B, ArBeq.symm, .refl, .refl⟩
  . case step ArB A0rB0 ArB' ArBst Tmst ih =>
    subst ArBeq
    have ⟨A0, B0, A0rB0eq, Amst, Bmst⟩ := ArBst.inv_arr
    specialize ih A0rB0eq.symm
    aesop (add unsafe apply MultiSmallStep.trans)

theorem preserve_shape_forall (Amst: [[ Δ ⊢ (∀ a? : K. A) ->* T ]]): ∃ A', T = [[∀ a? : K. A']] ∧ (∃I, ∀a ∉ (I: List _), [[ Δ, a : K ⊢ A^a ->* A'^a ]]) :=
by
  generalize LamAeq : [[(∀ a : K. A)]] = LamA at Amst
  induction Amst generalizing A
  . case refl => aesop (add unsafe tactic guessI, unsafe constructors [MultiSmallStep, SmallStep])
  . case step T1 T2 T3 red mred ih =>
    subst LamAeq
    have ⟨A', eqT2, I, AA'⟩ := red.inv_forall
    have ⟨A'', ih⟩ := ih eqT2.symm
    exists A''
    aesop (add unsafe tactic guessI, unsafe apply MultiSmallStep.trans)

theorem preserve_shape_prod (Amst: [[ Δ ⊢ ⊗A ->* T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ->* A' ]] :=
by
  generalize ProdAeq : [[(⊗A)]] = ProdA at Amst
  induction Amst generalizing A
  . case refl => aesop (add unsafe constructors [MultiSmallStep, SmallStep])
  . case step T1 T2 T3 red mred ih =>
    subst ProdAeq
    have := red.inv_prod
    aesop (add unsafe apply MultiSmallStep.trans)

theorem preserve_shape_sum (Amst: [[ Δ ⊢ ⊕A ->* T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ->* A' ]] :=
by
  generalize SumAeq : [[(⊕A)]] = SumA at Amst
  induction Amst generalizing A
  . case refl => aesop (add unsafe constructors [MultiSmallStep, SmallStep])
  . case step T1 T2 T3 red mred ih =>
    subst SumAeq
    have := red.inv_sum
    aesop (add unsafe apply MultiSmallStep.trans)

theorem preserve_shape_list (Amst: [[ Δ ⊢ { </ A@i // i in [:n] /> } ->* T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ Δ ⊢ A@i ->* B@i // i in [:n] /> ]] := by
  generalize ListAeq : [[{ </ A@i // i in [:n] /> }]] = ListA at Amst
  induction Amst generalizing A
  . case refl => aesop (add unsafe constructors [MultiSmallStep, SmallStep])
  . case step T1 T2 T3 red mred ih =>
    subst ListAeq
    have ⟨B, eqT2, AB⟩ := red.inv_list
    have ⟨B', ih⟩ := ih eqT2.symm
    exists B'
    aesop (add unsafe apply MultiSmallStep.trans)

end MultiSmallStep

namespace EqSmallStep

theorem preserve_lc (est : [[Δ ⊢ A <->* B]]) : A.TypeVarLocallyClosed ↔ B.TypeVarLocallyClosed := by
  induction est with
  | refl => rfl
  | step st => exact ⟨st.preserve_lc, st.preserve_lc_rev⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₀ ih₁ => exact ⟨(ih₁.mp <| ih₀.mp ·), (ih₀.mpr <| ih₁.mpr ·)⟩

theorem Environment_TypeVar_subst_swap (est : [[Δ, Δ'[B / a] ⊢ A <->* A']])
  : [[Δ, Δ'[B' / a] ⊢ A <->* A']] := by
  generalize Δ''eq : [[Δ, Δ'[B / a] ]] = Δ'' at est
  induction est with
  | refl =>
    cases Δ''eq
    rfl
  | step st =>
    cases Δ''eq
    exact step st.Environment_TypeVar_subst_swap
  | symm _ ih =>
    cases Δ''eq
    exact symm ih
  | trans _ _ ih₀ ih₁ =>
    cases Δ''eq
    exact trans ih₀ ih₁

instance : Trans (EqSmallStep Δ) (EqSmallStep Δ) (EqSmallStep Δ) where
  trans := trans

instance : Coe (MultiSmallStep Δ A B) (EqSmallStep Δ A B) where
  coe := MultiSmallStep.EqSmallStep_of

theorem lam (I : List TypeVarId) (Aest : ∀ a ∉ I, [[Δ, a : K ⊢ A^a <->* A'^a]])
  (Alc : A.TypeVarLocallyClosed 1) : [[Δ ⊢ λ a : K. A <->* λ a : K. A']] := by
  let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
  let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
  let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
  clear anin aninAA'
  specialize Aest a aninI
  generalize A''eq : A.TypeVar_open a = A'', A'''eq : A'.TypeVar_open a = A''' at Aest
  induction Aest generalizing A A' with
  | refl =>
    cases A''eq
    cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA A'''eq
    rfl
  | step st =>
    cases A''eq
    cases A'''eq
    apply step <| .lam Δ.typeVarDom _
    intro a' a'nin
    have : A.TypeVar_open a' = (A.TypeVar_open a).TypeVar_subst a (.var a') := by
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free, Type.TypeVar_subst,
          if_pos rfl, Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA]
    rw [this]
    have : A'.TypeVar_open a' = (A'.TypeVar_open a).TypeVar_subst a (.var a') := by
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free, Type.TypeVar_subst,
          if_pos rfl, Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA']
    rw [this]
    exact SmallStep.TypeVar_subst_var st a'nin (Δ' := .empty)
  | symm est ih =>
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A'oplc := est.symm.preserve_lc.mp Aoplc
    rw [← A'''eq] at A'oplc
    let A'lc := A'oplc.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact symm <| ih A'lc aninA' aninA A'''eq A''eq
  | trans est₀ est₁ ih₀ ih₁ =>
    rename_i _ A'''' _
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A''''lc := est₀.preserve_lc.mp Aoplc
    exact trans
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close A''eq
        A''''lc.TypeVar_open_TypeVar_close_id)
      (ih₁ A''''lc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        A''''lc.TypeVar_open_TypeVar_close_id A'''eq)

theorem app (Aki : [[Δ ⊢ A : K]]) (Aest : [[Δ ⊢ A <->* A']]) (Best : [[Δ ⊢ B <->* B']])
  : [[Δ ⊢ A B <->* A' B']] := by
  let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization Aki
  clear Aki
  calc
    [[Δ ⊢ A B <->* A'' B]] := by
      clear Aest A''v
      induction A''mst with
      | refl => rfl
      | step st _ ih =>
        exact trans (step (.appl st)) ih
    [[Δ ⊢ A'' B <->* A'' B']] := by
      induction Best with
      | refl => rfl
      | step st => exact step <| .appr A''v st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁
    [[Δ ⊢ A'' B' <->* A B']] := by
      symm
      clear Aest A''v
      induction A''mst with
      | refl => rfl
      | step st _ ih =>
        exact trans (step (.appl st)) ih
    [[Δ ⊢ A B' <->* A' B']] := by
      clear A''mst
      induction Aest with
      | refl => rfl
      | step st => exact step <| .appl st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem eta (Aki : [[Δ ⊢ A : K₁ ↦ K₂]]) (Δwf : [[⊢ Δ]]) : [[Δ ⊢ λ a : K₁. A a$0 <->* A]] := by
  let ⟨(a : TypeVarId), anin⟩ := A.freeTypeVars ++ Δ.typeVarDom |>.exists_fresh
  let ⟨aninA, aninΔ⟩ := List.not_mem_append'.mp anin
  clear anin
  let Aki' := Aki.weakening_r (fun | _, .head _ => aninΔ) (Δ' := .typeExt .empty a K₁)
  let ⟨A', A'v, A'mst⟩ := MultiSmallStep.normalization (A := [[A a]]) <| .app Aki' <| .var .head
  generalize A''eq : [[A a]] = A'' at A'mst
  induction A'mst generalizing A with
  | refl =>
    cases A''eq
    apply step <| .eta [] Aki ..
    intro a' _
    apply Type.IsValue.TypeVar_subst_var (a := a) (a' := a') at A'v
    rw [Type.TypeVar_subst, Type.TypeVar_subst, if_pos rfl,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA] at A'v
    exact A'v
  | step st _ ih =>
    match st with
    | .lamApp Aki'' _ A'v _ (A := A') =>
      cases A''eq
      cases Aki
      case lam I _ A'ki =>
      let ⟨a, anin⟩ := I.exists_fresh
      let A'lc := A'ki a anin |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop
        Nat.one_pos
      apply lam Δ.typeVarDom _ <| .app (.lam A'lc.weaken) (.var_bound Nat.one_pos)
      intro a' a'nin
      simp [Type.TypeVar_open, A'lc.TypeVar_open_id]
      rw [Type.Type_open_var]
      apply step <| .lamApp (K₂ := K₂) (.lam I _) (.var .head) A'v .var
      intro a'' a''nin
      exact A'ki a'' a''nin |>.weakening_r' (fun | _, .head _ => a'nin) (Δ' := .typeExt .empty ..)
        (Δ'' := .typeExt .empty ..)
    | .appl st' (A' := A') =>
      cases A''eq
      apply SmallStep.TypeVar_drop_of_not_mem_freeTypeVars aninA (Δ' := .empty) at st'
      calc
        [[Δ ⊢ λ a : K₁. A a$0 <->* λ a : K₁. A' a$0]] := by
          let Alc := Aki.TypeVarLocallyClosed_of
          apply lam Δ.typeVarDom _ <| .app (Alc.weaken (n := 1)) <| .var_bound Nat.one_pos
          intro a' a'nin
          simp [Type.TypeVar_open]
          let Alc := Aki.TypeVarLocallyClosed_of
          rw [Alc.TypeVar_open_id, st'.preserve_lc Alc |>.TypeVar_open_id]
          exact step <| st'.appl.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) <|
            Δwf.typeVarExt a'nin
        [[Δ ⊢ λ a : K₁. A' a$0 <->* A']] := ih (st'.preservation Aki)
          (st'.preserve_not_mem_freeTypeVars aninA) A'v rfl
        [[Δ ⊢ A' <->* A]] := symm <| step st'

theorem «forall» (I : List TypeVarId) (Aest : ∀ a ∉ I, [[Δ, a : K ⊢ A^a <->* A'^a]])
  (Alc : A.TypeVarLocallyClosed 1) : [[Δ ⊢ ∀ a : K. A <->* ∀ a : K. A']] := by
  let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
  let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
  let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
  clear anin aninAA'
  specialize Aest a aninI
  generalize A''eq : A.TypeVar_open a = A'', A'''eq : A'.TypeVar_open a = A''' at Aest
  induction Aest generalizing A A' with
  | refl =>
    cases A''eq
    cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA A'''eq
    rfl
  | step st =>
    cases A''eq
    cases A'''eq
    apply step <| .forall Δ.typeVarDom _
    intro a' a'nin
    have : A.TypeVar_open a' = (A.TypeVar_open a).TypeVar_subst a (.var a') := by
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free, Type.TypeVar_subst,
          if_pos rfl, Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA]
    rw [this]
    have : A'.TypeVar_open a' = (A'.TypeVar_open a).TypeVar_subst a (.var a') := by
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free, Type.TypeVar_subst,
          if_pos rfl, Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA']
    rw [this]
    exact SmallStep.TypeVar_subst_var st a'nin (Δ' := .empty)
  | symm est ih =>
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A'oplc := est.symm.preserve_lc.mp Aoplc
    rw [← A'''eq] at A'oplc
    let A'lc := A'oplc.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact symm <| ih A'lc aninA' aninA A'''eq A''eq
  | trans est₀ est₁ ih₀ ih₁ =>
    rename_i _ A'''' _
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A''''lc := est₀.preserve_lc.mp Aoplc
    exact trans
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close A''eq
        A''''lc.TypeVar_open_TypeVar_close_id)
      (ih₁ A''''lc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        A''''lc.TypeVar_open_TypeVar_close_id A'''eq)

theorem arr (Aki : [[Δ ⊢ A : K]]) (Aest : [[Δ ⊢ A <->* A']]) (Best : [[Δ ⊢ B <->* B']])
  : [[Δ ⊢ A → B <->* A' → B']] := by
  let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization Aki
  clear Aki
  calc
    [[Δ ⊢ A → B <->* A'' → B]] := by
      clear Aest A''v
      induction A''mst with
      | refl => rfl
      | step st _ ih =>
        exact trans (step (.arrl st)) ih
    [[Δ ⊢ A'' → B <->* A'' → B']] := by
      induction Best with
      | refl => rfl
      | step st => exact step <| .arrr A''v st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁
    [[Δ ⊢ A'' → B' <->* A → B']] := by
      symm
      clear Aest A''v
      induction A''mst with
      | refl => rfl
      | step st _ ih =>
        exact trans (step (.arrl st)) ih
    [[Δ ⊢ A → B' <->* A' → B']] := by
      clear A''mst
      induction Aest with
      | refl => rfl
      | step st => exact step <| .arrl st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem list (Aki : ∀ i ∈ [:n], [[Δ ⊢ A@i : K]]) (Aest : ∀ i ∈ [:n], [[Δ ⊢ A@i <->* A'@i]])
  : [[Δ ⊢ {</ A@i // i in [:n] />} <->* {</ A'@i // i in [:n] />}]] := by
  let ⟨A'', A''vA''mst⟩ := Range.skolem (MultiSmallStep.normalization <| Aki · ·)
  calc
    [[Δ ⊢ {</ A@i // i in [:n] />} <->* {</ A''@i // i in [:n] />}]] := by
      symm
      rw [Range.map, ← Range.map_append (Nat.zero_le _) Nat.le.refl,
          ← Range.map, ← Range.map]
      rw (occs := .pos [2]) [Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = A i
        nomatch Nat.not_lt_of_le mem.lower mem.upper
      )]
      generalize meq : n = m
      rw (occs := .pos [3, 4]) [← meq]
      let mlen := Nat.le_refl n
      rw (occs := .pos [1]) [meq] at mlen
      clear meq
      symm
      induction m with
      | zero => rw [Range.map_same_eq_nil, List.nil_append]
      | succ m' ih =>
        apply trans <| ih <| Nat.le_of_succ_le mlen
        rw [Range.map_eq_cons_of_lt <| Nat.lt_of_succ_le mlen,
            Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one,
            List.append_assoc, List.singleton_append,
            ← Range.map_shift (m := m' + 1) (j := m' + 1) Nat.le.refl,
            Nat.sub_self]
        let A''mst := A''vA''mst m' ⟨Nat.zero_le _, Nat.lt_of_succ_le mlen, Nat.mod_one _⟩ |>.right
        generalize A'''eq : A m' = A''', A''''eq : A'' m' = A''''
        rw [A'''eq, A''''eq] at A''mst
        clear A'''eq A''''eq
        induction A''mst with
        | refl => rfl
        | step st _ ih =>
          apply trans _ ih
          exact step <| .list (A''vA''mst · ⟨
              Nat.zero_le _,
              Nat.lt_of_lt_of_le ·.upper (Nat.le_of_succ_le mlen),
              Nat.mod_one _
            ⟩ |>.left) st
    [[Δ ⊢ {</ A''@i // i in [:n] />} <->* {</ A'@i // i in [:n] />}]] := by
      symm
      rw [Range.map, ← Range.map_append (Nat.zero_le _) (Nat.zero_le _),
          ← Range.map, ← Range.map]
      rw [Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = A'' i
        nomatch Nat.not_lt_of_le mem.lower mem.upper
      )]
      generalize meq : n = m
      rw (occs := .pos [2, 3]) [← Nat.sub_self m]
      rw (occs := .pos [1, 3, 5, 6]) [← meq]
      let mlen := Nat.le_refl n
      rw (occs := .pos [1]) [meq] at mlen
      clear meq
      induction m with
      | zero => rw [Nat.sub_zero, Range.map_same_eq_nil, List.append_nil]
      | succ m' ih =>
        apply trans _ <| ih <| Nat.le_of_succ_le mlen
        rw [Range.map_eq_cons_of_lt <| Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos _) mlen)
              (Nat.succ_pos _), Nat.sub_add_eq,
            Nat.sub_add_cancel <| Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact mlen),
            Range.map_eq_snoc_of_lt <| Nat.zero_lt_sub_of_lt <| Nat.lt_of_succ_le mlen,
            List.append_assoc, List.singleton_append,
            ← Range.map_shift (m := n - m') (j := n - m') Nat.le.refl, Nat.sub_self]
        specialize Aest (n - m' - 1) ⟨
          Nat.zero_le _,
          Nat.sub_lt_right_of_lt_add (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact mlen))
            (Nat.sub_lt_right_of_lt_add (Nat.le_of_succ_le mlen) (Nat.lt_add_right _ Nat.le.refl)),
          Nat.mod_one _
        ⟩
        let A''mst := A''vA''mst (n - m' - 1) ⟨
          Nat.zero_le _,
          Nat.sub_lt_right_of_lt_add (Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact mlen))
            (Nat.sub_lt_right_of_lt_add (Nat.le_of_succ_le mlen) (Nat.lt_add_right _ Nat.le.refl)),
          Nat.mod_one _
        ⟩ |>.right
        let A'A''est := Aest.symm.trans A''mst.EqSmallStep_of
        generalize A'''eq : A (n - m' - 1) = A''', A''''eq : A' (n - m' - 1) = A'''',
          A'''''eq : A'' (n - m' - 1) = A'''''
        rw [A''''eq, A'''''eq] at A'A''est
        clear A'''eq A''''eq A'''''eq
        induction A'A''est with
        | refl => rfl
        | step st =>
          apply step <| .list _ st
          intro i mem
          apply A''vA''mst .. |>.left
          exact ⟨
            Nat.zero_le _,
            Nat.lt_of_le_of_lt (by rw [Nat.add_assoc]; exact Nat.le_add_right ..)
              (Nat.add_lt_of_lt_sub (Nat.add_lt_of_lt_sub mem.upper)),
              Nat.mod_one _
          ⟩
        | symm _ ih => exact symm ih
        | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem listApp (Aki : [[Δ ⊢ A : K]]) (Aest : [[Δ ⊢ A <->* A']]) (Best : [[Δ ⊢ B <->* B']])
  : [[Δ ⊢ A ⟦B⟧ <->* A' ⟦B'⟧]] := by
  let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization Aki
  clear Aki
  calc
    [[Δ ⊢ A ⟦B⟧ <->* A'' ⟦B⟧]] := by
      clear Aest A''v
      induction A''mst with
      | refl => rfl
      | step st _ ih =>
        exact trans (step (.listAppl st)) ih
    [[Δ ⊢ A'' ⟦B⟧ <->* A'' ⟦B'⟧]] := by
      induction Best with
      | refl => rfl
      | step st => exact step <| .listAppr A''v st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁
    [[Δ ⊢ A'' ⟦B'⟧ <->* A ⟦B'⟧]] := by
      symm
      clear Aest A''v
      induction A''mst with
      | refl => rfl
      | step st _ ih =>
        exact trans (step (.listAppl st)) ih
    [[Δ ⊢ A ⟦B'⟧ <->* A' ⟦B'⟧]] := by
      clear A''mst
      induction Aest with
      | refl => rfl
      | step st => exact step <| .listAppl st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem listAppList (Aki : [[Δ ⊢ A : K₁ ↦ K₂]]) (Bki : ∀ i ∈ [:n], [[Δ ⊢ B@i : K₁]])
  : [[Δ ⊢ A ⟦{</ B@i // i in [:n] />}⟧ <->* {</ A B@i // i in [:n] />}]] := by
  let ⟨A', A'v, A'mst⟩ := MultiSmallStep.normalization Aki
  let ⟨B', B'vB'mst⟩ := Range.skolem (MultiSmallStep.normalization <| Bki · ·)
  by_cases ∃ K'', A' = [[λ a : K''. a$0]]
  · case pos h =>
    rcases h with ⟨K'', rfl⟩
    let .lam I aki := A'mst.preservation Aki
    let ⟨a, anin⟩ := I.exists_fresh
    specialize aki a anin
    rw [Type.TypeVar_open] at aki
    let .var .head := aki
    let B'ki i mem := B'vB'mst i mem |>.right.preservation <| Bki i mem
    calc
      [[Δ ⊢ A ⟦{</ B@i // i in [:n] />}⟧ <->* (λ a : K''. a$0) ⟦{</ B'@i // i in [:n] />}⟧]] :=
        listApp Aki A'mst <| list Bki (B'vB'mst · · |>.right)
      [[Δ ⊢ (λ a : K''. a$0) ⟦{</ B'@i // i in [:n] />}⟧ <->* {</ B'@i // i in [:n] />}]] :=
        step <| .listAppId (.list B'ki) <| .list (B'vB'mst · · |>.left)
      [[Δ ⊢ {</ B'@i // i in [:n] />} <->* {</ (λ a : K''. a$0) B'@i // i in [:n] />}]] := by
        apply list (fun i mem => B'vB'mst i mem |>.right.preservation <| Bki i mem)
        intro i mem
        have : B' i = Type.Type_open (.var (.bound 0)) (B' i) := by
          rw [Type.Type_open, if_pos rfl]
        rw (occs := .pos [1]) [this]
        exact symm <| step <| .lamApp .id (B'ki i mem) .id <| B'vB'mst i mem |>.left
      [[Δ ⊢ {</ (λ a : K''. a$0) B'@i // i in [:n] />} <->* {</ A B@i // i in [:n] />}]] :=
        symm <| list (.app Aki <| Bki · ·) (app Aki A'mst <| B'vB'mst · · |>.right)
  · case neg ne =>
    calc
      [[Δ ⊢ A ⟦{</ B@i // i in [:n] />}⟧ <->* A' ⟦{</ B'@i // i in [:n] />}⟧]] :=
        listApp Aki A'mst <| list Bki (B'vB'mst · · |>.right)
      [[Δ ⊢ A' ⟦{</ B'@i // i in [:n] />}⟧ <->* {</ A' B'@i // i in [:n] />}]] :=
        step <| .listAppList (not_exists.mp ne) (A'mst.preservation Aki) A'v (B'vB'mst · · |>.left)
      [[Δ ⊢ {</ A' B'@i // i in [:n] />} <->* {</ A B@i // i in [:n] />}]] :=
        symm <| list (.app Aki <| Bki · ·) (app Aki A'mst <| B'vB'mst · · |>.right)

theorem listAppId (Aki : [[Δ ⊢ A : L K]]) : [[Δ ⊢ (λ a : K. a$0) ⟦A⟧ <->* A]] := by
  let ⟨A', A'v, A'mst⟩ := MultiSmallStep.normalization Aki
  calc
    [[Δ ⊢ (λ a : K. a$0) ⟦A⟧ <->* (λ a : K. a$0) ⟦A'⟧]] :=
      listApp .id refl A'mst (Δ := Δ)
    [[Δ ⊢ (λ a : K. a$0) ⟦A'⟧ <->* A']] := step <| .listAppId (A'mst.preservation Aki) A'v
    [[Δ ⊢ A' <->* A]] := symm A'mst

theorem prod (est : [[Δ ⊢ A <->* B]]) : [[Δ ⊢ ⊗ A <->* ⊗ B]] := by
  induction est with
  | refl => rfl
  | step st => exact step st.prod
  | symm _ ih => exact symm ih
  | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem sum (est : [[Δ ⊢ A <->* B]]) : [[Δ ⊢ ⊕ A <->* ⊕ B]] := by
  induction est with
  | refl => rfl
  | step st => exact step st.sum
  | symm _ ih => exact symm ih
  | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

end EqSmallStep

open «Type» in
theorem SmallStep.Type_open_out (Bst : [[Δ ⊢ B -> B']])
  (Aki : Kinding [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) K') (Δwf : [[⊢ Δ, a : K, Δ']])
  (aninA : a ∉ A.freeTypeVars) (Bki : [[Δ ⊢ B : K]])
  : EqSmallStep [[Δ, Δ'[B / a] ]] (A.Type_open B n) (A.Type_open B' n) := by
  match A with
  | .var _ =>
    rw [Type_open]
    split
    · case isTrue h =>
      cases h
      rw [Type_open, if_pos rfl]
      exact .step <| Bst.weakening (Δwf.subst Bki) (Δ'' := .empty)
    · case isFalse h =>
      rw [Type_open, if_neg h]
  | .lam _ A' =>
    simp [freeTypeVars] at aninA
    rw [TypeVar_open] at Aki
    let .lam I A'ki (K₁ := K₁) := Aki
    rw [Type_open, Type_open]
    let ⟨a', a'nin⟩ := a :: (A'.TypeVar_open a (n + 1)).freeTypeVars ++
      (A'.Type_open B (n + 1)).freeTypeVars ++ I ++ [[Δ, a : K, Δ']].typeVarDom |>.exists_fresh
    let ⟨a'ninaA'A'BI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ninaA'A'B, a'ninI⟩ := List.not_mem_append'.mp a'ninaA'A'BI
    let ⟨a'ninaA', a'ninA'B⟩ := List.not_mem_append'.mp a'ninaA'A'B
    let ⟨ane, a'ninA'⟩ := List.not_mem_cons.mp a'ninaA'
    let A'ki' := A'ki a' a'ninI
    let Δa'wf := Δwf.typeVarExt a'ninΔ (K := K₁)
    rw [TypeVar_open_comm _ (Nat.add_one_ne_zero _)] at A'ki'
    rw [← Environment.append] at A'ki' Δa'wf
    let A'lc := A'ki'.Type_open_preservation'' Δa'wf
      (not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm) Bki
      |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a')
    rw [Type_open_TypeVar_open_comm Bki.TypeVarLocallyClosed_of (Nat.zero_ne_add_one _),
        TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA'B] at A'lc
    apply EqSmallStep.lam (a :: I ++ [[Δ, a : K, Δ']].typeVarDom) _ A'lc
    intro a'' a''nin
    let ⟨a''ninaI, a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← Type_open_TypeVar_open_comm Bki.TypeVarLocallyClosed_of (Nat.zero_ne_add_one _),
        ← Type_open_TypeVar_open_comm (Bst.preserve_lc Bki.TypeVarLocallyClosed_of)
          (Nat.zero_ne_add_one _)]
    specialize A'ki a'' a''ninI
    rw [Type_open_var, Type_open_TypeVar_open_comm .var_free (Nat.add_one_ne_zero _),
        ← Type_open_var, ← Environment.append] at A'ki
    exact Bst.Type_open_out A'ki (Δwf.typeVarExt a''ninΔ)
      (not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm) Bki
  | app .. =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    rw [TypeVar_open] at Aki
    let .app A'ki B'ki := Aki
    rw [Type_open, Type_open]
    exact Bst.Type_open_out A'ki Δwf aninA' Bki |>.app
      (A'ki.Type_open_preservation'' Δwf aninA' Bki) <|
      Bst.Type_open_out B'ki Δwf aninB' Bki
  | .forall _ A' =>
    simp [freeTypeVars] at aninA
    rw [TypeVar_open] at Aki
    let .scheme I A'ki (K₁ := K₁) := Aki
    rw [Type_open, Type_open]
    let ⟨a', a'nin⟩ := a :: (A'.TypeVar_open a (n + 1)).freeTypeVars ++
      (A'.Type_open B (n + 1)).freeTypeVars ++ I ++ [[Δ, a : K, Δ']].typeVarDom |>.exists_fresh
    let ⟨a'ninaA'A'BI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ninaA'A'B, a'ninI⟩ := List.not_mem_append'.mp a'ninaA'A'BI
    let ⟨a'ninaA', a'ninA'B⟩ := List.not_mem_append'.mp a'ninaA'A'B
    let ⟨ane, a'ninA'⟩ := List.not_mem_cons.mp a'ninaA'
    let A'ki' := A'ki a' a'ninI
    let Δa'wf := Δwf.typeVarExt a'ninΔ (K := K₁)
    rw [TypeVar_open_comm _ (Nat.add_one_ne_zero _)] at A'ki'
    rw [← Environment.append] at A'ki' Δa'wf
    let A'lc := A'ki'.Type_open_preservation'' Δa'wf
      (not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm) Bki
      |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a')
    rw [Type_open_TypeVar_open_comm Bki.TypeVarLocallyClosed_of (Nat.zero_ne_add_one _),
        TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA'B] at A'lc
    apply EqSmallStep.forall (a :: I ++ [[Δ, a : K, Δ']].typeVarDom) _ A'lc
    intro a'' a''nin
    let ⟨a''ninaI, a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← Type_open_TypeVar_open_comm Bki.TypeVarLocallyClosed_of (Nat.zero_ne_add_one _),
        ← Type_open_TypeVar_open_comm (Bst.preserve_lc Bki.TypeVarLocallyClosed_of)
          (Nat.zero_ne_add_one _)]
    specialize A'ki a'' a''ninI
    rw [Type_open_var, Type_open_TypeVar_open_comm .var_free (Nat.add_one_ne_zero _),
        ← Type_open_var, ← Environment.append] at A'ki
    exact Bst.Type_open_out A'ki (Δwf.typeVarExt a''ninΔ)
      (not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm) Bki
  | arr .. =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    rw [TypeVar_open] at Aki
    let .arr A'ki B'ki := Aki
    rw [Type_open, Type_open]
    exact Bst.Type_open_out A'ki Δwf aninA' Bki |>.arr
      (A'ki.Type_open_preservation'' Δwf aninA' Bki) <|
      Bst.Type_open_out B'ki Δwf aninB' Bki
  | .list A's =>
    rw [← Range.map_get!_eq (as := A's)] at Aki aninA ⊢
    simp [TypeVar_open, Type_open, freeTypeVars] at Aki aninA ⊢
    rcases Aki.inv_list' with ⟨_, rfl, A'ki⟩
    rw [← Range.map, ← Range.map]
    apply EqSmallStep.list
    · intro i mem
      specialize A'ki i mem
      specialize aninA i <| Range.mem_toList_of_mem mem
      simp [List.getElem?_eq_getElem mem.upper] at A'ki aninA ⊢
      exact A'ki.Type_open_preservation'' Δwf aninA Bki
    · intro i mem
      specialize A'ki i mem
      specialize aninA i <| Range.mem_toList_of_mem mem
      simp [List.getElem?_eq_getElem mem.upper] at A'ki aninA ⊢
      exact Type_open_out Bst A'ki Δwf aninA Bki
  | listApp .. =>
    simp [freeTypeVars] at aninA
    let ⟨aninA', aninB'⟩ := aninA
    rw [TypeVar_open] at Aki
    let .listApp A'ki B'ki := Aki
    rw [Type_open, Type_open]
    exact Bst.Type_open_out A'ki Δwf aninA' Bki |>.listApp
      (A'ki.Type_open_preservation'' Δwf aninA' Bki) <|
      Bst.Type_open_out B'ki Δwf aninB' Bki
  | .prod A'st =>
    rw [freeTypeVars] at aninA
    rw [TypeVar_open] at Aki
    let .prod A'ki := Aki
    rw [Type_open, Type_open]
    exact Bst.Type_open_out A'ki Δwf aninA Bki |>.prod
  | .sum .. =>
    rw [freeTypeVars] at aninA
    rw [TypeVar_open] at Aki
    let .sum A'ki := Aki
    rw [Type_open, Type_open]
    exact Bst.Type_open_out A'ki Δwf aninA Bki |>.sum
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| List.getElem_mem mem.upper

theorem MultiSmallStep.Type_open_out (Bst : [[Δ ⊢ B ->* B']])
  (Aki : Kinding [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) K') (ΔaΔ'wf : [[⊢ Δ, a : K, Δ']])
  (aninA : a ∉ A.freeTypeVars) (Bki : [[Δ ⊢ B : K]])
  : EqSmallStep [[Δ, Δ'[B / a] ]] (A.Type_open B n) (A.Type_open B' n) := by
  induction Bst with
  | refl => rfl
  | step st _ ih =>
    let .typeVarExt Δwf _ := ΔaΔ'wf.weakening
    exact .trans (st.Type_open_out Aki ΔaΔ'wf aninA Bki)
      (.Environment_TypeVar_subst_swap <| ih <| st.preservation Bki)

set_option maxHeartbeats 4000000 in
mutual

theorem SmallStep.TypeVar_subst_in (Ast : [[Δ, a : K, Δ' ⊢ A -> A']])
  (Aki : [[Δ, a : K, Δ' ⊢ A : K']]) (Δwf : [[⊢ Δ, a : K, Δ']]) (Bki : [[Δ ⊢ B : K]])
  : [[Δ, Δ'[B / a] ⊢ A[B / a] <->* A'[B / a] ]] := by
  open «Type» in
  match A, Ast, Aki with
  | .lam K'' (.app A'' _), .eta I A''ki _, .lam .. =>
    simp [Type.TypeVar_subst]
    exact .eta (A''ki.subst' Δwf Bki) (Δwf.subst Bki)
  | .app (.lam K'' A'') B', .lamApp .., .app (.lam I A''ki) B'ki =>
    rw [TypeVar_subst, TypeVar_subst, Bki.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist]
    apply EqSmallStep.lamApp (a :: I ++ [[Δ, a : K, Δ']].typeVarDom) _ (B'ki.subst' Δwf Bki)
      (Δwf.subst Bki) (K₂ := K')
    intro a' a'nin
    let ⟨a'ninaI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ne, a'ninI⟩ := List.not_mem_cons.mp a'ninaI
    specialize A''ki a' a'ninI
    rw [← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm a'ne.symm]
    let Δa'wf := Δwf.typeVarExt a'ninΔ (K := K'')
    rw [← Environment.append] at A''ki Δa'wf ⊢
    rw [← Environment.TypeVar_subst]
    exact A''ki.subst' Δa'wf Bki
  | _, .listAppList ne A''ki A''v B'v, Aki =>
    rename «Type» => A''
    rename Nat → «Type» => B'
    let .listApp A''ki' B'ki := Aki
    cases A''ki.deterministic A''ki'
    let B'ki' := B'ki.inv_list
    simp [TypeVar_subst]
    rw [← Range.map, ← Range.map, Range.map, Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = [[(A''[B / a] B'@i[B / a])]]
      simp [TypeVar_subst]
    ), Range.map]
    apply EqSmallStep.listAppList (A''ki.subst' Δwf Bki)
    intro i mem
    specialize B'ki' i mem
    simp at B'ki' ⊢
    exact B'ki'.subst' Δwf Bki
  | .listApp _ A'', .listAppId A''ki A''v, .listApp _ A''ki' =>
    cases A''ki.deterministic A''ki'
    simp [TypeVar_subst]
    exact .listAppId <| A''ki'.subst' Δwf Bki
  | _, .listAppComp ne A₁ki A''v B'v, .listApp A₀ki (.listApp A₁ki' B'ki) =>
    cases A₁ki.deterministic A₁ki'
    simp [TypeVar_subst]
    let A₁ki'' := A₁ki.subst' Δwf Bki
    let B'ki' := B'ki.subst' Δwf Bki
    let ⟨_, A₁B''v, A₁B''mst⟩ := MultiSmallStep.normalization <| .listApp A₁ki'' B'ki'
    let ⟨_, A₁B''ist⟩ := A₁B''mst.IndexedSmallStep_of
    exact .listAppComp' (A₀ki.subst' Δwf Bki) A₁ki'' B'ki' A₁B''ist A₁B''v (Δwf.subst Bki)
  | .lam K'' A'', .lam I A''st, .lam I' A''ki =>
    rw [TypeVar_subst, TypeVar_subst]
    let ⟨a', a'nin⟩ := a :: [[(A'' [B / a])]].freeTypeVars ++ I' ++ [[Δ, a : K, Δ']].typeVarDom
      |>.exists_fresh
    let ⟨a'ninaA''I', a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ninaA'', a'ninI'⟩ := List.not_mem_append'.mp a'ninaA''I'
    let ⟨ane, a'ninA''⟩ := List.not_mem_cons.mp a'ninaA''
    let A''ki' := A''ki a' a'ninI'
    rw [← Environment.append] at A''ki'
    let A''lc := A''ki'.subst' (Δwf.typeVarExt a'ninΔ) Bki
      |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a')
    rw [Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA''] at A''lc
    apply EqSmallStep.lam (a :: I ++ I' ++ [[Δ, a : K, Δ']].typeVarDom) _ A''lc
    intro a'' a''nin
    let ⟨a''ninaII', a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨a''ninaI, a''ninI'⟩ := List.not_mem_append'.mp a''ninaII'
    let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm]
    specialize A''ki a'' a''ninI'
    specialize A''st a'' a''ninI
    rw [← Environment.append] at A''ki A''st ⊢
    rw [← Environment.TypeVar_subst]
    exact A''st.TypeVar_subst_in A''ki (Δwf.typeVarExt a''ninΔ) Bki
  | .app A'' B', .appl A''st, .app A''ki B'ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .app (A''ki.subst' Δwf Bki) (A''st.TypeVar_subst_in A''ki Δwf Bki) .refl
  | .app A'' B', .appr A''v B''st, .app A''ki B'ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .app (A''ki.subst' Δwf Bki) .refl (B''st.TypeVar_subst_in B'ki Δwf Bki)
  | .forall K'' A'', .forall I A''st, .scheme I' A''ki =>
    rw [TypeVar_subst, TypeVar_subst]
    let ⟨a', a'nin⟩ := a :: [[(A'' [B / a])]].freeTypeVars ++ I' ++ [[Δ, a : K, Δ']].typeVarDom
      |>.exists_fresh
    let ⟨a'ninaA''I', a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ninaA'', a'ninI'⟩ := List.not_mem_append'.mp a'ninaA''I'
    let ⟨ane, a'ninA''⟩ := List.not_mem_cons.mp a'ninaA''
    let A''ki' := A''ki a' a'ninI'
    rw [← Environment.append] at A''ki'
    let A''lc := A''ki'.subst' (Δwf.typeVarExt a'ninΔ) Bki
      |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a')
    rw [Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA''] at A''lc
    apply EqSmallStep.forall (a :: I ++ I' ++ [[Δ, a : K, Δ']].typeVarDom) _ A''lc
    intro a'' a''nin
    let ⟨a''ninaII', a''ninΔ⟩ := List.not_mem_append'.mp a''nin
    let ⟨a''ninaI, a''ninI'⟩ := List.not_mem_append'.mp a''ninaII'
    let ⟨ane, a''ninI⟩ := List.not_mem_cons.mp a''ninaI
    rw [← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm]
    specialize A''ki a'' a''ninI'
    specialize A''st a'' a''ninI
    rw [← Environment.append] at A''ki A''st ⊢
    rw [← Environment.TypeVar_subst]
    exact A''st.TypeVar_subst_in A''ki (Δwf.typeVarExt a''ninΔ) Bki
  | .arr A'' B', .arrl A''st, .arr A''ki B'ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .arr (A''ki.subst' Δwf Bki) (A''st.TypeVar_subst_in A''ki Δwf Bki) .refl
  | .arr A'' B', .arrr A''v B''st, .arr A''ki B'ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .arr (A''ki.subst' Δwf Bki) .refl (B''st.TypeVar_subst_in B'ki Δwf Bki)
  | .list A'', Ast, Aki =>
    cases Ast
    case list _ A₁st =>
    simp [TypeVar_subst]
    rw [← Range.map, ← Range.map]
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rw (occs := .pos [3]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
    rw [List.length_append, List.length_map, Range.length_toList, Nat.sub_zero, List.length_cons,
        List.length_map, Range.length_toList, Nat.sub_zero] at Aki ⊢
    rw [List.length_append, List.length_map, Range.length_toList, Nat.sub_zero, List.length_cons,
        List.length_map, Range.length_toList, Nat.sub_zero]
    rcases Aki.inv_list' with ⟨K'', rfl, A''ki⟩
    apply EqSmallStep.list
    · intro i mem
      specialize A''ki i mem
      simp at A''ki ⊢
      rw [List.getElem?_append]
      split
      · case isTrue h =>
        simp [Range.length_toList] at h ⊢
        rw [List.getElem?_append_left (by simp_arith [Range.length_toList, h])] at A''ki
        simp at A''ki
        rw [List.getElem?_eq_getElem (by simp_arith [Range.length_toList, h]),
            Range.getElem_toList h] at A''ki ⊢
        simp at A''ki ⊢
        exact A''ki.subst' Δwf Bki
      · case isFalse h =>
        simp [Range.length_toList] at h ⊢
        rw [List.getElem?_append_right (by simp_arith [Range.length_toList, h])] at A''ki
        simp [Range.length_toList] at A''ki
        rw [List.getElem?_cons]
        split
        · case isTrue h' =>
          rw [h', List.getElem?_cons_zero] at A''ki
          rw [Option.getD] at A''ki ⊢
          exact A''ki.subst' Δwf Bki
        · case isFalse h' =>
          rw [List.getElem?_cons] at A''ki
          split at A''ki
          case isTrue h'' => nomatch h' h''
          simp at A''ki ⊢
          rw [List.getElem?_eq_getElem] at A''ki ⊢
          repeat (
            swap
            rw [Range.length_toList, Nat.sub_zero]
            apply Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h')
            apply Nat.sub_lt_left_of_lt_add h
            rw [Nat.add_comm 1]
            exact mem.upper
          )
          rw [Range.getElem_toList] at A''ki ⊢
          repeat (
            swap
            rw [Nat.sub_zero]
            apply Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h')
            apply Nat.sub_lt_left_of_lt_add h
            rw [Nat.add_comm 1]
            exact mem.upper
          )
          simp at A''ki ⊢
          exact A''ki.subst' Δwf Bki
    · intro i mem
      simp
      rw [List.getElem?_append]
      split
      · case isTrue h => rw [List.getElem?_append_left h]
      · case isFalse h =>
        rw [List.getElem?_append_right (Nat.le_of_not_lt h)]
        simp [Range.length_toList] at h ⊢
        rw [List.getElem?_cons]
        split
        · case isTrue h' =>
          rw [h', List.getElem?_cons_zero, Option.getD, Option.getD]
          apply A₁st.TypeVar_subst_in _ Δwf Bki (K' := K'')
          specialize A''ki i mem
          simp at A''ki
          rw [List.getElem?_append_right (by simp_arith [Range.length_toList, h])] at A''ki
          simp [Range.length_toList] at A''ki
          rw [h', List.getElem?_cons_zero] at A''ki
          rw [Option.getD] at A''ki
          exact A''ki
        · case isFalse h' =>
          rw [List.getElem?_cons]
          split
          case isTrue h'' => nomatch h' h''
          simp
          rw [List.getElem?_eq_getElem, Range.getElem_toList]
          rw [Nat.sub_zero]
          apply Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h')
          apply Nat.sub_lt_left_of_lt_add h
          rw [Nat.add_comm 1]
          exact mem.upper
  | .listApp A'' B', .listAppl A''st, .listApp A''ki B'ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .listApp (A''ki.subst' Δwf Bki) (A''st.TypeVar_subst_in A''ki Δwf Bki) .refl
  | .listApp A'' B', .listAppr A''v B''st, .listApp A''ki B'ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .listApp (A''ki.subst' Δwf Bki) .refl (B''st.TypeVar_subst_in B'ki Δwf Bki)
  | .prod A'', .prod A''st, .prod A''ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .prod <| A''st.TypeVar_subst_in A''ki Δwf Bki
  | .sum A'', .sum A''st, .sum A''ki =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .sum <| A''st.TypeVar_subst_in A''ki Δwf Bki
termination_by sizeOf Δ
decreasing_by all_goals sorry

theorem SmallStep.Type_open_in
  (Ast : SmallStep [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) (Type.TypeVar_open A' a n))
  (Aki : Kinding [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) K') (aninA : a ∉ A.freeTypeVars)
  (aninA' : a ∉ A'.freeTypeVars) (Δwf : [[⊢ Δ, a : K, Δ']]) (Bki : [[Δ ⊢ B : K]])
  : EqSmallStep [[Δ, Δ'[B / a] ]] (A.Type_open B n) (A'.Type_open B n) := by
  rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA,
      ← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA']
  exact Ast.TypeVar_subst_in Aki Δwf Bki
termination_by sizeOf Δ
decreasing_by all_goals sorry

theorem MultiSmallStep.Type_open_in
  (Amst : MultiSmallStep [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) (Type.TypeVar_open A' a n))
  (Aki : Kinding [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) K') (aninA : a ∉ A.freeTypeVars)
  (aninA' : a ∉ A'.freeTypeVars) (Δwf : [[⊢ Δ, a : K, Δ']]) (Bki : [[Δ ⊢ B : K]])
  : EqSmallStep [[Δ, Δ'[B / a] ]] (A.Type_open B n) (A'.Type_open B n) := by
  generalize A''eq : A.TypeVar_open a n = A'', A'''eq : A'.TypeVar_open a n = A''' at Amst
  induction Amst generalizing A A' with
  | refl =>
    cases A''eq
    cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA A'''eq
    rfl
  | step st _ ih =>
    rename_i A'''' _ _
    cases A''eq
    cases A'''eq
    let A''''lc := st.preserve_lc Aki.TypeVarLocallyClosed_of |>.weaken (n := n)
    rw [Nat.zero_add] at A''''lc
    refine .trans ?_ <| ih (A := A''''.TypeVar_close a n) (by
      rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id A''''lc]
      exact st.preservation Aki) Type.not_mem_freeTypeVars_TypeVar_close
      aninA' (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id A''''lc) rfl
    rw [← A''''lc.TypeVar_open_TypeVar_close_id (a := a) (n := n)] at st
    exact st.Type_open_in Aki aninA Type.not_mem_freeTypeVars_TypeVar_close Δwf Bki
termination_by sizeOf Δ
decreasing_by all_goals sorry

theorem MultiSmallStep.Type_open
  (Amst : MultiSmallStep [[Δ, a : K, Δ']] (A.TypeVar_open a n) (Type.TypeVar_open A' a n))
  (Bmst : [[Δ ⊢ B ->* B']]) (Aki : Kinding [[Δ, a : K, Δ']] (Type.TypeVar_open A a n) K')
  (Δwf : [[⊢ Δ, a : K, Δ']]) (aninA : a ∉ A.freeTypeVars) (aninA' : a ∉ A'.freeTypeVars)
  (Bki : [[Δ ⊢ B : K]]) : EqSmallStep [[Δ, Δ'[B / a] ]] (A.Type_open B n) (A'.Type_open B' n) := by
  refine .trans ?_ <| Bmst.Type_open_out (Amst.preservation Aki) Δwf aninA' Bki
  exact Amst.Type_open_in Aki aninA aninA' Δwf Bki
termination_by sizeOf Δ
decreasing_by all_goals sorry

theorem EqSmallStep.lamApp (I : List TypeVarId) (Aki : ∀ a ∉ I, [[Δ, a : K₁ ⊢ A^a : K₂]])
  (Bki : [[Δ ⊢ B : K₁]]) (Δwf : [[⊢ Δ]]) : [[Δ ⊢ (λ a : K₁. A) B <->* A^^B]] := by
  open EqSmallStep in
  replace Aki := fun a' (a'nin : a' ∉ I ++ Δ.typeVarDom) =>
    Aki a' <| And.left <| List.not_mem_append'.mp a'nin
  let ⟨(a : TypeVarId), anin⟩ := I ++ Δ.typeVarDom ++ A.freeTypeVars |>.exists_fresh
  let ⟨aninIΔ, aninA⟩ := List.not_mem_append'.mp anin
  let ⟨_, aninΔ⟩ := List.not_mem_append'.mp aninIΔ
  let Alc := Aki a aninIΔ |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
  rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA] at Alc
  let ⟨A', A'v, A'mst⟩ := MultiSmallStep.normalization <| Aki a aninIΔ
  let ⟨B', B'v, B'mst⟩ := MultiSmallStep.normalization Bki
  by_cases ∃ A'', A' = [[A'' a]] ∧ a ∉ A''.freeTypeVars
  · case pos h =>
    rcases h with ⟨A'', rfl, aninA''⟩
    let .app A''lc _ := A'v.TypeVarLocallyClosed_of
    let A''aki := A'mst.preservation (Aki a aninIΔ)
    calc
      [[Δ ⊢ (λ a : K₁. A) B <->* (λ a : K₁. A'' a$0) B']] := by
        apply app (.lam (I ++ Δ.typeVarDom) Aki) _ B'mst
        apply lam Δ.typeVarDom _ Alc
        intro a' a'nin
        simp [Type.TypeVar_open, A''lc.TypeVar_open_id]
        let A'mst' := A'mst.TypeVar_subst_var a'nin (a' := a')
        simp [Type.TypeVar_subst] at A'mst'
        rw [Type.Type_open_var, Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
            Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA''] at A'mst'
        simp [Type.TypeVar_subst] at A'mst'
        rw [Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA, ← Type.Type_open_var] at A'mst'
        exact A'mst'.EqSmallStep_of
      [[Δ ⊢ (λ a : K₁. A'' a$0) B' <->* A'' B']] := by
        apply app _ _ refl (K := [[K₁ ↦ K₂]])
        · apply Kinding.lam <| Δ.typeVarDom
          intro a' a'nin
          simp [Type.TypeVar_open, A''lc.TypeVar_open_id]
          apply (Kinding.weakening_r' · (fun | _, .head _ => a'nin) (Δ := [[Δ]])
            (Δ' := [[ε, a' : K₁]]) (Δ'' := [[ε, a : K₁]])) at A''aki
          apply (Kinding.substAux · nofun nofun (.var .head) (Δ' := .empty)) at A''aki
          simp [Type.TypeVar_subst, Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA''] at A''aki
          exact A''aki
        · apply step <| .eta (K₂ := K₂) [] ..
          · let .app A''ki (.var .head) := A''aki
            exact A''ki.TypeVar_drop_of_not_mem_freeTypeVars aninA'' (Δ' := .empty)
          · intro a' a'nin
            apply Type.IsValue.TypeVar_subst_var (a := a) (a' := a') at A'v
            simp [Type.TypeVar_subst, Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA''] at A'v
            exact A'v
      [[Δ ⊢ A'' B' <->* A^^B]] := by
        clear A''aki A''lc A'v anin B'v
        generalize A'''eq : A.TypeVar_open a = A''', A''''eq : [[A'' a]] = A'''' at A'mst
        induction A'mst generalizing A A'' with
        | refl =>
          cases A'''eq
          cases A
          all_goals rw [Type.TypeVar_open] at A''''eq
          case app A'''''' A''''' =>
            injection A''''eq with eq eq'
            cases eq
            cases A'''''
            all_goals rw [Type.TypeVar_open] at eq'
            case var =>
              split at eq'
              · case isTrue h =>
                cases h
                simp [Type.Type_open]
                let .app A''lc _ := Alc
                let A''lc' := A''lc.not_mem_freeTypeVars_TypeVar_open_dec aninA''
                rw [A''lc'.TypeVar_open_id, A''lc'.Type_open_id]
                specialize Aki a aninIΔ
                simp [Type.TypeVar_open, A''lc'.TypeVar_open_id] at Aki
                let .app A''ki _ := Aki
                apply app _ refl (symm B'mst)
                swap
                exact A''ki.TypeVar_drop_of_not_mem_freeTypeVars
                  (Type.not_mem_freeTypeVars_TypeVar_open_drop aninA'') (Δ' := .empty)
              · case isFalse h =>
                cases eq'
                simp [Type.freeTypeVars] at aninA
            all_goals nomatch eq'
          all_goals nomatch A''''eq
        | step st _ ih =>
          cases A''''eq
          cases A'''eq
          let Aalc := Alc.Type_open_dec .var_free (B := .var (.free a))
          rw [← Type.Type_open_var] at Aalc
          let A₁lc := st.preserve_lc Aalc
          apply EqSmallStep.trans <| ih
            (fun a' a'nin => st.TypeVar_open_swap Alc aninA (List.not_mem_append'.mp a'nin |>.right)
                |>.preservation <| Aki a' a'nin)
            Type.not_mem_freeTypeVars_TypeVar_close (A₁lc.TypeVar_close_inc (a := a)) _ aninA''
            A₁lc.TypeVar_open_TypeVar_close_id rfl
          symm
          apply SmallStep.Type_open_in _ (Aki a aninIΔ) aninA
            Type.not_mem_freeTypeVars_TypeVar_close (Δwf.typeVarExt aninΔ) Bki (Δ' := .empty)
          rw [A₁lc.TypeVar_open_TypeVar_close_id]
          exact st
  · case neg h =>
    calc
      [[Δ ⊢ (λ a : K₁. A) B <->* (λ a : K₁. \a^A') B']] := app (.lam (I ++ Δ.typeVarDom) Aki)
          (lam Δ.typeVarDom
            (fun _ a'nin => A'mst.TypeVar_open_swap Alc aninA a'nin |>.EqSmallStep_of) Alc) B'mst
      [[Δ ⊢ (λ a : K₁. \a^A') B' <->* (\a^A')^^B']] := by
        apply step <| .lamApp _ (B'mst.preservation Bki) _ B'v (K₂ := K₂)
        · apply Kinding.lam <| I ++ Δ.typeVarDom
          intro a' a'nin
          let ⟨_, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
          exact A'mst.TypeVar_open_swap Alc aninA a'ninΔ |>.preservation <| Aki a' a'nin
        · apply Type.IsValue.lam I
          · intro a' a'nin
            rw [Type.Type_open_var,
                A'v.TypeVarLocallyClosed_of.Type_open_TypeVar_close_eq_TypeVar_subst]
            exact A'v.TypeVar_subst_var
          · intro A'' eq A''lc
            apply not_exists.mp at h
            specialize h A''
            apply not_and.mp at h
            apply h
            · have : [[(A'' a)]] = [[((A'' a$0)^a)]] := by
                rw [Type.TypeVar_open, A''lc.TypeVar_open_id, Type.TypeVar_open, if_pos rfl]
              rw [this, ← eq, Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id]
              apply A'mst.preserve_lc
              rw [Type.Type_open_var]
              exact Alc.Type_open_dec .var_free
            · have : A''.freeTypeVars = [[(A'' a$0)]].freeTypeVars := by
                simp [Type.freeTypeVars]
              rw [this, ← eq]
              exact Type.not_mem_freeTypeVars_TypeVar_close
      [[Δ ⊢ (\a^A')^^B' <->* A^^B]] :=
        symm <| A'mst.TypeVar_open_swap Alc aninA aninΔ |>.Type_open B'mst (Aki a aninIΔ)
          (Δwf.typeVarExt aninΔ) (Δ' := .empty) aninA Type.not_mem_freeTypeVars_TypeVar_close Bki
termination_by sizeOf Δ
decreasing_by all_goals sorry

theorem EqSmallStep.listAppComp' (A₀ki : [[Δ ⊢ A₀ : K₂ ↦ K₃]]) (A₁ki : [[Δ ⊢ A₁ : K₁ ↦ K₂]])
  (B'ki : [[Δ ⊢ B' : L K₁]]) (A₁B''ist : [[Δ ⊢ A₁ ⟦B'⟧ ->n* A₁B'']]) (A₁B''v : [[value A₁B'']])
  (Δwf : [[⊢ Δ]]) : [[Δ ⊢ A₀ ⟦A₁ ⟦B'⟧⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B'⟧]] := by
  open EqSmallStep in
  let ⟨A₀', A₀'v, A₀'mst⟩ := MultiSmallStep.normalization A₀ki
  by_cases ∃ K', A₀' = [[λ a : K'. a$0]]
  · case pos h =>
    rcases h with ⟨_, rfl⟩
    cases A₀'mst.preservation A₀ki
    case lam I' A₀''ki =>
    let ⟨a, anin⟩ := I'.exists_fresh
    specialize A₀''ki a anin
    rw [Type.TypeVar_open, if_pos rfl] at A₀''ki
    let .var ain := A₀''ki
    cases ain
    case typeVarExt ne => nomatch ne
    let ⟨A₁', A₁'v, A₁'mst⟩ := MultiSmallStep.normalization A₁ki
    let ⟨B'', B''v, B''mst⟩ := MultiSmallStep.normalization B'ki
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    let A₁lc := A₁ki.TypeVarLocallyClosed_of
    calc
      [[Δ ⊢ A₀ ⟦A₁ ⟦B'⟧⟧ <->* (λ a : K₂. a$0) ⟦A₁ ⟦B'⟧⟧]] := listApp A₀ki A₀'mst refl
      [[Δ ⊢ (λ a : K₂. a$0) ⟦A₁ ⟦B'⟧⟧ <->* A₁ ⟦B'⟧]] := listAppId <| .listApp A₁ki B'ki
      [[Δ ⊢ A₁ ⟦B'⟧ <->* (λ a : K₁. A₁ a$0) ⟦B'⟧]] := listApp A₁ki (symm <| eta A₁ki Δwf) refl
      [[Δ ⊢ (λ a : K₁. A₁ a$0) ⟦B'⟧ <->* (λ a : K₁. (λ a : K₂. a$0) (A₁ a$0)) ⟦B'⟧]] := by
        apply listApp
        · apply Kinding.lam Δ.typeVarDom
          intro a' a'nin
          simp [Type.TypeVar_open, A₁lc.TypeVar_open_id]
          exact .app
            (A₁ki.weakening (Δwf.typeVarExt a'nin) (Δ' := .typeExt .empty ..) (Δ'' := .empty))
            (.var .head)
        · apply lam Δ.typeVarDom _ <| .app (A₁lc.weaken (n := 1)) <| .var_bound Nat.one_pos
          intro a' a'nin
          simp [Type.TypeVar_open, A₁lc.TypeVar_open_id]
          symm
          have : [[A₁ a']] = Type.Type_open (.var (.bound 0)) [[A₁ a']] := by
            rw [Type.Type_open, if_pos rfl]
          rw (occs := .pos [2]) [this]
          let Δa'wf := Δwf.typeVarExt a'nin (K := K₁)
          apply EqSmallStep.lamApp []
            (fun _ _ => by rw [Type.TypeVar_open, if_pos rfl]; exact .var .head) _ Δa'wf
          exact .app
            (A₁ki.weakening Δa'wf (Δ' := .typeExt .empty ..) (Δ'' := .empty))
            (.var .head)
        · rfl
      [[Δ ⊢ (λ a : K₁. (λ a : K₂. a$0) (A₁ a$0)) ⟦B'⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B'⟧]] := by
        symm
        apply listApp
        · apply Kinding.lam Δ.typeVarDom
          intro a' a'nin
          simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
          exact .app
            (A₀ki.weakening (Δwf.typeVarExt a'nin) (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
            .app
              (A₁ki.weakening (Δwf.typeVarExt a'nin) (Δ' := .typeExt .empty ..) (Δ'' := .empty))
              (.var .head)
        · apply lam Δ.typeVarDom _ <|
            .app (A₀lc.weaken (n := 1)) <| .app (A₁lc.weaken (n := 1)) <| .var_bound Nat.one_pos
          intro a' a'nin
          simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
          exact app
            (A₀ki.weakening (Δwf.typeVarExt a'nin) (Δ' := .typeExt .empty ..) (Δ'' := .empty))
            (A₀'mst.weakening (Δwf.typeVarExt a'nin) (Δ' := .typeExt .empty ..)
              (Δ'' := .empty)).EqSmallStep_of
            refl
        · rfl
  · case neg ne =>
    generalize A₁B'eq : [[A₁ ⟦B'⟧]] = A₁B' at A₁B''ist
    generalize meq : n = m at A₁B''ist
    let mlen : n ≤ n := Nat.le.refl
    rw (occs := .pos [1]) [meq] at mlen
    clear meq
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    induction A₁B''ist generalizing A₁ B' with
    | refl =>
      cases A₁B'eq
      let A₁lc := A₁ki.TypeVarLocallyClosed_of
      calc
        [[Δ ⊢ A₀ ⟦A₁ ⟦B'⟧⟧ <->* A₀' ⟦A₁ ⟦B'⟧⟧]] := listApp A₀ki A₀'mst refl
        [[Δ ⊢ A₀' ⟦A₁ ⟦B'⟧⟧ <->* (λ a : K₁. A₀' (A₁ a$0)) ⟦B'⟧]] :=
          step <| .listAppComp (not_exists.mp ne) A₁ki A₀'v A₁B''v
        [[Δ ⊢ (λ a : K₁. A₀' (A₁ a$0)) ⟦B'⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B'⟧]] := by
          symm
          apply listApp
          · apply Kinding.lam Δ.typeVarDom
            intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
            let Δawf := Δwf.typeVarExt anin (K := K₁)
            exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
              .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <| .var .head
          · apply lam Δ.typeVarDom _ <| .app (A₀lc.weaken (n := 1)) <|
              .app (A₁lc.weaken (n := 1)) <| .var_bound Nat.one_pos
            intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                  A₀'mst.preserve_lc A₀lc |>.TypeVar_open_id]
            let Δawf := Δwf.typeVarExt anin (K := K₁)
            exact app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty))
              (A₀'mst.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)).EqSmallStep_of
              refl
          · rfl
    | step st A₁B''ist' ih =>
      cases A₁B'eq
      match st with
      | .listAppList ne' _ A₁v B''v (B := B'') (n := n) =>
        let A₁lc := A₁ki.TypeVarLocallyClosed_of
        let B'ki' := B'ki.inv_list
        calc
          [[Δ ⊢ A₀ ⟦A₁ ⟦{</ B''@i // i in [:n] />}⟧⟧ <->* A₀ ⟦{</ A₁ B''@i // i in [:n] />}⟧]] :=
            listApp A₀ki refl <| listAppList A₁ki B'ki'
          [[Δ ⊢ A₀ ⟦{</ A₁ B''@i // i in [:n] />}⟧ <->* {</ A₀ (A₁ B''@i) // i in [:n] />}]] :=
            listAppList A₀ki (.app A₁ki <| B'ki' · ·)
          [[Δ ⊢ {</ A₀ (A₁ B''@i) // i in [:n] />} <->* {</ (λ a : K₁. A₀ (A₁ a$0)) B''@i // i in [:n] />}]] := by
            apply list (.app A₀ki <| .app A₁ki <| B'ki' · ·)
            intro i mem
            have : [[A₀ (A₁ B''@i)]] = [[((A₀ (A₁ a$0))^^B''@i)]] := by
              simp [Type.Type_open, A₀lc.Type_open_id, A₁lc.Type_open_id]
            rw [this]
            symm
            apply EqSmallStep.lamApp Δ.typeVarDom _ (B'ki' i mem) Δwf (K₂ := K₃)
            intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
            let Δawf := Δwf.typeVarExt anin (K := K₁)
            exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
              .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <| .var .head
          [[Δ ⊢ {</ (λ a : K₁. A₀ (A₁ a$0)) B''@i // i in [:n] />} <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦{</ B''@i // i in [:n] />}⟧]] := by
            symm
            apply listAppList _ B'ki' (K₂ := K₃)
            apply Kinding.lam Δ.typeVarDom
            intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
            let Δawf := Δwf.typeVarExt anin (K := K₁)
            exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
              .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <| .var .head
      | .listAppId _ _ (A := B'') (K := K') =>
        let .lam I aki := A₁ki
        let ⟨a, anin⟩ := I.exists_fresh
        specialize aki a anin
        rw [Type.TypeVar_open, if_pos rfl] at aki
        let .var .head := aki
        calc
          [[Δ ⊢ A₀ ⟦(λ a : K'. a$0) ⟦B''⟧⟧ <->* A₀ ⟦B''⟧]] := listApp A₀ki refl <| listAppId B'ki
          [[Δ ⊢ A₀ ⟦B''⟧ <->* (λ a : K'. A₀ a$0) ⟦B''⟧]] := listApp A₀ki (symm <| eta A₀ki Δwf) refl
          [[Δ ⊢ (λ a : K'. A₀ a$0) ⟦B''⟧ <->* (λ a : K'. A₀ ((λ a : K'. a$0) a$0)) ⟦B''⟧]] := by
            apply listApp
            · apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K')
              exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                .var .head
            · apply lam Δ.typeVarDom _ <| .app (A₀lc.weaken (n := 1)) <| .var_bound Nat.one_pos
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K')
              apply app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) refl
              have : Type.var (.free a) = Type.Type_open (.var (.bound 0)) (.var (.free a)) := by
                rw [Type.Type_open, if_pos rfl]
              rw (occs := .pos [1]) [this]
              symm
              apply step <| .lamApp .id (.var .head) .id .var
            · rfl
      | .listAppComp ne' B₀ki A₁v B₀B₁v (A₁ := B₀) (B := B₁) (K₁ := K₀) =>
        let .listApp B₀ki' B₁ki := B'ki
        cases B₀ki.deterministic B₀ki'
        let A₁lc := A₁v.TypeVarLocallyClosed_of
        let B₀lc := B₀ki.TypeVarLocallyClosed_of
        let A₀A₁ki : [[Δ ⊢ λ a : K₁. A₀ (A₁ a$0) : K₁ ↦ K₃]] := by
          apply Kinding.lam Δ.typeVarDom
          intro a anin
          simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
          let Δawf := Δwf.typeVarExt anin (K := K₁)
          exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
            .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <| .var .head
        let ⟨A₀A₁', A₀A₁'v, A₀A₁'mst⟩ := MultiSmallStep.normalization A₀A₁ki
        let A₀A₁'lc := A₀A₁'v.TypeVarLocallyClosed_of
        calc
          [[Δ ⊢ A₀ ⟦A₁ ⟦B₀ ⟦B₁⟧⟧⟧ <->* A₀ ⟦(λ a : K₀. A₁ (B₀ a$0)) ⟦B₁⟧⟧]] :=
            listApp A₀ki refl <| step <| .listAppComp ne' B₀ki A₁v B₀B₁v
          [[Δ ⊢ A₀ ⟦(λ a : K₀. A₁ (B₀ a$0)) ⟦B₁⟧⟧ <->* (λ a : K₀. A₀ ((λ a : K₀. A₁ (B₀ a$0)) a$0)) ⟦B₁⟧]] := by
            apply EqSmallStep.listAppComp' A₀ki _ B₁ki A₁B''ist' A₁B''v Δwf
            apply Kinding.lam Δ.typeVarDom
            intro a anin
            simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
            let Δawf := Δwf.typeVarExt anin (K := K₀)
            exact .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
              .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <| .var .head
          [[Δ ⊢ (λ a : K₀. A₀ ((λ a : K₀. A₁ (B₀ a$0)) a$0)) ⟦B₁⟧ <->* (λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]] := by
            symm
            apply listApp _ _ refl (K := [[K₀ ↦ K₃]])
            · apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                    B₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                    .var .head
            · apply lam Δ.typeVarDom _ <| .app (A₀lc.weaken (n := 1)) <|
                .app (A₁lc.weaken (n := 1)) <| .app (B₀lc.weaken (n := 1)) <| .var_bound Nat.one_pos
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                    A₁lc.weaken (n := 1).TypeVar_open_id, B₀lc.TypeVar_open_id,
                    B₀lc.weaken (n := 1).TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              apply app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) refl
              symm
              have : [[A₁ (B₀ a)]] = [[((A₁ (B₀ a$0))^^a)]] := by
                simp [Type.Type_open, A₁lc.Type_open_id, B₀lc.Type_open_id]
              rw [this]
              apply EqSmallStep.lamApp (a :: Δ.typeVarDom) _ (.var .head) Δawf (K₂ := K₂)
              intro a' a'nin
              simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
              let Δaa'wf := Δawf.typeVarExt a'nin (K := K₀)
              exact .app (A₁ki.weakening Δaa'wf (Δ' := [[ε, a : K₀, a' : K₀]]) (Δ'' := .empty)) <|
                .app (B₀ki.weakening Δaa'wf (Δ' := [[ε, a : K₀, a' : K₀]]) (Δ'' := .empty)) <|
                  .var .head
          [[Δ ⊢ (λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧ <->* (λ a : K₀. (λ a : K₁. A₀ (A₁ a$0)) (B₀ a$0)) ⟦B₁⟧]] := by
            apply listApp _ _ refl (K := [[K₀ ↦ K₃]])
            · apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                    B₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                    .var .head
            · apply lam Δ.typeVarDom _ <| .app (A₀lc.weaken (n := 1)) <|
                .app (A₁lc.weaken (n := 1)) <| .app (B₀lc.weaken (n := 1)) <| .var_bound Nat.one_pos
              intro a anin
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₀lc.weaken (n := 1).TypeVar_open_id,
                    A₁lc.TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
                    B₀lc.TypeVar_open_id]
              symm
              have : [[A₀ (A₁ (B₀ a))]] = [[((A₀ (A₁ a$0))^^(B₀ a))]] := by
                simp [Type.Type_open, A₀lc.Type_open_id, A₁lc.Type_open_id]
              rw [this]
              apply EqSmallStep.lamApp (a :: Δ.typeVarDom) _ _ Δawf (K₂ := K₃)
              · intro a' a'nin
                simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
                let Δaa'wf := Δawf.typeVarExt a'nin (K := K₁)
                exact .app (A₀ki.weakening Δaa'wf (Δ' := [[ε, a : K₀, a' : K₁]]) (Δ'' := .empty)) <|
                  .app (A₁ki.weakening Δaa'wf (Δ' := [[ε, a : K₀, a' : K₁]]) (Δ'' := .empty)) <|
                    .var .head
              · exact .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .var .head
          [[Δ ⊢ (λ a : K₀. (λ a : K₁. A₀ (A₁ a$0)) (B₀ a$0)) ⟦B₁⟧ <->* (λ a : K₀. A₀A₁' (B₀ a$0)) ⟦B₁⟧]] := by
            symm
            apply listApp (K := [[K₀ ↦ K₃]]) _ _ refl
            · apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀A₁'lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              exact .app (A₀A₁'mst.preservation A₀A₁ki |>.weakening Δawf
                  (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .var .head
            · apply lam Δ.typeVarDom _ <| .app (A₀A₁'lc.weaken (n := 1)) <|
                .app (B₀lc.weaken (n := 1)) <| .var_bound Nat.one_pos
              intro a anin
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              simp [Type.TypeVar_open, A₀lc.weaken (n := 1).TypeVar_open_id,
                    A₁lc.weaken (n := 1).TypeVar_open_id, A₀A₁'lc.TypeVar_open_id,
                    B₀lc.TypeVar_open_id]
              symm
              exact app (A₀A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty))
                (A₀A₁'mst.weakening Δawf (Δ' := .typeExt .empty ..)
                  (Δ'' := .empty)).EqSmallStep_of refl
        by_cases ∃ K', A₀A₁' = [[λ a : K'. a$0]]
        · case pos h =>
          rcases h with ⟨K₁, rfl⟩
          cases A₀A₁'mst.preservation A₀A₁ki
          calc
            [[Δ ⊢ (λ a : K₀. (λ a : K₁. a$0) (B₀ a$0)) ⟦B₁⟧ <->* (λ a : K₀. B₀ a$0) ⟦B₁⟧]] := by
              symm
              apply listApp _ _ refl (K := [[K₀ ↦ K₁]])
              · apply Kinding.lam Δ.typeVarDom
                intro a anin
                simp [Type.TypeVar_open, B₀lc.TypeVar_open_id]
                let Δawf := Δwf.typeVarExt anin (K := K₀)
                exact .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .var .head
              · apply lam Δ.typeVarDom _ <| .app (B₀lc.weaken (n := 1)) <| .var_bound Nat.one_pos
                intro a anin
                simp [Type.TypeVar_open, B₀lc.TypeVar_open_id, B₀lc.weaken (n := 1).TypeVar_open_id]
                symm
                have : [[B₀ a]] = [[((a$0)^^(B₀ a))]] := by
                  rw [Type.Type_open, if_pos rfl]
                rw (occs := .pos [2]) [this]
                let Δawf := Δwf.typeVarExt anin (K := K₀)
                apply EqSmallStep.lamApp []
                  (fun _ _ => by rw [Type.TypeVar_open, if_pos rfl]; exact .var .head) _ Δawf
                exact .app (B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .var .head
            [[Δ ⊢ (λ a : K₀. B₀ a$0) ⟦B₁⟧ <->* B₀ ⟦B₁⟧]] :=
              symm <| listApp B₀ki (symm <| eta B₀ki Δwf) refl
            [[Δ ⊢ B₀ ⟦B₁⟧ <->* (λ a : K₁. a$0) ⟦B₀ ⟦B₁⟧⟧]] := symm <| listAppId (.listApp B₀ki B₁ki)
            [[Δ ⊢ (λ a : K₁. a$0) ⟦B₀ ⟦B₁⟧⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B₀ ⟦B₁⟧⟧]] :=
              symm <| listApp A₀A₁ki A₀A₁'mst refl
        · case neg ne =>
          calc
            [[Δ ⊢ (λ a : K₀. A₀A₁' (B₀ a$0)) ⟦B₁⟧ <->* A₀A₁' ⟦B₀ ⟦B₁⟧⟧]] :=
              symm <| step <| .listAppComp (not_exists.mp ne) B₀ki A₀A₁'v B₀B₁v
            [[Δ ⊢ A₀A₁' ⟦B₀ ⟦B₁⟧⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B₀ ⟦B₁⟧⟧]] :=
              listApp (A₀A₁'mst.preservation A₀A₁ki) (symm ↑A₀A₁'mst) refl
      | .listAppl st' (A' := A₁') =>
        let A₁lc := A₁ki.TypeVarLocallyClosed_of
        calc
          [[Δ ⊢ A₀ ⟦A₁ ⟦B'⟧⟧ <->* A₀ ⟦A₁' ⟦B'⟧⟧]] :=
            listApp A₀ki refl <| listApp A₁ki (step st') refl
          [[Δ ⊢ A₀ ⟦A₁' ⟦B'⟧⟧ <->* (λ a : K₁. A₀ (A₁' a$0)) ⟦B'⟧]] :=
            ih (st'.preservation A₁ki) B'ki A₁B''v rfl <| Nat.le_of_add_right_le mlen
          [[Δ ⊢ (λ a : K₁. A₀ (A₁' a$0)) ⟦B'⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B'⟧]] := by
            symm
            apply listApp (K := [[K₁ ↦ K₃]]) (Δ := Δ) _ _ refl
            · apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₁)
              exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
                  .var .head
            · apply lam Δ.typeVarDom _ <| .app (A₀lc.weaken (n := 1)) <|
                .app (A₁lc.weaken (n := 1)) <| .var_bound Nat.one_pos
              intro a anin
              let Δawf := Δwf.typeVarExt anin (K := K₁)
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                    st'.preserve_lc A₁lc |>.TypeVar_open_id]
              apply app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) refl
              exact app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty))
                (step (st'.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty))) refl
      | .listAppr _ st' (B' := B'') =>
        calc
          [[Δ ⊢ A₀ ⟦A₁ ⟦B'⟧⟧ <->* A₀ ⟦A₁ ⟦B''⟧⟧]] :=
            listApp A₀ki refl <| listApp A₁ki refl <| step st'
          [[Δ ⊢ A₀ ⟦A₁ ⟦B''⟧⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B''⟧]] :=
            ih A₁ki (st'.preservation B'ki) A₁B''v rfl <| Nat.le_of_add_right_le mlen
          [[Δ ⊢ (λ a : K₁. A₀ (A₁ a$0)) ⟦B''⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B'⟧]] := by
            apply listApp (K := [[K₁ ↦ K₃]]) (Δ := Δ) _ refl <| symm <| step st'
            apply Kinding.lam Δ.typeVarDom
            intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id,
                  A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
            let Δawf := Δwf.typeVarExt anin (K := K₁)
            exact .app (A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
              .app (A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <| .var .head
termination_by n
decreasing_by all_goals sorry

end

namespace EqSmallStep

theorem listAppComp (A₀ki : [[Δ ⊢ A₀ : K₂ ↦ K₃]]) (A₁ki : [[Δ ⊢ A₁ : K₁ ↦ K₂]])
  (B'ki : [[Δ ⊢ B' : L K₁]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A₀ ⟦A₁ ⟦B'⟧⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B'⟧]] :=
  let ⟨_, A₁B''v, A₁B''mst⟩ := MultiSmallStep.normalization <| A₁ki.listApp B'ki
  let ⟨_, A₁B''ist⟩ := A₁B''mst.IndexedSmallStep_of
  listAppComp' A₀ki A₁ki B'ki A₁B''ist A₁B''v Δwf

theorem of_EquivalenceI (equ : [[Δ ⊢ A ≡ᵢ B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A <->* B]] := by
  induction equ generalizing K with
  | refl => rfl
  | eta A'lc =>
    rename_i A' _ _
    let .lam I A'aki := Aki
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    specialize A'aki a aninI
    simp [Type.TypeVar_open, A'lc.TypeVar_open_id] at A'aki
    let .app A'ki (.var .head) := A'aki
    exact eta (A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA' (Δ' := .empty)) Δwf
  | lamApp B'ki =>
    let .app (.lam I A'ki) B'ki' := Aki
    cases B'ki.deterministic B'ki'
    exact lamApp I A'ki B'ki Δwf
  | listAppList =>
    let .listApp A'ki B'ki := Aki
    exact listAppList A'ki B'ki.inv_list
  | listAppId A'ki =>
    rename_i Δ A' K'
    let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization A'ki
    calc
      [[Δ ⊢ (λ a : K'. a$0) ⟦A'⟧ <->* (λ a : K'. a$0) ⟦A''⟧]] :=
        listApp .id .refl A''mst
      [[Δ ⊢ (λ a : K'. a$0) ⟦A''⟧ <->* A'']] := step <| .listAppId (A''mst.preservation A'ki) A''v
      [[Δ ⊢ A'' <->* A']] := symm A''mst
  | lam I _ ih =>
    rename_i Δ _ A' _ _
    let .lam I' A'ki := Aki
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I' |>.exists_fresh
    let ⟨aninA', aninI'⟩ := List.not_mem_append'.mp anin
    let A'lc := A'ki a aninI' |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    apply lam (I ++ I' ++ Δ.typeVarDom) _ A'lc
    intro a' a'nin
    let ⟨a'ninII', a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ninI, a'ninI'⟩ := List.not_mem_append'.mp a'ninII'
    exact ih a' a'ninI (A'ki a' a'ninI') <| Δwf.typeVarExt a'ninΔ
  | app _ _ ih₀ ih₁ =>
    let .app A'ki B'ki := Aki
    exact app A'ki (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
  | scheme I _ ih =>
    rename_i Δ _ A' _ _
    let .scheme I' A'ki := Aki
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I' |>.exists_fresh
    let ⟨aninA', aninI'⟩ := List.not_mem_append'.mp anin
    let A'lc := A'ki a aninI' |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    apply «forall» (I ++ I' ++ Δ.typeVarDom) _ A'lc
    intro a' a'nin
    let ⟨a'ninII', a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨a'ninI, a'ninI'⟩ := List.not_mem_append'.mp a'ninII'
    exact ih a' a'ninI (A'ki a' a'ninI') <| Δwf.typeVarExt a'ninΔ
  | arr _ _ ih₀ ih₁ =>
    let .arr A'ki B'ki := Aki
    exact .arr A'ki (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
  | list _ ih =>
    rcases Aki.inv_list' with ⟨_, rfl, A'ki⟩
    apply list A'ki
    intro i mem
    exact ih i mem (A'ki i mem) Δwf
  | listApp _ _ ih₀ ih₁ =>
    let .listApp A'ki B'ki := Aki
    exact listApp A'ki (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
  | listAppComp _ A₁ki =>
    rename_i A₀ Δ A₁ K₁ K₂ B' _
    let .listApp A₀ki (.listApp A₁ki' B'ki) (K₂ := K₃) := Aki
    cases A₁ki.deterministic A₁ki'
    exact listAppComp A₀ki A₁ki B'ki Δwf
  | prod equ' ih =>
    let .prod A'ki := Aki
    exact ih A'ki Δwf |>.prod
  | sum equ' ih =>
    let .sum A'ki := Aki
    exact ih A'ki Δwf |>.sum

theorem _root_.TabularTypeInterpreter.«F⊗⊕ω».TypeEquivalenceS.preservation : [[Δ ⊢ A ≡ₛ B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ B : K]] := sorry

theorem of_EquivalenceS (equ : [[Δ ⊢ A ≡ₛ B]]) (Aki : [[Δ ⊢ A : K]]) (Bki : [[Δ ⊢ B : K]])
  (Δwf : [[⊢ Δ]]) : [[Δ ⊢ A <->* B]] := by
  induction equ with
  | base equ' => exact .of_EquivalenceI equ' Aki Δwf
  | symm equ' => exact .symm <| .of_EquivalenceI equ' Bki Δwf
  | trans equ' _ ih₀ ih₁ =>
    exact .trans (ih₀ Aki (equ'.preservation Aki)) (ih₁ (equ'.preservation Aki) Bki)

theorem preservation (Aest : [[Δ ⊢ A <->* B]]) : [[Δ ⊢ A : K]] ↔ [[Δ ⊢ B : K]] := by
  induction Aest with
  | refl => exact ⟨id, id⟩
  | step Ast => exact ⟨(Ast.preservation ·), (Ast.preservation_rev ·)⟩
  | symm _ ih => exact .symm ih
  | trans _ _ ih₀ ih₁ => exact ⟨(ih₁.mp <| ih₀.mp ·), (ih₀.mpr <| ih₁.mpr ·)⟩

theorem Equivalence_of (Aest : [[Δ ⊢ A <->* B]]) (Aki : [[Δ ⊢ A : K]]) : [[Δ ⊢ A ≡ B]] := by
  induction Aest with
  | refl => exact .refl
  | step A'st => exact A'st.Equivalence_of Aki
  | symm B'st ih => exact .symm <| ih <| symm B'st |>.preservation |>.mp Aki
  | trans A'st _ ih₀ ih₁ => exact .trans (ih₀ Aki) <| ih₁ <| A'st.preservation |>.mp Aki

theorem common_reduct (est : [[Δ ⊢ A <->* B]]) : ∃ C, [[Δ ⊢ A ->* C]] ∧ [[Δ ⊢ B ->* C]] := by
  induction est with
  | refl => exact ⟨_, .refl, .refl⟩
  | step st => exact ⟨_, .step st .refl, .refl⟩
  | symm est ih =>
    let ⟨C, B'mst, A'mst⟩ := ih
    exact ⟨_, A'mst, B'mst⟩
  | trans q r ih₀ ih₁ =>
    let ⟨C₀, A'mst, A''mst₀⟩ := ih₀
    let ⟨C₁, A''mst₁, A'''mst⟩ := ih₁
    let ⟨C, C₀mst, C₁mst⟩ := A''mst₀.confluence A''mst₁
    exact ⟨_, A'mst.trans C₀mst, A'''mst.trans C₁mst⟩

-- ====================


-- Injectivity of Type Constructors.
theorem inj_arr (ArBest: [[ Δ ⊢ (A → B) <->* (A' → B') ]]): [[ Δ ⊢ A <->* A' ]] ∧ [[ Δ ⊢ B <->* B' ]] := by
  have ⟨T, ArB_Tmst, A'rB'_Tmst⟩ := ArBest.common_reduct
  have ⟨A1, B1, Teq1, AA1, BB1⟩ := ArB_Tmst.preserve_shape_arr
  have ⟨A2, B2, Teq2, A'A2, B'B2⟩ := A'rB'_Tmst.preserve_shape_arr
  subst T; cases Teq2; case refl =>
  refine ⟨AA1.est_of.trans A'A2.est_of.symm, BB1.est_of.trans B'B2.est_of.symm⟩

theorem inj_forall (Aest: [[ Δ ⊢ (∀ a? : K. A) <->* (∀ a? : K'. A') ]]): K = K' ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a <->* A'^a ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct
  have ⟨A1, Teq1, I1, AA1⟩:= AT.preserve_shape_forall
  have ⟨A2, Teq2, I2, A'A2⟩ := A'T.preserve_shape_forall
  subst T; cases Teq2; case refl =>
  exact ⟨rfl, I1 ++ I2, λa nin => AA1 a (by simp_all) |>.est_of.trans <| A'A2 a (by simp_all) |>.est_of.symm⟩

theorem inj_prod (Aest: [[ Δ ⊢ ⊗A <->* ⊗A' ]]): [[ Δ ⊢ A <->* A' ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_prod
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_prod
  subst T; cases Teq2; case refl =>
  exact AA1.est_of.trans A'A2.est_of.symm

theorem inj_sum (Aest: [[ Δ ⊢ ⊕A <->* ⊕A' ]]): [[ Δ ⊢ A <->* A' ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_sum
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_sum
  subst T; cases Teq2; case refl =>
  exact AA1.est_of.trans A'A2.est_of.symm

theorem inj_list (Aest: [[ Δ ⊢ { </ A@i // i in [:n] /> } <->* { </ B@i // i in [:n'] /> } ]]): n = n' ∧ [[ </ Δ ⊢ A@i <->* B@i // i in [:n] /> ]] := by
  have ⟨T, AT, BT⟩ := Aest.common_reduct
  have ⟨A1, Teq1, AA1⟩ := AT.preserve_shape_list
  have ⟨B1, Teq2, BB1⟩ := BT.preserve_shape_list
  subst T
  injection Teq2 with eq
  have eqn'n := Std.Range.length_eq_of_mem_eq eq; subst eqn'n
  have eqBA := Std.Range.eq_of_mem_of_map_eq eq; clear eq
  simp_all
  exact λ x xin => AA1 x xin |>.est_of.trans <| BB1 x xin |>.est_of.symm

end EqSmallStep

end TabularTypeInterpreter.«F⊗⊕ω»
