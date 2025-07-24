import TabularTypeInterpreter.Data.List
import TabularTypeInterpreter.Logic.Relation
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Equivalence
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type.SmallStep
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Basic
import Thesis.Newman

namespace TabularTypeInterpreter.«F⊗⊕ω»

open Std

namespace Type.IsValue

theorem id : [[value λ a : K. a$0]] :=
  lam [] (fun _ _ => by rw [TypeVar_open, if_pos rfl]; exact var) nofun

theorem list_inversion (h : [[value {</ A@i // i in [:n] /> </ : K // b />}]])
  : ∀ i ∈ [:n], [[value A@i]] := by
  generalize Aseq : [:n].map _ = As, Option.someIf .. = K' at h
  let .list Asv := h
  let lengths_eq : ([:n].map _).length = _ := by rw [Aseq]
  rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at lengths_eq
  cases lengths_eq
  intro i mem
  rw [Range.eq_of_mem_of_map_eq Aseq i mem]
  exact Asv i mem

theorem app_inversion : [[value A B]] → [[value A]] ∧ [[value B]]
  | varApp Av => ⟨.var, Av⟩
  | appApp Av Bv => ⟨Av, Bv⟩

theorem listApp_inversion : [[value A ⟦B⟧]] → [[value A]] ∧ [[value B]]
  | listAppVar _ Av => ⟨Av, .var⟩
  | listAppApp _ Av Bv => ⟨Av, Bv⟩

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
  apply Nat.lt_add_right
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
  · case lam.eta Bki _ h => nomatch h _ rfl Bki.TypeVarLocallyClosed_of
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
  · case arr.arrr _ v' _ st' => exact not_step v' st'
  · case list n _ _ _ v' =>
    generalize Aseq : [:n].map _ = As, Option.someIf .. = K' at st
    let .list A₁st (m := m) := st
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
  · case varApp.appr v' _ st' => exact not_step v' st'
  · case appApp.appl v' _ _ st' => exact not_step v' st'
  · case appApp.appr v' _ st' => exact not_step v' st'
  · case listAppVar.listAppId K' ne _ _ => nomatch ne K'
  · case listAppVar.listAppl v' _ st' => exact not_step v' st'
  · case listAppVar.listAppr st' => exact not_step var st'
  · case listAppApp.listAppId K' ne _ _ => nomatch ne K'
  · case listAppApp.listAppl v' _ _ st' => exact not_step v' st'
  · case listAppApp.listAppr v' _ st' => exact not_step v' st'
termination_by sizeOf A
decreasing_by
  all_goals try (
    rename A = _ => eq
    cases eq
    simp_arith
  )
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  apply Range.mem_map_of_mem
  rename_i eq _ _ _ _ _ _ _
  cases eq
  exact ⟨Nat.zero_le _, Nat.lt_add_of_pos_right (Nat.succ_pos _), Nat.mod_one _⟩

end Type.IsValue

local
instance : Inhabited «Type» where
  default := .list [] none

local
instance : Inhabited Kind where
  default := .star

namespace SmallStep

instance : Coe [[Δ ⊢ A -> B]] [[Δ ⊢ A ->* B]] where
  coe := .single

theorem list' (A₁st : [[Δ ⊢ A₁ -> A₁']]) : SmallStep Δ (.list (A₀ ++ A₁ :: A₂) (Option.someIf K b))
    (.list (A₀ ++ A₁' :: A₂) (Option.someIf K b)) := by
  rw [← Range.map_get!_eq (as := A₀), ← Range.map_get!_eq (as := A₂)]
  exact list A₁st

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
  | eta Bki, _ => Bki.TypeVarLocallyClosed_of
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
  | appr B'st, .app A'lc B'lc => .app A'lc (B'st.preserve_lc B'lc)
  | .forall I A'st (A' := A''), .forall A'lc => by
    let ⟨a, anin⟩ := A''.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA'', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A''lc := A'st a aninI |>.preserve_lc A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A''lc
    exact .forall A''lc
  | arrl A'st, .arr A'lc B'lc => .arr (A'st.preserve_lc A'lc) B'lc
  | arrr B'st, .arr A'lc B'lc => .arr A'lc (B'st.preserve_lc B'lc)
  | list A'st, .list A'lc => by
    apply Type.TypeVarLocallyClosed.list
    intro A' mem
    match List.mem_append.mp mem with
    | .inl mem' => exact A'lc _ <| List.mem_append.mpr <| .inl mem'
    | .inr (.head _) => exact A'st.preserve_lc <| A'lc _ <| List.mem_append.mpr <| .inr <| .head ..
    | .inr (.tail _ mem') => exact A'lc _ <| List.mem_append.mpr <| .inr <| mem'.tail _
  | listAppl A'st, .listApp A'lc B'lc => .listApp (A'st.preserve_lc A'lc) B'lc
  | listAppr B'st, .listApp A'lc B'lc => .listApp A'lc (B'st.preserve_lc B'lc)
  | prod A'st, .prod A'lc => .prod <| A'st.preserve_lc A'lc
  | sum A'st, .sum A'lc => .sum <| A'st.preserve_lc A'lc

theorem preserve_lc_rev : [[Δ ⊢ A -> B]] → B.TypeVarLocallyClosed → A.TypeVarLocallyClosed
  | eta .., Blc => .lam <| .app Blc.weaken <| .var_bound Nat.one_pos
  | lamApp _ B'v, Blc =>
    .app (.lam (Blc.weaken (n := 1).Type_open_drop Nat.one_pos)) B'v.TypeVarLocallyClosed_of
  | listAppList A'ki, .list Blc' => by
    refine .listApp A'ki.TypeVarLocallyClosed_of <| .list ?_
    intro _ mem
    rcases Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
    let .app _ B'lc := Blc' _ <| Range.mem_map_of_mem mem'
    exact B'lc
  | listAppId .., A'lc => .listApp (.lam (.var_bound Nat.one_pos)) A'lc
  | listAppComp A₀lc A₁ki, .listApp (.lam (.app _ (.app _ _))) B'lc =>
    .listApp A₀lc <| .listApp A₁ki.TypeVarLocallyClosed_of B'lc
  | lam I A'st (A := A'), .lam A'lc => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A'lc := A'st a aninI |>.preserve_lc_rev A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact .lam A'lc
  | appl A'st, .app A'lc B'lc => .app (A'st.preserve_lc_rev A'lc) B'lc
  | appr B'st, .app A'lc B'lc => .app A'lc (B'st.preserve_lc_rev B'lc)
  | .forall I A'st (A := A'), .forall A'lc => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    let A'lc' := A'lc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at A'lc'
    let A'lc := A'st a aninI |>.preserve_lc_rev A'lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact .forall A'lc
  | arrl A'st, .arr A'lc B'lc => .arr (A'st.preserve_lc_rev A'lc) B'lc
  | arrr B'st, .arr A'lc B'lc => .arr A'lc (B'st.preserve_lc_rev B'lc)
  | list A'st, .list A'lc => by
    apply Type.TypeVarLocallyClosed.list
    intro A' mem
    match List.mem_append.mp mem with
    | .inl mem' => exact A'lc _ <| List.mem_append.mpr <| .inl mem'
    | .inr (.head _) =>
      exact A'st.preserve_lc_rev <| A'lc _ <| List.mem_append.mpr <| .inr <| .head ..
    | .inr (.tail _ mem') => exact A'lc _ <| List.mem_append.mpr <| .inr <| mem'.tail _
  | listAppl A'st, .listApp A'lc B'lc => .listApp (A'st.preserve_lc_rev A'lc) B'lc
  | listAppr B'st, .listApp A'lc B'lc => .listApp A'lc (B'st.preserve_lc_rev B'lc)
  | prod A'st, .prod A'lc => .prod <| A'st.preserve_lc_rev A'lc
  | sum A'st, .sum A'lc => .sum <| A'st.preserve_lc_rev A'lc

open «Type» in
theorem TypeVar_subst_var (Ast : [[Δ, a : K, Δ' ⊢ A -> B]]) (a'ninΔ : [[a' ∉ dom(Δ)]])
  (aninΔ' : [[a ∉ dom(Δ')]] := by nofun) (a'ninΔ' : [[a' ∉ dom(Δ')]] := by nofun)
  : [[Δ, a' : K, Δ' ⊢ A[a' / a] -> B[a' / a] ]] := by match Ast with
  | eta Bki =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, if_neg nofun]
    exact eta <| Bki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | lamApp A'ki B'ki =>
    rw [TypeVar_subst, TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free]
    let A'ki' := A'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
    rw [TypeVar_subst] at A'ki' ⊢
    exact lamApp A'ki' (B'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ')
  | listAppList A'ki (K₁ := K₁) (K₂ := K₂) =>
    rename_i A' _ B' _
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
    exact listAppList (A'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ')
  | listAppId A'ki =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, if_neg nofun]
    exact listAppId <| A'ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | listAppComp A₀lc A₁ki =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst,
        TypeVar_subst]
    exact listAppComp (A₀lc.TypeVar_subst .var_free) <|
      A₁ki.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
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
  | appr B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact appr <| B'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | .forall I A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    apply «forall» <| a :: a' :: I
    intro a'' a''nin
    let ⟨ane, a''nina'I⟩ := List.not_mem_cons.mp a''nin
    let ⟨a'ne, a''ninI⟩ := List.not_mem_cons.mp a''nina'I
    rw [TypeVar_open_TypeVar_subst_var_comm ane.symm, TypeVar_open_TypeVar_subst_var_comm ane.symm]
    specialize A'st a'' a''ninI
    rw [← Environment.append] at A'st ⊢
    apply A'st.TypeVar_subst_var a'ninΔ _ _
    all_goals rw [Environment.TypeVarNotInDom, Environment.TypeVarInDom, Environment.typeVarDom]
    · exact List.not_mem_cons.mpr ⟨ane.symm, aninΔ'⟩
    · exact List.not_mem_cons.mpr ⟨a'ne.symm, a'ninΔ'⟩
  | arrl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact arrl <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | arrr B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact arrr <| B'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | list A₁st =>
    rw [TypeVar_subst, List.mapMem_eq_map, List.map_append, List.map_cons, List.map_map,
        List.map_map, ← Range.map, ← Range.map, TypeVar_subst, List.mapMem_eq_map, List.map_append,
        List.map_cons, List.map_map, List.map_map, ← Range.map, ← Range.map]
    exact list <| A₁st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | listAppl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact listAppl <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | listAppr B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact listAppr <| B'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | prod A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact prod <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
  | sum A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact sum <| A'st.TypeVar_subst_var a'ninΔ aninΔ' a'ninΔ'
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  exact Nat.le_of_lt <| Nat.lt_add_right _ <| List.sizeOf_lt_of_mem <| List.mem_append.mpr <|
    .inr <| .head _

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
  | eta A'ki => eta <| A'ki.weakening ΔΔ'Δ''wf
  | lamApp A'ki B'ki => lamApp (A'ki.weakening ΔΔ'Δ''wf) (B'ki.weakening ΔΔ'Δ''wf)
  | listAppList A'ki => listAppList <| A'ki.weakening ΔΔ'Δ''wf
  | listAppId A'ki => listAppId <| A'ki.weakening ΔΔ'Δ''wf
  | listAppComp A₀lc A₁ki => listAppComp A₀lc <| A₁ki.weakening ΔΔ'Δ''wf
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
  | appr B'st => appr <| B'st.weakening ΔΔ'Δ''wf
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
  | arrr B'st => arrr <| B'st.weakening ΔΔ'Δ''wf
  | list A₁st => list <| A₁st.weakening ΔΔ'Δ''wf
  | listAppl A'st => listAppl <| A'st.weakening ΔΔ'Δ''wf
  | listAppr B'st => listAppr <| B'st.weakening ΔΔ'Δ''wf
  | prod A'st => prod <| A'st.weakening ΔΔ'Δ''wf
  | sum A'st => sum <| A'st.weakening ΔΔ'Δ''wf
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem Environment_TypeVar_subst_swap : [[Δ, Δ'[B / a] ⊢ A -> A']] → [[Δ, Δ'[B' / a] ⊢ A -> A']]
  | eta A'ki => eta A'ki.Environment_TypeVar_subst_swap
  | lamApp A'ki B'ki =>
    lamApp A'ki.Environment_TypeVar_subst_swap B'ki.Environment_TypeVar_subst_swap
  | listAppList A'ki => listAppList A'ki.Environment_TypeVar_subst_swap
  | listAppId A'ki => listAppId A'ki.Environment_TypeVar_subst_swap
  | listAppComp A₀lc A₁ki => listAppComp A₀lc A₁ki.Environment_TypeVar_subst_swap
  | lam I A'st => by
    apply lam I
    intro a' a'nin
    specialize A'st a' a'nin
    rw [← Environment.append, ← Environment.TypeVar_subst] at A'st ⊢
    exact A'st.Environment_TypeVar_subst_swap
  | appl A'st => appl A'st.Environment_TypeVar_subst_swap
  | appr B'st => appr B'st.Environment_TypeVar_subst_swap
  | «forall» I A'st => by
    apply «forall» I
    intro a' a'nin
    specialize A'st a' a'nin
    rw [← Environment.append, ← Environment.TypeVar_subst] at A'st ⊢
    exact A'st.Environment_TypeVar_subst_swap
  | arrl A'st => arrl A'st.Environment_TypeVar_subst_swap
  | arrr B'st => arrr B'st.Environment_TypeVar_subst_swap
  | list A₁st => list A₁st.Environment_TypeVar_subst_swap
  | listAppl A'st => listAppl A'st.Environment_TypeVar_subst_swap
  | listAppr B'st => listAppr B'st.Environment_TypeVar_subst_swap
  | prod A'st => prod A'st.Environment_TypeVar_subst_swap
  | sum A'st => sum A'st.Environment_TypeVar_subst_swap
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem TypeVar_drop_of_not_mem_freeTypeVars (aninA : a ∉ A.freeTypeVars)
  (st : [[Δ, a : K, Δ' ⊢ A -> B]]) : [[Δ, Δ' ⊢ A -> B]] := by
  cases st <;> simp [Type.freeTypeVars] at aninA
  · case eta A'ki => exact eta <| A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA
  · case lamApp A'ki B'ki =>
    let ⟨aninA', aninB'⟩ := aninA
    apply lamApp (A'ki.TypeVar_drop_of_not_mem_freeTypeVars _)
      (B'ki.TypeVar_drop_of_not_mem_freeTypeVars aninB')
    simp [Type.freeTypeVars]
    exact aninA'
  · case listAppList A'ki =>
    exact listAppList <| A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case listAppId A'ki => exact listAppId <| A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA
  · case listAppComp A₀lc A₁ki =>
    exact listAppComp A₀lc <| A₁ki.TypeVar_drop_of_not_mem_freeTypeVars aninA.right.left
  · case lam I A'st =>
    apply lam <| a :: I
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'st a' a'ninI
    rw [← Environment.append] at A'st ⊢
    apply A'st.TypeVar_drop_of_not_mem_freeTypeVars <|
      Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  · case appl A'st => exact appl <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case appr B'st => exact appr <| B'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right
  · case «forall» I A'st =>
    apply «forall» <| a :: I
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'st a' a'ninI
    rw [← Environment.append] at A'st ⊢
    apply A'st.TypeVar_drop_of_not_mem_freeTypeVars <|
      Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  · case arrl A'st => exact arrl <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case arrr B'st => exact arrr <| B'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right
  · case list A₁st =>
    exact list <| A₁st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right.left
  · case listAppl A'st => exact listAppl <| A'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.left
  · case listAppr B'st =>
    exact listAppr <| B'st.TypeVar_drop_of_not_mem_freeTypeVars aninA.right
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
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

end SmallStep

namespace «Type»

@[simp]
private
def _root_.TabularTypeInterpreter.«F⊗⊕ω».Type.sizeOf' : «Type» → Nat
  | .var _ => 1
  | .lam _ A | .forall _ A | .prod A | .sum A => 1 + sizeOf' A
  | .app A B | .arr A B | .listApp A B => 1 + sizeOf' A + sizeOf' B
  | .list As _ => 1 + (As.mapMem fun A _ => sizeOf' A).sum
termination_by A => sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  assumption

@[simp]
theorem sizeOf'_pos (A : «Type») : 0 < sizeOf' A := by
  cases A
  all_goals simp

@[simp]
theorem TypeVar_open_sizeOf' (A : «Type») : sizeOf' (A.TypeVar_open a n) = sizeOf' A := by
  induction A using rec_uniform generalizing n
  case list ih =>
    rw [TypeVar_open, List.mapMem_eq_map, sizeOf', List.mapMem_eq_map, List.map_map, sizeOf',
        List.mapMem_eq_map]
    apply Nat.add_right_inj.mpr
    apply List.sum_map_eq_of_eq_of_mem
    intro A' mem
    rw [Function.comp, ih A' mem]
  all_goals aesop (add simp [TypeVar_open])

end «Type»

namespace SmallStep

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
        exact .inr ⟨_, .eta (A''ki.TypeVar_drop_of_not_mem_freeTypeVars aninA' (Δ' := .empty))⟩
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
        | lam I A''ki => exact .inr ⟨_, .lamApp (.lam I A''ki) B'ki⟩
        | app => exact .inl <| .appApp A'v B'v
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .appr B'st⟩
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
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .arrr B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .arrl A'st⟩
  | .list A's K?, Aki => by
    rw [← Range.map_get!_eq (as := A's), ← Option.someIf_get!_eq (x? := K?)] at Aki
    rcases Aki.inv_list' with ⟨K', rfl, A'ki, h⟩
    clear Aki
    rw [← List.reverse_reverse A's] at *
    generalize A's'eq : A's.reverse = A's' at *
    match A's' with
    | [] =>
      have : [] = [:0].map fun i => (fun _ => default (α := «Type»)) i := by
        rw [Range.map_same_eq_nil]
      rw [List.reverse_nil, this, ← Option.someIf_get!_eq (x? := K?)]
      exact .inl <| .list nofun
    | A'' :: A's' =>
      rw [List.reverse_cons, List.length_append, List.length_singleton] at A'ki
      have := progress (A := .list A's'.reverse (Option.someIf K' true)) <| by
        rw [← Range.map_get!_eq (as := A's'.reverse)]
        apply Kinding.list _ <| .inr rfl
        swap
        intro i mem
        have :  A's'.reverse.get! i = (A's'.reverse ++ [A'']).get! i := by
          simp [List.getElem?_append_left mem.upper]
        rw [this]
        exact A'ki i ⟨Nat.zero_le _, Nat.lt_succ_of_lt mem.upper, Nat.mod_one _⟩
      match this with
      | .inl h =>
        generalize A's''eq : A's'.reverse = A's'', Option.someIf .. = K'' at h
        let .list A's'v := h
        let lengths_eq : List.length (List.reverse _) = _ := by rw [A's''eq]
        rw [List.length_reverse, List.length_map, Range.length_toList, Nat.sub_zero] at lengths_eq
        cases lengths_eq
        let A''ki := A'ki A's'.reverse.length ⟨Nat.zero_le _, Nat.le.refl, Nat.mod_one _⟩
        simp at A''ki
        match progress A''ki with
        | .inl A'v =>
          left
          rw [List.reverse_cons, ← Range.map_get!_eq (as := _ ++ _),
              ← Option.someIf_get!_eq (x? := K?)]
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
          refine ⟨.list (A's'.reverse ++ [A''']) K?, ?_⟩
          rw [List.reverse_cons, ← Option.someIf_get!_eq (x? := K?)]
          exact list' A''st
      | .inr ⟨A's'', A's'st⟩ =>
        right
        generalize A's'''eq : A's'.reverse = A's''', Option.someIf .. = K'' at A's'st
        cases A's'st
        case list A₁' m A₀ n A₂ K''' b A₁st =>
        refine ⟨[[{</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] />, A'' </ : K?.get! // K?.isSome />}]], ?_⟩
        rw [List.reverse_cons, A's'''eq, List.append_assoc, List.cons_append]
        rw (occs := .pos [1]) [← Option.someIf_get!_eq (x? := K?)]
        exact list' A₁st
  | .listApp A' B', .listApp A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => by
        by_cases ∃ K', A' = [[λ a : K'. a$0]]
        · case pos h =>
          rcases h with ⟨_, rfl⟩
          let .lam .. := A'ki
          exact .inr ⟨_, .listAppId B'ki⟩
        · case neg ne =>
          apply not_exists.mp at ne
          cases B'ki with
          | var => exact .inl <| .listAppVar ne A'v
          | app => exact .inl <| .listAppApp ne A'v B'v
          | list => exact .inr ⟨_, .listAppList A'ki⟩
          | listApp B''ki => exact .inr ⟨_, .listAppComp A'ki.TypeVarLocallyClosed_of B''ki⟩
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .listAppr B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .listAppl A'st⟩
  | .prod A', .prod A'ki => match progress A'ki with
    | .inl A'v => .inl <| .prod A'v
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .prod A'stB'⟩
  | .sum A', .sum A'ki => match progress A'ki with
    | .inl A'v => .inl <| .sum A'v
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .sum A'stB'⟩
termination_by A.sizeOf'
decreasing_by
  all_goals simp_arith
  all_goals (
    let eq : List.reverse (List.reverse _) = _ := by rw [A's'eq]
    rw [List.reverse_reverse] at eq
    rw [eq, List.reverse_cons]
  )
  · apply Nat.lt_of_add_lt_add_right (n := 1)
    simp_arith
  · apply Nat.le_of_add_le_add_right (b := 1)
    simp_arith

theorem preservation : [[Δ ⊢ A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ B : K]]
  | .eta Bki, .lam I Baki => by
    let ⟨a, anin⟩ := B.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninB, aninI⟩ := List.not_mem_append'.mp anin
    specialize Baki a aninI
    simp [Type.TypeVar_open, Bki.TypeVarLocallyClosed_of.TypeVar_open_id] at Baki
    let .app Bki (.var .head) := Baki
    exact Bki.TypeVar_drop_of_not_mem_freeTypeVars aninB (Δ' := .empty)
  | .lamApp _ _ (A := A'), .app (.lam I A'ki) B'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    A'ki a aninI |>.Type_open_preservation aninA' B'ki
  | .listAppList A'ki (b := b), .listApp A'ki' B'ki => by
    cases A'ki.deterministic A'ki'
    let ⟨B'ki', h⟩ := B'ki.inv_list
    apply Kinding.list (.app A'ki <| B'ki' · ·)
    split at h
    · case isTrue h' => exact .inr h'
    · case isFalse => exact .inl h
  | .listAppId _, .listApp (.lam I aki) A'ki => by
    let ⟨a, anin⟩ := I.exists_fresh
    specialize aki a anin
    rw [Type.TypeVar_open, if_pos rfl] at aki
    let .var .head := aki
    exact A'ki
  | .listAppComp A₀lc A₁ki, .listApp A₀ki (.listApp A₁ki' Bki) => by
    cases A₁ki.deterministic A₁ki'
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
  | .appr B'st, .app A'ki B'ki => .app A'ki <| B'st.preservation B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.preservation A'ki) B'ki
  | .arrr B'st, .arr A'ki B'ki => .arr A'ki <| B'st.preservation B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation (A'st a aninI) <| A'ki a aninI'
  | .list A₁st (m := m) (n := n) (K := K) (b := b), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rcases Aki.inv_list' with ⟨K', rfl, Aki', h⟩
    have : Option.someIf K b = Option.someIf K' b := by
      split at h
      · case isTrue h' => rw [h', Option.someIf_true, Option.someIf_true, h]
      · case isFalse h' => rw [Bool.not_eq_true _ |>.mp h', Option.someIf_false, Option.someIf_false]
    rw [this]
    apply Kinding.list _ <| by
      split at h
      · case isTrue h' => exact .inr h'
      · case isFalse =>
        rw [List.length_append, List.length_map, Range.length_toList, List.length_cons,
            List.length_map, Range.length_toList] at h ⊢
        exact .inl h
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
  | .listAppr B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.preservation B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.preservation A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.preservation A'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem preservation_rev : [[Δ ⊢ A -> B]] → [[Δ ⊢ B : K]] → [[Δ ⊢ A : K]]
  | .eta Bki, Bki' => by
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
  | .lamApp (.lam I A'ki) B'ki (A := A'), Bki => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    cases A'ki a aninI |>.Type_open_preservation aninA' B'ki |>.deterministic Bki
    exact .app (.lam I A'ki) B'ki
  | .listAppList A'ki (K₂ := K₂) (n := n), ki => by
    rcases ki.inv_list' with ⟨_, rfl, ki', h⟩
    match n with
    | 0 =>
      rw [Range.map_same_eq_nil]
      rw [Range.map_same_eq_nil] at ki
      split at h
      case isFalse => nomatch h
      case isTrue h' =>
      convert Kinding.listApp A'ki .empty_list
      · rw [h', Option.someIf_true]
      · exact h.symm
    | _ + 1 =>
      let .app A'ki' _ := ki' 0 ⟨Nat.zero_le _, Nat.add_one_pos _, Nat.mod_one _⟩
      cases A'ki.deterministic A'ki'
      apply Kinding.listApp A'ki
      apply Kinding.list
      · intro i mem
        specialize ki' i mem
        let .app A'ki'' B'ki := ki'
        cases A'ki.deterministic A'ki''
        exact B'ki
      · split at h
        · case isTrue h' => exact .inr h'
        · case isFalse => exact .inl h
  | .listAppId Bki, Bki' => by
    cases Bki.deterministic Bki'
    exact .listApp .id Bki'
  | .listAppComp A₀lc A₁ki (A₀ := A₀) (A₁ := A₁), .listApp (.lam I A₀A₁ki) B'ki => by
    let ⟨a, anin⟩ := A₀.freeTypeVars ++ A₁.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA₀A₁, aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninA₀, aninA₁⟩ := List.not_mem_append'.mp aninA₀A₁
    specialize A₀A₁ki a aninI
    simp [Type.TypeVar_open] at A₀A₁ki
    let .app A₀ki (.app A₁ki' (.var .head)) := A₀A₁ki
    rw [A₀lc.TypeVar_open_id] at A₀ki
    rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id] at A₁ki'
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
  | .appr B'st, .app A'ki B'ki => .app A'ki <| B'st.preservation_rev B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.preservation_rev A'ki) B'ki
  | .arrr B'st, .arr A'ki B'ki => .arr A'ki <| B'st.preservation_rev B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation_rev (A'st a aninI) <| A'ki a aninI'
  | .list A₁st (m := m) (n := n) (K := K) (b := b), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rcases Aki.inv_list' with ⟨K', rfl, Aki', h⟩
    have : Option.someIf K b = Option.someIf K' b := by
      split at h
      · case isTrue h' => rw [h', Option.someIf_true, Option.someIf_true, h]
      · case isFalse h' => rw [Bool.not_eq_true _ |>.mp h', Option.someIf_false, Option.someIf_false]
    rw [this]
    apply Kinding.list _ <| by
      split at h
      · case isTrue h' => exact .inr h'
      · case isFalse =>
        rw [List.length_append, List.length_map, Range.length_toList, List.length_cons,
            List.length_map, Range.length_toList] at h ⊢
        exact .inl h
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
  | .listAppr B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.preservation_rev B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.preservation_rev A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.preservation_rev A'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem Equivalence_of : [[Δ ⊢ A -> B]] → [[Δ ⊢ A ≡ B]]
  | .eta A'ki => .eta A'ki
  | .lamApp A'ki B'ki .. => .lamApp A'ki B'ki
  | .listAppList A'ki => .listAppList A'ki
  | .listAppId A'ki => .listAppId A'ki
  | .listAppComp A₀lc A₁ki => .listAppComp A₀lc A₁ki
  | .lam I A'st => .lam I (A'st · · |>.Equivalence_of)
  | .appl A'st => .app A'st.Equivalence_of .refl
  | .appr B'st => .app .refl B'st.Equivalence_of
  | .arrl A'st => .arr A'st.Equivalence_of .refl
  | .arrr B'st => .arr .refl B'st.Equivalence_of
  | .forall I A'st => .scheme I (A'st · · |>.Equivalence_of)
  | .list A'st (m := m) (n := n) => by
    rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)]
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
    · case a.isTrue h =>
      rw [List.getElem?_append_left h, List.getElem?_eq_getElem h]
      simp
      rw [List.length_map, Range.length_toList] at h
      rw [Range.getElem_toList h, Nat.zero_add]
      exact .refl
    · case a.isFalse h =>
      rw [List.getElem?_append_right (Nat.le_of_not_lt h)]
      rw [List.getElem?_cons]
      split
      · case isTrue h' =>
        simp
        rw [List.length_map] at h'
        rw [h', List.getElem?_cons_zero, Option.getD]
        exact A'st.Equivalence_of
      · case isFalse h' =>
        rw [List.getElem?_cons, if_neg h']
        exact .refl
  | .listAppl A'st => .listApp A'st.Equivalence_of .refl
  | .listAppr B'st => .listApp .refl B'st.Equivalence_of
  | .prod A'st => .prod A'st.Equivalence_of
  | .sum A'st => .sum A'st.Equivalence_of
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

-- Inversion

-- the conclusion should be the reflexive closure of st but we can use this weaker version.
theorem inv_arr (ArBst: [[ Δ ⊢ (A → B) -> T ]]): ∃ A' B', T = [[ (A' → B') ]] ∧ [[ Δ ⊢ A ->* A' ]] ∧ [[ Δ ⊢ B ->* B' ]] := by
  cases ArBst <;> aesop (add unsafe constructors [Relation.ReflTransGen, SmallStep])

theorem inv_forall (Ast: [[ Δ ⊢ (∀ a? : K. A) -> T ]]): ∃ A', T = [[∀ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a ->* A'^a ]] := by
  cases Ast
  aesop (add unsafe tactic guessI, unsafe constructors [Relation.ReflTransGen, SmallStep])

theorem inv_prod (Ast: [[ Δ ⊢ ⊗A -> T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ->* A' ]] := by
  cases Ast; aesop (add unsafe constructors [Relation.ReflTransGen, SmallStep])

theorem inv_sum (Ast: [[ Δ ⊢ ⊕A -> T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ->* A' ]] := by
  cases Ast; aesop (add unsafe constructors [Relation.ReflTransGen, SmallStep])

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

theorem inv_list (Ast: [[ Δ ⊢ { </ A@i // i in [:n] /> </ : K // b /> } -> T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> </ : K // b /> }]] ∧ [[ </ Δ ⊢ A@i ->* B@i // i in [:n] /> ]] := by
  generalize T_eq : [[{ </ A@i // i in [:n] /> </ : K // b /> } ]] = T_ at Ast
  cases Ast <;> try cases T_eq
  . case list A₁ A₁' n₀ A₀i n₂ A₂i _ b A₁st =>
    injection T_eq with eq eq'
    have nlen: n = n₀ + 1 + n₂ := by
      apply congrArg List.length at eq
      rw [List.length_append, List.length_cons] at eq
      repeat' rw [List.length_map] at eq
      repeat' rw [Std.Range.length_toList] at eq
      omega
    refine ⟨(fun i => if i < n₀ then A₀i i else if i = n₀ then A₁' else A₂i (i - n₀ - 1)), ?_, λ i iltn => ?_⟩
    . simp; rw [nlen, ← sandwich', eq']; exact ⟨rfl, rfl⟩
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
        exact .single A₁st
      . case _ Niltn₀ Nieqn₀ =>
        specialize A₂eq (i - n₀ - 1) (by simp_all [Membership.mem] ; omega)
        rw [← A₂eq]
        rwomega i - n₀ - 1 + (n₀ + 1) = i

end SmallStep

namespace MultiSmallStep

theorem est_of : [[Δ ⊢ A ->* B]] → [[Δ ⊢ A <->* B]] := Relation.ReflTransGen.to_eqvGen

theorem preserve_lc (st : [[Δ ⊢ A ->* B]]) (Alc : A.TypeVarLocallyClosed) : B.TypeVarLocallyClosed := by
  induction st with
  | refl => exact Alc
  | tail _ st ih => exact st.preserve_lc ih

open «Type» in
theorem TypeVar_subst_var (Amst : [[Δ, a : K ⊢ A ->* B]]) (a'ninΔ : [[a' ∉ dom(Δ)]])
  : [[Δ, a' : K ⊢ A[a' / a] ->* B[a' / a] ]] := by
  induction Amst with
  | refl => rfl
  | tail _ st ih => exact .tail ih <| st.TypeVar_subst_var a'ninΔ (Δ' := .empty)

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
  | tail _ st ih =>
    cases Δ'''eq
    exact .tail ih <| st.weakening ΔΔ'Δ''wf

theorem Environment_TypeVar_subst_swap (mst : [[Δ, Δ'[B / a] ⊢ A ->* A']])
  : [[Δ, Δ'[B' / a] ⊢ A ->* A']] := by
  generalize Δ''eq : [[Δ, Δ'[B / a] ]] = Δ'' at mst
  induction mst with
  | refl =>
    cases Δ''eq
    rfl
  | tail _ st ih =>
    cases Δ''eq
    exact .tail ih st.Environment_TypeVar_subst_swap

theorem preservation (Amst : [[Δ ⊢ A ->* B]]) (Aki : [[Δ ⊢ A : K]]) : [[Δ ⊢ B : K]] := by
  induction Amst with
  | refl => exact Aki
  | tail _ st ih => exact st.preservation ih

theorem EqSmallStep_of : [[Δ ⊢ A ->* B]] → [[Δ ⊢ A <->* B]] := Relation.ReflTransGen.to_eqvGen

theorem Equivalence_of (Amst : [[Δ ⊢ A ->* B]]) : [[Δ ⊢ A ≡ B]] := by
  induction Amst with
  | refl => exact .refl
  | tail _ st ih => exact ih.trans <| st.Equivalence_of

theorem lam (I : List TypeVarId) (Alc : A.TypeVarLocallyClosed 1)
  (Amst : ∀ a ∉ I, [[Δ, a : K ⊢ A^a ->* A'^a]]) : [[Δ ⊢ λ a : K. A ->* λ a : K. A']] := by
  let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
  let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
  let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
  specialize Amst a aninI
  generalize A''eq : A.TypeVar_open a = A'', A'''eq : A'.TypeVar_open a = A''' at Amst
  clear anin aninAA'
  induction Amst using Relation.ReflTransGen.trans_induction_on generalizing A A' with
  | ih₁ =>
    cases A''eq
    cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA A'''eq
    rfl
  | ih₂ st =>
    cases A''eq
    cases A'''eq
    apply Relation.ReflTransGen.single
    apply SmallStep.lam <| I ++ Δ.typeVarDom
    intro a' a'nin
    let ⟨a'ninI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    replace st := st.TypeVar_open_swap Alc aninA a'ninΔ
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at st
    exact st
  | ih₃ mst _ ih₀ ih₁ =>
    cases A''eq
    cases A'''eq
    let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc'
    let Blc := preserve_lc mst Alc'
    exact .trans
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close rfl
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc)) <|
      ih₁ Blc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc) rfl

theorem app : [[Δ ⊢ A ->* A']] → [[Δ ⊢ B ->* B']] → [[Δ ⊢ A B ->* A' B']] :=
  Relation.ReflTransGen.map₂ .appl .appr

theorem «forall» (I : List TypeVarId) (Alc : A.TypeVarLocallyClosed 1)
  (Amst : ∀ a ∉ I, [[Δ, a : K ⊢ A^a ->* A'^a]]) : [[Δ ⊢ ∀ a : K. A ->* ∀ a : K. A']] := by
  let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
  let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
  let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
  specialize Amst a aninI
  generalize A''eq : A.TypeVar_open a = A'', A'''eq : A'.TypeVar_open a = A''' at Amst
  clear anin aninAA'
  induction Amst using Relation.ReflTransGen.trans_induction_on generalizing A A' with
  | ih₁ =>
    cases A''eq
    cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA' aninA A'''eq
    rfl
  | ih₂ st =>
    cases A''eq
    cases A'''eq
    apply Relation.ReflTransGen.single
    apply SmallStep.forall <| I ++ Δ.typeVarDom
    intro a' a'nin
    let ⟨a'ninI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    replace st := st.TypeVar_open_swap Alc aninA a'ninΔ
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at st
    exact st
  | ih₃ mst _ ih₀ ih₁ =>
    cases A''eq
    cases A'''eq
    let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc'
    let Blc := preserve_lc mst Alc'
    exact .trans
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close rfl
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc)) <|
      ih₁ Blc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id Blc) rfl

theorem arr : [[Δ ⊢ A ->* A']] → [[Δ ⊢ B ->* B']] → [[Δ ⊢ A → B ->* A' → B']] :=
  Relation.ReflTransGen.map₂ .arrl .arrr

theorem list (Amst : ∀ i ∈ [:n], [[Δ ⊢ A@i ->* A'@i]])
  : [[Δ ⊢ {</ A@i // i in [:n] /> </ : K // b />} ->* {</ A'@i // i in [:n] /> </ : K // b />}]] := by
  rw (occs := .pos [2]) [Range.map]
  rw [← Range.map_append (Nat.zero_le _) Nat.le.refl, ← Range.map, ← Range.map]
  rw (occs := .pos [3]) [Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = A i
    nomatch Nat.not_lt_of_le mem.lower mem.upper
  )]
  generalize meq : n = m
  rw (occs := .pos [1, 4]) [← meq]
  let mlen := Nat.le_refl n
  rw (occs := .pos [1]) [meq] at mlen
  clear meq
  induction m with
  | zero => rw [Range.map_same_eq_nil, List.nil_append]
  | succ m' ih =>
    refine .trans (ih (Nat.le_of_succ_le mlen)) ?_
    rw [Range.map_eq_cons_of_lt <| Nat.lt_of_succ_le mlen,
        Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one,
        List.append_assoc, List.singleton_append,
        ← Range.map_shift (m := m' + 1) (j := m' + 1) Nat.le.refl,
        Nat.sub_self]
    specialize Amst m' ⟨Nat.zero_le _, Nat.lt_of_succ_le mlen, Nat.mod_one _⟩
    generalize A''eq : A m' = A'', A'''eq : A' m' = A'''
    rw [A''eq, A'''eq] at Amst
    clear A''eq A'''eq
    induction Amst with
    | refl => rfl
    | tail _ st ih => exact ih.tail <| .list st

theorem list' (A₁mst : [[Δ ⊢ A₁ ->* A₁']])
  : [[Δ ⊢ {</ A₀@i // i in [:m] />, A₁, </ A₂@j // j in [:n] /> </ : K // b />} ->* {</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] /> </ : K // b />}]] := by
  induction A₁mst with
  | refl => rfl
  | tail _ st ih => exact ih.tail <| .list st

theorem listApp : [[Δ ⊢ A ->* A']] → [[Δ ⊢ B ->* B']] → [[Δ ⊢ A ⟦B⟧ ->* A' ⟦B'⟧]] :=
  Relation.ReflTransGen.map₂ .listAppl .listAppr

theorem prod : [[Δ ⊢ A ->* A']] → [[Δ ⊢ ⊗ A ->* ⊗ A']] := Relation.ReflTransGen.map .prod

theorem sum : [[Δ ⊢ A ->* A']] → [[Δ ⊢ ⊕ A ->* ⊕ A']] := Relation.ReflTransGen.map .sum

end MultiSmallStep

namespace SmallStep

theorem TypeVar_subst_out (Bst : [[Δ ⊢ B -> B']]) (Alc : A.TypeVarLocallyClosed)
  (Bki : [[Δ ⊢ B : K]]) (Δwf : [[⊢ Δ]]) : [[Δ ⊢ A[B / a] ->* A[B' / a] ]] := by
  cases A <;> simp [Type.TypeVar_subst]
  · case var =>
    split
    · case isTrue h =>
      cases h
      exact ↑Bst
    · case isFalse h => rfl
  · case lam K _ =>
    let .lam A'lc := Alc
    let Blc := Bki.TypeVarLocallyClosed_of
    apply MultiSmallStep.lam (a :: Δ.typeVarDom) <| A'lc.TypeVar_subst Blc.weaken
    intro a' a'nin
    let ⟨ane, a'ninΔ⟩ := List.not_mem_cons.mp a'nin
    rw [← Blc.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bst.preserve_lc Blc |>.TypeVar_open_TypeVar_subst_comm ane.symm]
    let Δawf := Δwf.typeVarExt a'ninΔ (K := K)
    replace A'lc := A'lc.Type_open_dec .var_free (B := .var (.free a'))
    rw [← Type.Type_open_var] at A'lc
    exact TypeVar_subst_out (Bst.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) A'lc
      (Bki.weakening_r (fun | _, .head _ => a'ninΔ) (Δ' := .typeExt .empty ..)) Δawf
  · case app =>
    let .app A'lc B''lc := Alc
    exact .app (TypeVar_subst_out Bst A'lc Bki Δwf) (TypeVar_subst_out Bst B''lc Bki Δwf)
  · case «forall» K _ =>
    let .forall A'lc := Alc
    let Blc := Bki.TypeVarLocallyClosed_of
    apply MultiSmallStep.forall (a :: Δ.typeVarDom) <| A'lc.TypeVar_subst Blc.weaken
    intro a' a'nin
    let ⟨ane, a'ninΔ⟩ := List.not_mem_cons.mp a'nin
    rw [← Blc.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bst.preserve_lc Blc |>.TypeVar_open_TypeVar_subst_comm ane.symm]
    let Δawf := Δwf.typeVarExt a'ninΔ (K := K)
    replace A'lc := A'lc.Type_open_dec .var_free (B := .var (.free a'))
    rw [← Type.Type_open_var] at A'lc
    exact TypeVar_subst_out (Bst.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)) A'lc
      (Bki.weakening_r (fun | _, .head _ => a'ninΔ) (Δ' := .typeExt .empty ..)) Δawf
  · case arr =>
    let .arr A'lc B''lc := Alc
    exact .arr (TypeVar_subst_out Bst A'lc Bki Δwf) (TypeVar_subst_out Bst B''lc Bki Δwf)
  · case list A's K? =>
    let .list Alc' := Alc
    rw [← Range.map_get!_eq (as := A's), List.map_map, List.map_map,
        ← Option.someIf_get!_eq (x? := K?), ← Range.map, ← Range.map]
    apply MultiSmallStep.list
    intro i mem
    exact TypeVar_subst_out Bst (Alc' _ <| List.get!_mem mem.upper) Bki Δwf
  · case listApp =>
    let .listApp A'lc B''lc := Alc
    exact .listApp (TypeVar_subst_out Bst A'lc Bki Δwf) (TypeVar_subst_out Bst B''lc Bki Δwf)
  · case prod =>
    let .prod A'lc := Alc
    exact .prod <| TypeVar_subst_out Bst A'lc Bki Δwf
  · case sum =>
    let .sum A'lc := Alc
    exact .sum <| TypeVar_subst_out Bst A'lc Bki Δwf
termination_by sizeOf A
decreasing_by
  all_goals (
    rename A = _ => eq
    cases eq
    simp_arith
  )
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  rw [List.getElem?_eq_getElem mem.upper, Option.getD]
  exact List.getElem_mem mem.upper

theorem Type_open_out (Bst : [[Δ ⊢ B -> B']]) (Alc : A.TypeVarLocallyClosed 1)
  (Bki : [[Δ ⊢ B : K]]) (Δwf : [[⊢ Δ]]) : [[Δ ⊢ A^^B ->* A^^B']] := by
  let ⟨a, anin⟩ := A.freeTypeVars.exists_fresh
  rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars anin,
      ← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars anin]
  let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
  rw [← Type.Type_open_var] at Alc'
  exact TypeVar_subst_out Bst Alc' Bki Δwf

theorem TypeVar_subst_in (Ast : [[Δ, a : K, Δ' ⊢ A -> A']]) (Alc : A.TypeVarLocallyClosed)
  (Δwf : [[⊢ Δ, a : K, Δ']]) (Bki : [[Δ ⊢ B : K]])
  : [[Δ, Δ'[B / a] ⊢ A[B / a] ->* A'[B / a] ]] := by
  cases Ast <;> simp [Type.TypeVar_subst]
  · case eta A'ki => exact .single <| eta (A'ki.subst' Δwf Bki)
  · case lamApp A'ki B'ki =>
    rw [Bki.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist]
    replace A'ki := A'ki.subst' Δwf Bki
    rw [Type.TypeVar_subst] at A'ki
    exact .single <| lamApp A'ki (B'ki.subst' Δwf Bki)
  · case listAppList A' _ _ _ B' _ A'ki =>
    rw [Range.map_eq_of_eq_of_mem (by
      intro i mem
      show _ = [[(B'@i[B / a])]]
      simp [Type.TypeVar_subst]
    ), ← Range.map, Range.map_eq_of_eq_of_mem (by
      intro i mem
      show _ = [[(A'[B/ a] B'@i[B / a])]]
      simp [Type.TypeVar_subst]
    ), ← Range.map]
    exact .single <| listAppList (A'ki.subst' Δwf Bki)
  · case listAppId A'ki => exact .single <| listAppId (A'ki.subst' Δwf Bki)
  · case listAppComp A₀lc A₁ki =>
    exact .single <|
      listAppComp (A₀lc.TypeVar_subst Bki.TypeVarLocallyClosed_of) (A₁ki.subst' Δwf Bki)
  · case lam I A'st =>
    let .lam A'lc := Alc
    apply MultiSmallStep.lam (a :: I ++ [[Δ, a : K, Δ']].typeVarDom) <|
      A'lc.TypeVar_subst Bki.TypeVarLocallyClosed_of.weaken
    intro a' a'nin
    let ⟨a'ninaI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'ninaI
    specialize A'st a' a'ninI
    rw [← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Environment.append, ← Environment.TypeVar_subst]
    rw [← Environment.append] at A'st
    replace A'lc := A'lc.Type_open_dec .var_free (B := .var (.free a'))
    rw [← Type.Type_open_var] at A'lc
    exact TypeVar_subst_in A'st A'lc (Δwf.typeVarExt a'ninΔ) Bki
  · case appl A'st =>
    let .app A'lc _ := Alc
    exact .app (TypeVar_subst_in A'st A'lc Δwf Bki) .refl
  · case appr B'st =>
    let .app _ B'lc := Alc
    exact .app .refl <| TypeVar_subst_in B'st B'lc Δwf Bki
  · case «forall» I A'st =>
    let .forall A'lc := Alc
    apply MultiSmallStep.forall (a :: I ++ [[Δ, a : K, Δ']].typeVarDom) <|
      A'lc.TypeVar_subst Bki.TypeVarLocallyClosed_of.weaken
    intro a' a'nin
    let ⟨a'ninaI, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'ninaI
    specialize A'st a' a'ninI
    rw [← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bki.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Environment.append, ← Environment.TypeVar_subst]
    rw [← Environment.append] at A'st
    replace A'lc := A'lc.Type_open_dec .var_free (B := .var (.free a'))
    rw [← Type.Type_open_var] at A'lc
    exact TypeVar_subst_in A'st A'lc (Δwf.typeVarExt a'ninΔ) Bki
  · case arrl A'st =>
    let .arr A'lc _ := Alc
    exact .arr (TypeVar_subst_in A'st A'lc Δwf Bki) .refl
  · case arrr B'st =>
    let .arr _ B'lc := Alc
    exact .arr .refl <| TypeVar_subst_in B'st B'lc Δwf Bki
  · case list A₁st =>
    rw [← Range.map_get!_eq (as := _ ++ _ :: _), List.length_append, List.length_map,
        Range.length_toList, Nat.sub_zero, List.length_cons, List.length_map, Range.length_toList,
        Nat.sub_zero]
    rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
    rw [List.length_append, List.length_map, Range.length_toList, Nat.sub_zero, List.length_cons,
        List.length_map, Range.length_toList, Nat.sub_zero, ← Range.map, ← Range.map]
    refine .list ?_
    intro i mem
    simp
    rw [List.getElem?_append]
    split
    · case isTrue h => rw [List.getElem?_append_left h]
    · case isFalse h =>
      rw [List.getElem?_append_right <| Nat.le_of_not_lt h]
      rw [List.getElem?_cons]
      split
      · case isTrue h' =>
        rw [h']
        simp
        let .list Alc' := Alc
        exact TypeVar_subst_in A₁st (Alc' _ <| List.mem_append.mpr <| .inr <| .head _) Δwf Bki
      · case isFalse h' =>
        let ⟨_, eq⟩ := Nat.exists_add_one_eq.mpr <| Nat.pos_of_ne_zero h'
        rw [← eq, List.getElem?_cons_succ]
        rfl
  · case listAppl A'st =>
    let .listApp A'lc _ := Alc
    exact .listApp (TypeVar_subst_in A'st A'lc Δwf Bki) .refl
  · case listAppr B'st =>
    let .listApp _ B'lc := Alc
    exact .listApp .refl <| TypeVar_subst_in B'st B'lc Δwf Bki
  · case prod A'st =>
    let .prod A'lc := Alc
    exact .prod <| TypeVar_subst_in A'st A'lc Δwf Bki
  · case sum A'st =>
    let .sum A'lc := Alc
    exact .sum <| TypeVar_subst_in A'st A'lc Δwf Bki
termination_by sizeOf A
decreasing_by
  all_goals (
    rename A = _ => eq
    cases eq
    simp_arith
  )
  exact Nat.le_of_lt <| Nat.lt_add_right _ <| List.sizeOf_lt_of_mem <| List.mem_append.mpr <|
    .inr <| .head _

theorem Type_open_in (Ast : [[Δ, a : K, Δ' ⊢ A^a -> A'^a]]) (Alc : A.TypeVarLocallyClosed 1)
  (Bki : [[Δ ⊢ B : K]]) (Δwf : [[⊢ Δ, a : K, Δ']]) (aninA : a ∉ A.freeTypeVars)
  (aninA' : a ∉ A'.freeTypeVars) : [[Δ, Δ'[B / a] ⊢ A^^B ->* A'^^B]] := by
  rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA,
      ← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA']
  let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
  rw [← Type.Type_open_var] at Alc'
  exact TypeVar_subst_in Ast Alc' Δwf Bki

theorem local_confluence (AstB₀ : [[Δ ⊢ A -> B₀]]) (AstB₁ : [[Δ ⊢ A -> B₁]]) (Aki : [[Δ ⊢ A : K]])
  (Δwf : [[⊢ Δ]]) : ∃ C, [[Δ ⊢ B₀ ->* C]] ∧ [[Δ ⊢ B₁ ->* C]] := by
  match AstB₀, AstB₁, Aki with
  | .eta .., .eta .., _ => exact of_eq
  | .eta B₀ki, .lam I B₀st (A' := B₀'), _ =>
    let ⟨a, anin⟩ := B₀.freeTypeVars ++ B₀'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninB₀B₀', aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninB₀, aninB₀'⟩ := List.not_mem_append'.mp aninB₀B₀'
    specialize B₀st a aninI
    simp [Type.TypeVar_open, B₀ki.TypeVarLocallyClosed_of.TypeVar_open_id] at B₀st
    generalize B₀''eq : B₀'.TypeVar_open a = B₀'' at B₀st
    match B₀st with
    | lamApp _ (.var .head) =>
      apply of_eq
      rw [← Type.Type_open_var] at B₀''eq
      rw [Type.freeTypeVars] at aninB₀
      cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninB₀' aninB₀ B₀''eq
      rfl
    | appl B₀st =>
      rename «Type» => B₀'''
      cases B₀'
      all_goals rw [Type.TypeVar_open] at B₀''eq
      case app B₀'''' B₀''''' =>
        cases B₀'''''
        all_goals rw [Type.TypeVar_open] at B₀''eq
        case var =>
          split at B₀''eq
          case isFalse h =>
            cases B₀''eq
            simp [Type.freeTypeVars] at aninB₀'
          case isTrue h =>
          cases h
          simp [Type.freeTypeVars] at aninB₀'
          cases B₀''eq
          let B₀''''lc := B₀st.preserve_lc B₀ki.TypeVarLocallyClosed_of
            |>.TypeVar_close_inc (a := a)
          rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninB₀'] at B₀''''lc
          replace B₀''''lc := B₀''''lc.not_mem_freeTypeVars_TypeVar_open_dec <|
            B₀st.preserve_not_mem_freeTypeVars aninB₀
          rw [B₀''''lc.TypeVar_open_id] at B₀st
          replace B₀st := B₀st.TypeVar_drop_of_not_mem_freeTypeVars aninB₀ (Δ' := .empty)
          rw [Environment.append] at B₀st
          exact ⟨B₀'''', B₀st, eta <| B₀st.preservation B₀ki⟩
        all_goals nomatch B₀''eq
      all_goals nomatch B₀''eq
  | .lamApp A'ki B'ki (A := A'), st, _ =>
    let .lam A'lc := A'ki.TypeVarLocallyClosed_of
    match st with
    | .appl A'st => match A'st with
      | .eta A'ki' =>
        simp [Type.Type_open, A'ki'.TypeVarLocallyClosed_of.Type_open_id]
        exact ⟨_, .refl⟩
      | .lam I A'st' (A' := A'') =>
        let ⟨a, anin⟩ := A'.freeTypeVars ++ A''.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
        let ⟨aninA'A''I, aninΔ⟩ := List.not_mem_append'.mp anin
        let ⟨aninA'A'', aninI⟩ := List.not_mem_append'.mp aninA'A''I
        let ⟨aninA', aninA''⟩ := List.not_mem_append'.mp aninA'A''
        exact ⟨
          _,
          Type_open_in (A'st' a aninI) A'lc B'ki (Δwf.typeVarExt aninΔ) aninA' aninA''
            (Δ' := .empty),
          .single <| lamApp (preservation (.lam I A'st') A'ki) B'ki
        ⟩
    | .appr B'st =>
      exact ⟨_, Type_open_out B'st A'lc B'ki Δwf, lamApp A'ki (B'st.preservation B'ki)⟩
    | .lamApp _ _ => exact of_eq
  | .listAppList A'ki (A := A') (n := n) (b := b) (K₂ := K₂) (B := B'), st, _ =>
    generalize Bseq : [:n].map _ = Bs, K'eq : Option.someIf .. = K' at st
    match st with
    | .listAppList A'ki' =>
      apply of_eq
      let lengths_eq : ([:n].map _).length = _ := by rw [Bseq]
      rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList,
          Nat.sub_zero, Nat.sub_zero] at lengths_eq
      cases lengths_eq
      cases A'ki.deterministic A'ki'
      cases Option.someIf_eq K'eq
      rw [Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        rw [Range.eq_of_mem_of_map_eq Bseq i mem]
      )]
    | .listAppId B'ki =>
      cases Bseq
      cases K'eq
      let .lam I aki := A'ki
      let ⟨a, anin⟩ := I.exists_fresh
      specialize aki a anin
      simp [Type.TypeVar_open] at aki
      let .var mem := aki
      cases mem
      case typeVarExt ne => nomatch ne
      let ⟨B'ki', _⟩ := B'ki.inv_list
      apply Exists.intro [[{</ B'@i // i in [:n] /> </ : K₂ // b />}]]
      constructor
      · apply MultiSmallStep.list
        intro i mem
        have : B' i = Type.Type_open (.var (.bound 0)) (B' i) := by rw [Type.Type_open, if_pos rfl]
        rw (occs := .pos [2]) [this]
        exact .single <| .lamApp .id <| B'ki' i mem
      · rfl
    | .listAppl A'st =>
      cases Bseq
      cases K'eq
      apply Exists.intro _
      constructor
      swap
      exact .single <| .listAppList <| A'st.preservation A'ki
      apply MultiSmallStep.list
      intro i mem
      exact .app A'st .refl
    | .listAppr B'st =>
      let .list B₁st (A₀ := B₀) (A₁ := B₁) (A₁' := B₁') (A₂ := B₂) (m := m) (n := n') := B'st
      apply Exists.intro [[{</ A' B₀@i // i in [:m] />, A' B₁', </ A' B₂@j // j in [:n'] /> </ : K₂ // b />}]]
      let lengths_eq := congrArg List.length Bseq
      simp [Range.length_toList] at lengths_eq
      rw [← Range.map_get!_eq (as := _ ++ _ :: _), List.length_append, List.length_map,
          Range.length_toList, Nat.sub_zero, List.length_cons, List.length_map, Range.length_toList,
          Nat.sub_zero, ← lengths_eq] at Bseq
      have map_map : ∀ {m n} {f : _ → _}, [m:n].map (fun i => A'.app (f i)) =
        List.map A'.app ([m:n].map fun i => f i) := by
        intros
        rw [Range.map, List.map_map, ← Range.map, ← Range.map,
            Range.map_eq_of_eq_of_mem'' (fun _ _ => Function.comp.eq_def _ _ _)]
      constructor
      · rw [Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          show _ = (([:m].map fun i => A'.app (B₀ i)) ++
            A'.app B₁ :: [:n'].map fun j => A'.app (B₂ j)).get! i
          rw [Range.eq_of_mem_of_map_eq Bseq i mem, map_map, map_map, ← List.map_cons,
              ← List.map_append]
          rw (occs := .pos [2]) [List.get!_eq_getElem!]
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem,
              Option.map, Option.getD, List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD,
              List.getElem?_eq_getElem, Option.getD]
          simp [Range.length_toList, ← lengths_eq, mem.upper]
        )]
        have : n = (([:m].map fun i => A'.app (B₀ i)) ++
            A'.app B₁ :: [:n'].map fun j => A'.app (B₂ j)).length := by
          simp [Range.length_toList, lengths_eq]
        rw (occs := .pos [1]) [this, Range.map_get!_eq]
        exact .single <| .list <| .appr B₁st
      · rw [← Range.map_get!_eq (as := _ ++ _ :: _), ← Range.map_get!_eq (as := _ ++ _ :: _),
            ← K'eq]
        convert Relation.ReflTransGen.single <| SmallStep.listAppList A'ki
        simp [Range.length_toList, lengths_eq]
        rw (occs := .pos [3]) [Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          rw [List.getElem?_eq_getElem (by rw [Range.length_toList]; exact mem.upper),
              Range.getElem_toList mem.upper, Option.map, Option.getD, Nat.zero_add]
        )]
        rw [map_map, map_map, map_map]
        have : m + (n' + 1) =
            (([:m].map fun i => B₀ i) ++ B₁' :: [:n'].map fun j => B₂ j).length := by
          simp [Range.length_toList, lengths_eq]
        rw (occs := .pos [1]) [this, Range.map_get!_eq]
        rw [← List.map_cons, List.map_append]
  | .listAppId B'ki (K := K), st, _ => match st with
    | .listAppList A'ki (B := B') (n := n) (b := b) =>
      let .lam I aki := A'ki
      let ⟨a, anin⟩ := I.exists_fresh
      specialize aki a anin
      simp [Type.TypeVar_open] at aki
      let .var mem := aki
      cases mem
      case typeVarExt ne => nomatch ne
      let ⟨B'ki', _⟩ := B'ki.inv_list
      apply Exists.intro [[{</ B'@i // i in [:n] /> </ : K // b />}]]
      constructor
      · rfl
      · apply MultiSmallStep.list
        intro i mem
        have : B' i = Type.Type_open (.var (.bound 0)) (B' i) := by rw [Type.Type_open, if_pos rfl]
        rw (occs := .pos [2]) [this]
        exact .single <| .lamApp .id <| B'ki' i mem
    | .listAppId .. => exact of_eq
    | .listAppComp _ A₁ki (A₁ := A₁) =>
      let .listApp A₁ki' _ := B'ki
      cases A₁ki.deterministic A₁ki'
      apply Exists.intro _
      apply And.intro .refl
      refine .listApp ?_ .refl
      apply Relation.ReflTransGen.trans (.single _) <| .single <| .eta A₁ki
      apply SmallStep.lam Δ.typeVarDom
      intro a anin
      simp [Type.TypeVar_open, A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      have : [[(A₁ a)]] = Type.Type_open [[(a$0)]] [[(A₁ a)]] := by rw [Type.Type_open, if_pos rfl]
      rw (occs := .pos [2]) [this]
      exact .lamApp .id <|
        .app (A₁ki.weakening_r (fun | _, .head _ => anin) (Δ' := .typeExt .empty a _)) <|
        .var <| .head
    | .listAppl A'st => nomatch Type.IsValue.id.not_step A'st
    | .listAppr B'st => exact ⟨_, .single B'st, .single <| .listAppId <| B'st.preservation B'ki⟩
  | .listAppComp A₀lc A₁ki (A₀ := A₀) (A₁ := A₁) (B := B') (K₁ := K₁) (K₂ := K₂), st,
    .listApp A₀ki (.listApp A₁ki' B'ki) (K₂ := K₃) =>
    cases A₁ki.deterministic A₁ki'
    match st with
    | .listAppId A₁B'ki =>
      let .listApp A₁ki' _ := A₁B'ki
      cases A₁ki.deterministic A₁ki'
      apply Exists.intro _
      apply And.intro _ .refl
      refine .listApp ?_ .refl
      apply Relation.ReflTransGen.trans (.single _) <| .single <| .eta A₁ki
      apply SmallStep.lam Δ.typeVarDom
      intro a anin
      simp [Type.TypeVar_open, A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      have : [[(A₁ a)]] = Type.Type_open [[(a$0)]] [[(A₁ a)]] := by rw [Type.Type_open, if_pos rfl]
      rw (occs := .pos [2]) [this]
      exact .lamApp .id <|
        .app (A₁ki.weakening_r (fun | _, .head _ => anin) (Δ' := .typeExt .empty a _)) <|
        .var <| .head
    | .listAppComp _ A₁ki' =>
      cases A₁ki.deterministic A₁ki'
      exact of_eq
    | .listAppl A₀st (A' := A₀') =>
      apply Exists.intro [[(λ a : K₁. A₀' (A₁ a$0)) ⟦B'⟧]]
      constructor
      · refine .listApp ?_ .refl
        apply MultiSmallStep.lam Δ.typeVarDom <|
          A₀lc.weaken (n := 1).app <| A₁ki.TypeVarLocallyClosed_of.weaken (n := 1).app <|
          .var_bound Nat.one_pos
        intro a anin
        simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₀st.preserve_lc A₀lc |>.TypeVar_open_id,
              A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        refine .app ?_ .refl
        exact .single <| A₀st.weakening (Δwf.typeVarExt anin) (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
      · exact .single <| listAppComp (A₀st.preserve_lc A₀lc) A₁ki
    | .listAppr A₁B'st => match A₁B'st with
      | .listAppList A₁ki'' (B := B') (n := n) (b := b) =>
        cases A₁ki.deterministic A₁ki''
        apply Exists.intro [[{</ A₀ (A₁ B'@i) // i in [:n] /> </ : K₃ // b />}]]
        constructor
        · calc
            [[Δ ⊢ (λ a : K₁. A₀ (A₁ a$0)) ⟦{</ B'@i // i in [:n] /> </ : K₁ // b />}⟧ ->* {</ (λ a : K₁. A₀ (A₁ a$0)) B'@i // i in [:n] /> </ : K₃ // b />}]] := by
              refine .single <| .listAppList ?_
              apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id,
                    A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₁)
              exact A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| .var .head
            [[Δ ⊢ {</ (λ a : K₁. A₀ (A₁ a$0)) B'@i // i in [:n] /> </ : K₃ // b />} ->* {</ A₀ (A₁ B'@i) // i in [:n] /> </ : K₃ // b />}]] := by
              refine .list ?_
              intro i mem
              have : [[(A₀ (A₁ (B'@i)))]] = [[((A₀ (A₁ a$0))^^B'@i)]] := by
                simp [Type.Type_open, A₀lc.Type_open_id,
                      A₁ki.TypeVarLocallyClosed_of.Type_open_id]
              rw [this]
              refine .single <| .lamApp ?_ (B'ki.inv_list.left i mem) (K₂ := K₃)
              apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id,
                    A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₁)
              exact A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| .var .head
        · exact .single <| .listAppList A₀ki
      | .listAppId B'ki (A := B') (K := K) =>
        let .lam I aki := A₁ki
        let ⟨a, anin⟩ := I.exists_fresh
        specialize aki a anin
        simp [Type.TypeVar_open] at aki
        let .var mem := aki
        cases mem
        case typeVarExt ne => nomatch ne
        apply Exists.intro [[A₀ ⟦B'⟧]]
        constructor
        · calc
            [[Δ ⊢ (λ a : K₂. A₀ ((λ a : K₂. a$0) a$0)) ⟦B'⟧ ->* (λ a : K₂. A₀ a$0) ⟦B'⟧]] := by
              refine .listApp ?_ .refl
              apply MultiSmallStep.lam [] <|
                A₀lc.weaken (n := 1).app <| .app (.weaken .id) <| .var_bound Nat.one_pos
              intro a _
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id]
              refine .app .refl ?_
              have : Type.var (.free a) = Type.Type_open (.var (.bound 0)) (.var (.free a)) := by
                rw [Type.Type_open, if_pos rfl]
              rw (occs := .pos [2]) [this]
              exact .single <| .lamApp .id <| .var .head
            [[Δ ⊢ (λ a : K₂. A₀ a$0) ⟦B'⟧ ->* A₀ ⟦B'⟧]] := .listApp (.single <| eta A₀ki) .refl
        · rfl
      | .listAppComp _ B₀ki (A₁ := B₀) (B := B₁) (K₁ := K₀) =>
        let .listApp B₀ki' B₁ki := B'ki
        cases B₀ki.deterministic B₀ki'
        let A₁lc := A₁ki.TypeVarLocallyClosed_of
        let B₀lc := B₀ki.TypeVarLocallyClosed_of
        apply Exists.intro [[(λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]]
        constructor
        · calc
            [[Δ ⊢ (λ a : K₁. A₀ (A₁ a$0)) ⟦B₀ ⟦B₁⟧⟧ ->* (λ a : K₀. (λ a : K₁. A₀ (A₁ a$0)) (B₀ a$0)) ⟦B₁⟧]] :=
              .single <| .listAppComp
                (.lam (.app A₀lc.weaken (.app A₁lc.weaken
                  (.var_bound Nat.one_pos))))
                B₀ki
            [[Δ ⊢ (λ a : K₀. (λ a : K₁. A₀ (A₁ a$0)) (B₀ a$0)) ⟦B₁⟧ ->* (λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]] := by
              refine .listApp ?_ .refl
              refine .lam Δ.typeVarDom ?_ ?_
              · exact .app
                  (.lam (.app
                    (A₀lc.weaken (n := 2))
                    (.app (A₁lc.weaken (n := 2)) (.var_bound Nat.two_pos))))
                  (.app (B₀ki.TypeVarLocallyClosed_of.weaken (n := 1)) (.var_bound Nat.one_pos))
              · intro a anin
                let Δawf := Δwf.typeVarExt anin (K := K₀)
                simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₀lc.weaken (n := 1).TypeVar_open_id,
                      A₁lc.TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
                      B₀lc.TypeVar_open_id]
                have : [[(A₀ (A₁ (B₀ a)))]] = [[((A₀ (A₁ a$0))^^(B₀ a))]] := by
                  simp [Type.Type_open, A₀lc.Type_open_id, A₁lc.Type_open_id]
                rw [this]
                refine .single ?_
                apply SmallStep.lamApp
                · apply Kinding.lam <| a :: Δ.typeVarDom
                  intro a' a'nin
                  let Δaa'wf := Δawf.typeVarExt a'nin (K := K₁)
                  simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
                  exact A₀ki.weakening Δaa'wf (Δ' := .typeExt (.typeExt .empty ..) ..)
                    (Δ'' := .empty) |>.app <| A₁ki.weakening Δaa'wf
                      (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty) |>.app <| .var .head
                · exact B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty) |>.app <|
                    .var .head
        · calc
            [[Δ ⊢ A₀ ⟦(λ a : K₀. A₁ (B₀ a$0)) ⟦B₁⟧⟧ ->* (λ a : K₀. A₀ ((λ a : K₀. A₁ (B₀ a$0)) a$0)) ⟦B₁⟧]] := by
              refine .single <| .listAppComp A₀lc ?_ (K₂ := K₂)
              apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              exact A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty) |>.app <|
                B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty) |>.app <| .var .head
            [[Δ ⊢ (λ a : K₀. A₀ ((λ a : K₀. A₁ (B₀ a$0)) a$0)) ⟦B₁⟧ ->* (λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]] := by
              refine .listApp ?_ .refl
              refine .lam Δ.typeVarDom ?_ ?_
              · exact .app (A₀lc.weaken (n := 1)) <|
                  .app
                    (.lam (.app (A₁lc.weaken (n := 2))
                      (.app (B₀lc.weaken (n := 2)) (.var_bound Nat.two_pos)))) <|
                    .var_bound Nat.one_pos
              · intro a anin
                let Δawf := Δwf.typeVarExt anin (K := K₀)
                simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                      A₁lc.weaken (n := 1).TypeVar_open_id, B₀lc.TypeVar_open_id,
                      B₀lc.weaken (n := 1).TypeVar_open_id]
                refine .app .refl ?_
                have : [[A₁ (B₀ a)]] = [[((A₁ (B₀ a$0))^^a)]] := by
                  simp [Type.Type_open, A₁lc.Type_open_id, B₀lc.Type_open_id]
                rw [this]
                refine .single ?_
                apply SmallStep.lamApp _ <| .var .head
                swap
                apply Kinding.lam <| a :: Δ.typeVarDom
                intro a' a'nin
                let Δaa'wf := Δawf.typeVarExt a'nin (K := K₀)
                simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
                exact A₁ki.weakening Δaa'wf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty)
                  |>.app <| B₀ki.weakening Δaa'wf (Δ' := .typeExt (.typeExt .empty ..) ..)
                    (Δ'' := .empty) |>.app <| .var .head
      | .listAppl A₁st (A' := A₁') =>
        apply Exists.intro [[(λ a : K₁. A₀ (A₁' a$0)) ⟦B'⟧]]
        let A₁lc := A₁ki.TypeVarLocallyClosed_of
        constructor
        · refine .listApp ?_ .refl
          refine .lam Δ.typeVarDom ?_ ?_
          · exact A₀lc.weaken (n := 1).app <| A₁lc.weaken (n := 1).app <| .var_bound Nat.one_pos
          · intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                  A₁st.preserve_lc A₁lc |>.TypeVar_open_id]
            refine .app .refl <| .app (.single ?_) .refl
            exact A₁st.weakening (Δwf.typeVarExt anin) (Δ' := .typeExt .empty ..) (Δ'' := .empty)
        · exact .single <| .listAppComp A₀lc <| A₁st.preservation A₁ki
      | .listAppr B'st (B' := B'') =>
        apply Exists.intro [[(λ a : K₁. A₀ (A₁ a$0)) ⟦B''⟧]]
        constructor
        · exact .listApp .refl <| .single B'st
        · exact .single <| .listAppComp A₀lc A₁ki
  | .lam I B₁st (A' := B₁'), .eta B₁ki, _ =>
    let ⟨a, anin⟩ := B₁.freeTypeVars ++ B₁'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninB₁B₁', aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninB₁, aninB₁'⟩ := List.not_mem_append'.mp aninB₁B₁'
    specialize B₁st a aninI
    simp [Type.TypeVar_open, B₁ki.TypeVarLocallyClosed_of.TypeVar_open_id] at B₁st
    generalize B₁''eq : B₁'.TypeVar_open a = B₁'' at B₁st
    match B₁st with
    | lamApp _ (.var .head) =>
      apply of_eq
      rw [← Type.Type_open_var] at B₁''eq
      rw [Type.freeTypeVars] at aninB₁
      cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninB₁' aninB₁ B₁''eq
      rfl
    | appl B₁st =>
      rename «Type» => B₁'''
      cases B₁'
      all_goals rw [Type.TypeVar_open] at B₁''eq
      case app B₁'''' B₁''''' =>
        cases B₁'''''
        all_goals rw [Type.TypeVar_open] at B₁''eq
        case var =>
          split at B₁''eq
          case isFalse h =>
            cases B₁''eq
            simp [Type.freeTypeVars] at aninB₁'
          case isTrue h =>
          cases h
          simp [Type.freeTypeVars] at aninB₁'
          cases B₁''eq
          let B₁''''lc := B₁st.preserve_lc B₁ki.TypeVarLocallyClosed_of
            |>.TypeVar_close_inc (a := a)
          rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninB₁'] at B₁''''lc
          replace B₁''''lc := B₁''''lc.not_mem_freeTypeVars_TypeVar_open_dec <|
            B₁st.preserve_not_mem_freeTypeVars aninB₁
          rw [B₁''''lc.TypeVar_open_id] at B₁st
          replace B₁st := B₁st.TypeVar_drop_of_not_mem_freeTypeVars aninB₁ (Δ' := .empty)
          rw [Environment.append] at B₁st
          exact ⟨B₁'''', eta <| B₁st.preservation B₁ki, B₁st⟩
        all_goals nomatch B₁''eq
      all_goals nomatch B₁''eq
  | .lam I A'st, .lam I' A''st, .lam I'' A'''ki =>
    rename_i A' A'' _
    let ⟨a, anin⟩ := A'.freeTypeVars ++ A''.freeTypeVars ++ I ++ I' ++ I'' ++ Δ.typeVarDom
      |>.exists_fresh
    let ⟨aninA'A''II'I'', aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA'A''II', aninI''⟩ := List.not_mem_append'.mp aninA'A''II'I''
    let ⟨aninA'A''I, aninI'⟩ := List.not_mem_append'.mp aninA'A''II'
    let ⟨aninA'A'', aninI⟩ := List.not_mem_append'.mp aninA'A''I
    let ⟨aninA', aninA''⟩ := List.not_mem_append'.mp aninA'A''
    specialize A'st a aninI
    specialize A''st a aninI'
    specialize A'''ki a aninI''
    let A'''lc' := A'''ki.TypeVarLocallyClosed_of
    let ⟨C, A'mst, A''mst⟩ := A'st.local_confluence A''st A'''ki <| Δwf.typeVarExt aninΔ
    let A'lc := A'st.preserve_lc A'''lc' |>.TypeVar_close_inc (a := a)
    let A''lc := A''st.preserve_lc A'''lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A''lc
    refine ⟨
      _,
      .lam Δ.typeVarDom A'lc fun _ a'nin => A'mst.TypeVar_open_swap A'lc aninA' a'nin,
      .lam Δ.typeVarDom A''lc fun _ a'nin => A''mst.TypeVar_open_swap A''lc aninA'' a'nin
    ⟩
  | .appl A'st, st, .app A'ki _ => match st with
    | .appl A'st' =>
      let ⟨_, A'mst, A'mst'⟩ := A'st.local_confluence A'st' A'ki Δwf
      exact ⟨_, .app A'mst .refl, .app A'mst' .refl⟩
    | .appr B'st => exact ⟨_, .app .refl <| .single B'st, .app (.single A'st) .refl⟩
    | .lamApp A'ki B'ki => match A'st, A'ki with
      | .eta A'ki, _ =>
        simp [Type.Type_open, A'ki.TypeVarLocallyClosed_of.Type_open_id]
        exact ⟨_, .refl⟩
      | .lam I A'st' (A := A'') (A' := A'''), .lam I' A'ki' =>
        let ⟨a, anin⟩ := A''.freeTypeVars ++ A'''.freeTypeVars ++ I ++ I' ++ Δ.typeVarDom
          |>.exists_fresh
        let ⟨aninA''A'''II', aninΔ⟩ := List.not_mem_append'.mp anin
        let ⟨aninA''A'''I, aninI'⟩ := List.not_mem_append'.mp aninA''A'''II'
        let ⟨aninA''A''', aninI⟩ := List.not_mem_append'.mp aninA''A'''I
        let ⟨aninA'', aninA'''⟩ := List.not_mem_append'.mp aninA''A'''
        let A'lc' := A'ki' a aninI' |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
        rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A'lc'
        exact ⟨
          _,
          .single <| .lamApp (preservation (.lam I A'st') (.lam I' A'ki')) B'ki,
          Type_open_in (A'st' a aninI) A'lc' B'ki (Δwf.typeVarExt aninΔ) aninA'' aninA'''
            (Δ' := .empty)
        ⟩
  | .appr B'st, st, .app A'ki B'ki => match st with
    | .appl A'st => exact ⟨_, .app (.single A'st) .refl, .app .refl <| .single B'st⟩
    | .appr B'st' =>
      let ⟨_, B'mst, B'mst'⟩ := B'st.local_confluence B'st' B'ki Δwf
      exact ⟨_, .app .refl B'mst, .app .refl B'mst'⟩
    | .lamApp A'ki B'ki (A := A') =>
      let .lam I A'ki' := A'ki
      let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
      let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
      let A'lc' := A'ki' a aninI |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
      rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc'
      exact ⟨
        _,
        .single <| .lamApp A'ki <| B'st.preservation B'ki,
        Type_open_out B'st A'lc' B'ki Δwf
      ⟩
  | .forall I A'st, .forall I' A''st, .scheme I'' A'''ki =>
    rename_i A' A''
    let ⟨a, anin⟩ := A'.freeTypeVars ++ A''.freeTypeVars ++ I ++ I' ++ I'' ++ Δ.typeVarDom
      |>.exists_fresh
    let ⟨aninA'A''II'I'', aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA'A''II', aninI''⟩ := List.not_mem_append'.mp aninA'A''II'I''
    let ⟨aninA'A''I, aninI'⟩ := List.not_mem_append'.mp aninA'A''II'
    let ⟨aninA'A'', aninI⟩ := List.not_mem_append'.mp aninA'A''I
    let ⟨aninA', aninA''⟩ := List.not_mem_append'.mp aninA'A''
    specialize A'st a aninI
    specialize A''st a aninI'
    specialize A'''ki a aninI''
    let A'''lc' := A'''ki.TypeVarLocallyClosed_of
    let ⟨C, A'mst, A''mst⟩ := A'st.local_confluence A''st A'''ki <| Δwf.typeVarExt aninΔ
    let A'lc := A'st.preserve_lc A'''lc' |>.TypeVar_close_inc (a := a)
    let A''lc := A''st.preserve_lc A'''lc' |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA''] at A''lc
    refine ⟨
      _,
      .forall Δ.typeVarDom A'lc fun _ a'nin => A'mst.TypeVar_open_swap A'lc aninA' a'nin,
      .forall Δ.typeVarDom A''lc fun _ a'nin => A''mst.TypeVar_open_swap A''lc aninA'' a'nin
    ⟩
  | .arrl A'st, st, .arr A'lc _ => match st with
    | .arrl A'st' =>
      let ⟨_, A'mst, A'mst'⟩ := A'st.local_confluence A'st' A'lc Δwf
      exact ⟨_, .arr A'mst .refl, .arr A'mst' .refl⟩
    | .arrr B'st => exact ⟨_, .single <| arrr B'st, .single <| arrl A'st⟩
  | .arrr B'st, st, .arr _ B'lc => match st with
    | .arrl A'st => exact ⟨_, .single <| arrl A'st, .single <| arrr B'st⟩
    | .arrr B'st' =>
      let ⟨_, B'mst, B'mst'⟩ := B'st.local_confluence B'st' B'lc Δwf
      exact ⟨_, .arr .refl B'mst, .arr .refl B'mst'⟩
  | .list A₁st (m := m) (n := n) (A₀ := A₀) (A₁ := A₁) (A₁' := A₁') (A₂ := A₂) (K := K) (b := b),
    st, Aki =>
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki
    rcases Aki.inv_list' with ⟨_, rfl, Aki', h⟩
    generalize A'seq : _ ++ _ :: _ = A's, K'eq : Option.someIf .. = K' at st
    let .list A₁st' (m := m') (n := n') (A₁' := A₁'') := st
    match Nat.lt_trichotomy m m' with
    | .inl mltm' =>
      rcases List.of_length_lt_of_append_eq_append (by simp [Range.length_toList, mltm']) A'seq with
        ⟨_, A₃, A₀eq, A₁A₂eq⟩
      rcases List.cons.inj A₁A₂eq with ⟨rfl, A₂eq⟩
      let m'eq := congrArg List.length A₀eq
      let neq := congrArg List.length A₂eq
      simp_arith [Range.length_toList] at m'eq neq
      rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc] at neq
      let m'le := Nat.le_of_eq m'eq.symm
      rw [Nat.add_assoc, Nat.add_comm] at m'le
      apply Nat.le_of_add_right_le at m'le
      let nle := Nat.le_of_add_right_le <| Nat.le_of_eq neq.symm
      let A₂eq' := A₂eq
      rw [Range.map, ← Range.map_append (Nat.zero_le _) nle, ← Range.map, ← Range.map,
          ← List.singleton_append, List.append_eq, ← List.append_assoc] at A₂eq'
      let ⟨A₂eq₀, A₂eq₁⟩ := List.of_length_eq_of_append_eq_append (by simp [Range.length_toList])
        A₂eq'
      rw [neq] at A₂eq₁
      apply Exists.intro [[{</ A₀@i // i in [:m] />, A₁', </ A₃.get!@k // k in [:A₃.length] />, A₁'', </ A₂@j // j in [m' - m:n] /> </ : K // b />}]]
      constructor
      · rw [← K'eq, A₂eq, Range.map_get!_eq, List.append_eq, ← List.cons_append,
            ← List.append_assoc, ← List.cons_append, ← List.append_assoc, m'eq, neq,
            Nat.sub_add_comm (Nat.le_add_right ..), Nat.sub_add_comm Nat.le.refl, Nat.sub_self,
            Nat.zero_add, A₂eq₁]
        rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        rw (occs := .pos [5]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        exact .single <| .list A₁st'
      · rw [← K'eq, A₀eq, Range.map_get!_eq, List.append_assoc, List.cons_append, m'eq, neq,
            Nat.sub_add_comm (Nat.le_add_right ..), Nat.sub_add_comm Nat.le.refl, Nat.sub_self,
            Nat.zero_add, A₂eq₁]
        rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        rw (occs := .pos [5]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        exact .single <| .list A₁st
    | .inr (.inl meqm') =>
      cases meqm'
      let lengths_eq := congrArg List.length A'seq
      simp [Range.length_toList] at lengths_eq
      cases lengths_eq
      let ⟨A₀seq, A₁A₂seq⟩ := List.of_length_eq_of_append_eq_append (by simp [Range.length_toList])
        A'seq
      rcases List.cons.inj A₁A₂seq with ⟨rfl, A₂seq⟩
      specialize Aki' m
      simp [Range.length_toList] at Aki'
      specialize Aki' ⟨Nat.zero_le _, Nat.lt_add_of_pos_right (Nat.succ_pos _), Nat.mod_one _⟩
      rw [List.getElem_append_right (by simp [Range.length_toList])] at Aki'
      simp [Range.length_toList] at Aki'
      let ⟨A₁''', A₁'mst, A₁''mst⟩ := A₁st.local_confluence A₁st' Aki' Δwf
      apply Exists.intro [[{</ A₀@i // i in [:m] />, A₁''', </ A₂@j // j in [:n] /> </ : K // b />}]]
      constructor
      · rw [← K'eq]
        exact .list' A₁'mst
      · rw [← A₀seq, ← A₂seq, ← K'eq]
        exact .list' A₁''mst
    | .inr (.inr m'ltm) =>
      rcases List.of_length_lt_of_append_eq_append (by simp [Range.length_toList, m'ltm]) A'seq.symm
        with ⟨_, A₃, A₀eq, A₁A₂eq⟩
      rcases List.cons.inj A₁A₂eq with ⟨rfl, A₂eq⟩
      rw [List.append_eq] at A₂eq
      let meq := congrArg List.length A₀eq
      let n'eq := congrArg List.length A₂eq
      simp_arith [Range.length_toList] at meq n'eq
      rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc] at n'eq
      let mle := Nat.le_of_eq meq.symm
      rw [Nat.add_assoc] at mle
      let mle' := Nat.le_of_add_right_le mle
      rw [Nat.add_comm] at mle
      apply Nat.le_of_add_right_le at mle
      let n'le := Nat.le_of_add_right_le <| Nat.le_of_eq n'eq.symm
      let A₀eq' := A₀eq
      let A₂eq' := A₂eq
      rw [Range.map, ← Range.map_append (Nat.zero_le _) mle', ← Range.map, ← Range.map] at A₀eq'
      rw [Range.map, ← Range.map_append (Nat.zero_le _) n'le, ← Range.map, ← Range.map,
          ← List.singleton_append, ← List.append_assoc] at A₂eq'
      let ⟨A₀eq₀, A₀eq₁⟩ := List.of_length_eq_of_append_eq_append (by simp [Range.length_toList])
        A₀eq'
      let ⟨A₂eq₀, A₂eq₁⟩ := List.of_length_eq_of_append_eq_append (by simp [Range.length_toList])
        A₂eq'
      rw [n'eq] at A₂eq₁
      apply Exists.intro [[{</ A₀@i // i in [:m'] />, A₁'', </ A₃.get!@k // k in [:A₃.length] />, A₁', </ A₂@j // j in [:n] /> </ : K // b />}]]
      constructor
      · rw [← K'eq, A₀eq, Range.map_get!_eq, List.append_assoc, List.cons_append, ← A₀eq₀]
        rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        rw (occs := .pos [5]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        exact .single <| .list A₁st'
      · rw [← K'eq, A₂eq, Range.map_get!_eq, ← List.cons_append, ← List.cons_append,
            ← List.append_assoc, ← List.append_assoc, ← A₀eq₀]
        rw (occs := .pos [2]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        rw (occs := .pos [5]) [← Range.map_get!_eq (as := _ ++ _ :: _)]
        exact .single <| .list A₁st
  | .listAppl A'st (A' := A''), st, .listApp A'ki _ => match st with
    | .listAppList A'ki =>
      apply Exists.intro _
      constructor
      exact .single <| .listAppList <| A'st.preservation A'ki
      apply MultiSmallStep.list
      intro i mem
      exact .app A'st .refl
    | .listAppId _ => nomatch Type.IsValue.id.not_step A'st
    | .listAppComp A₀lc A₁ki (A₁ := A₁) (B := B') (K₁ := K₁) =>
      rename' A'' => A₀'
      rename' A'st => A₀st
      apply Exists.intro [[(λ a : K₁. A₀' (A₁ a$0)) ⟦B'⟧]]
      constructor
      · exact .single <| listAppComp (A₀st.preserve_lc A₀lc) A₁ki
      · refine .listApp ?_ .refl
        apply MultiSmallStep.lam Δ.typeVarDom <|
          A₀lc.weaken (n := 1).app <| A₁ki.TypeVarLocallyClosed_of.weaken (n := 1).app <|
          .var_bound Nat.one_pos
        intro a anin
        simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₀st.preserve_lc A₀lc |>.TypeVar_open_id,
              A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        refine .app ?_ .refl
        exact .single <| A₀st.weakening (Δwf.typeVarExt anin) (Δ' := .typeExt .empty ..)
          (Δ'' := .empty)
    | .listAppl A'st' =>
      let ⟨_, A'mst, A'mst'⟩ := A'st.local_confluence A'st' A'ki Δwf
      exact ⟨_, .listApp A'mst .refl, .listApp A'mst' .refl⟩
    | .listAppr B'st => exact ⟨_, .listApp .refl (.single B'st), .listApp (.single A'st) .refl⟩
  | .listAppr B'st, st, .listApp A'ki B'ki (K₁ := K₂) (K₂ := K₃) => match st with
    | .listAppList A'ki (A := A') (n := n) (b := b) (K₂ := K₂) (B := B') =>
      generalize Bseq : [:n].map _ = Bs, K'eq : Option.someIf .. = K' at B'st
      let .list B₁st (A₀ := B₀) (A₁ := B₁) (A₁' := B₁') (A₂ := B₂) (m := m) (n := n') := B'st
      apply Exists.intro [[{</ A' B₀@i // i in [:m] />, A' B₁', </ A' B₂@j // j in [:n'] /> </ : K₂ // b />}]]
      let lengths_eq := congrArg List.length Bseq
      simp [Range.length_toList] at lengths_eq
      rw [← Range.map_get!_eq (as := _ ++ _ :: _), List.length_append, List.length_map,
          Range.length_toList, Nat.sub_zero, List.length_cons, List.length_map, Range.length_toList,
          Nat.sub_zero, ← lengths_eq] at Bseq
      have map_map : ∀ {m n} {f : _ → _}, [m:n].map (fun i => A'.app (f i)) =
        List.map A'.app ([m:n].map fun i => f i) := by
        intros
        rw [Range.map, List.map_map, ← Range.map, ← Range.map,
            Range.map_eq_of_eq_of_mem'' (fun _ _ => Function.comp.eq_def _ _ _)]
      constructor
      · rw [← Range.map_get!_eq (as := _ ++ _ :: _), ← Range.map_get!_eq (as := _ ++ _ :: _),
            ← K'eq]
        convert Relation.ReflTransGen.single <| SmallStep.listAppList A'ki
        simp [Range.length_toList, lengths_eq]
        rw (occs := .pos [3]) [Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          rw [List.getElem?_eq_getElem (by rw [Range.length_toList]; exact mem.upper),
              Range.getElem_toList mem.upper, Option.map, Option.getD, Nat.zero_add]
        )]
        rw [map_map, map_map, map_map]
        have : m + (n' + 1) =
            (([:m].map fun i => B₀ i) ++ B₁' :: [:n'].map fun j => B₂ j).length := by
          simp [Range.length_toList, lengths_eq]
        rw (occs := .pos [1]) [this, Range.map_get!_eq]
        rw [← List.map_cons, List.map_append]
      · rw [Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          show _ = (([:m].map fun i => A'.app (B₀ i)) ++
            A'.app B₁ :: [:n'].map fun j => A'.app (B₂ j)).get! i
          rw [Range.eq_of_mem_of_map_eq Bseq i mem, map_map, map_map, ← List.map_cons,
              ← List.map_append]
          rw (occs := .pos [2]) [List.get!_eq_getElem!]
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem,
              Option.map, Option.getD, List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD,
              List.getElem?_eq_getElem, Option.getD]
          simp [Range.length_toList, ← lengths_eq, mem.upper]
        )]
        have : n = (([:m].map fun i => A'.app (B₀ i)) ++
            A'.app B₁ :: [:n'].map fun j => A'.app (B₂ j)).length := by
          simp [Range.length_toList, lengths_eq]
        rw (occs := .pos [1]) [this, Range.map_get!_eq]
        exact .single <| .list <| .appr B₁st
    | .listAppId B'ki => exact ⟨_, .single <| .listAppId <| B'st.preservation B'ki, .single B'st⟩
    | .listAppComp A₀lc A₁ki (A₀ := A₀) (A₁ := A₁) (B := B') (K₁ := K₁) (K₂ := K₂) =>
      rename' A'ki => A₀ki
      rename' B'st => A₁B'st
      let .listApp A₁ki' B'ki := B'ki
      cases A₁ki.deterministic A₁ki'
      match A₁B'st with
      | .listAppList A₁ki'' (B := B') (n := n) (b := b) =>
        cases A₁ki.deterministic A₁ki''
        apply Exists.intro [[{</ A₀ (A₁ B'@i) // i in [:n] /> </ : K₃ // b />}]]
        constructor
        · exact .single <| .listAppList A₀ki
        · calc
            [[Δ ⊢ (λ a : K₁. A₀ (A₁ a$0)) ⟦{</ B'@i // i in [:n] /> </ : K₁ // b />}⟧ ->* {</ (λ a : K₁. A₀ (A₁ a$0)) B'@i // i in [:n] /> </ : K₃ // b />}]] := by
              refine .single <| .listAppList ?_
              apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id,
                    A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₁)
              exact A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| .var .head
            [[Δ ⊢ {</ (λ a : K₁. A₀ (A₁ a$0)) B'@i // i in [:n] /> </ : K₃ // b />} ->* {</ A₀ (A₁ B'@i) // i in [:n] /> </ : K₃ // b />}]] := by
              refine .list ?_
              intro i mem
              have : [[(A₀ (A₁ (B'@i)))]] = [[((A₀ (A₁ a$0))^^B'@i)]] := by
                simp [Type.Type_open, A₀lc.Type_open_id,
                      A₁ki.TypeVarLocallyClosed_of.Type_open_id]
              rw [this]
              refine .single <| .lamApp ?_ (B'ki.inv_list.left i mem) (K₂ := K₃)
              apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id,
                    A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₁)
              exact A₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
                |>.app <| .var .head
      | .listAppId B'ki (A := B') (K := K) =>
        let .lam I aki := A₁ki
        let ⟨a, anin⟩ := I.exists_fresh
        specialize aki a anin
        simp [Type.TypeVar_open] at aki
        let .var mem := aki
        cases mem
        case typeVarExt ne => nomatch ne
        apply Exists.intro [[A₀ ⟦B'⟧]]
        constructor
        · rfl
        · calc
            [[Δ ⊢ (λ a : K₂. A₀ ((λ a : K₂. a$0) a$0)) ⟦B'⟧ ->* (λ a : K₂. A₀ a$0) ⟦B'⟧]] := by
              refine .listApp ?_ .refl
              apply MultiSmallStep.lam [] <|
                A₀lc.weaken (n := 1).app <| .app (.weaken .id) <| .var_bound Nat.one_pos
              intro a _
              simp [Type.TypeVar_open, A₀lc.TypeVar_open_id]
              refine .app .refl ?_
              have : Type.var (.free a) = Type.Type_open (.var (.bound 0)) (.var (.free a)) := by
                rw [Type.Type_open, if_pos rfl]
              rw (occs := .pos [2]) [this]
              exact .single <| .lamApp .id <| .var .head
            [[Δ ⊢ (λ a : K₂. A₀ a$0) ⟦B'⟧ ->* A₀ ⟦B'⟧]] := .listApp (.single <| eta A₀ki) .refl
      | .listAppComp _ B₀ki (A₁ := B₀) (B := B₁) (K₁ := K₀) =>
        let .listApp B₀ki' B₁ki := B'ki
        cases B₀ki.deterministic B₀ki'
        let A₁lc := A₁ki.TypeVarLocallyClosed_of
        let B₀lc := B₀ki.TypeVarLocallyClosed_of
        apply Exists.intro [[(λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]]
        constructor
        · calc
            [[Δ ⊢ A₀ ⟦(λ a : K₀. A₁ (B₀ a$0)) ⟦B₁⟧⟧ ->* (λ a : K₀. A₀ ((λ a : K₀. A₁ (B₀ a$0)) a$0)) ⟦B₁⟧]] := by
              refine .single <| .listAppComp A₀lc ?_ (K₂ := K₂)
              apply Kinding.lam Δ.typeVarDom
              intro a anin
              simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
              let Δawf := Δwf.typeVarExt anin (K := K₀)
              exact A₁ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty) |>.app <|
                B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty) |>.app <| .var .head
            [[Δ ⊢ (λ a : K₀. A₀ ((λ a : K₀. A₁ (B₀ a$0)) a$0)) ⟦B₁⟧ ->* (λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]] := by
              refine .listApp ?_ .refl
              refine .lam Δ.typeVarDom ?_ ?_
              · exact .app (A₀lc.weaken (n := 1)) <|
                  .app
                    (.lam (.app (A₁lc.weaken (n := 2))
                      (.app (B₀lc.weaken (n := 2)) (.var_bound Nat.two_pos)))) <|
                    .var_bound Nat.one_pos
              · intro a anin
                let Δawf := Δwf.typeVarExt anin (K := K₀)
                simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                      A₁lc.weaken (n := 1).TypeVar_open_id, B₀lc.TypeVar_open_id,
                      B₀lc.weaken (n := 1).TypeVar_open_id]
                refine .app .refl ?_
                have : [[A₁ (B₀ a)]] = [[((A₁ (B₀ a$0))^^a)]] := by
                  simp [Type.Type_open, A₁lc.Type_open_id, B₀lc.Type_open_id]
                rw [this]
                refine .single ?_
                apply SmallStep.lamApp _ <| .var .head
                swap
                apply Kinding.lam <| a :: Δ.typeVarDom
                intro a' a'nin
                let Δaa'wf := Δawf.typeVarExt a'nin (K := K₀)
                simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
                exact A₁ki.weakening Δaa'wf (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty)
                  |>.app <| B₀ki.weakening Δaa'wf (Δ' := .typeExt (.typeExt .empty ..) ..)
                    (Δ'' := .empty) |>.app <| .var .head
        · calc
            [[Δ ⊢ (λ a : K₁. A₀ (A₁ a$0)) ⟦B₀ ⟦B₁⟧⟧ ->* (λ a : K₀. (λ a : K₁. A₀ (A₁ a$0)) (B₀ a$0)) ⟦B₁⟧]] :=
              .single <| .listAppComp
                (.lam (.app A₀lc.weaken (.app A₁lc.weaken
                  (.var_bound Nat.one_pos))))
                B₀ki
            [[Δ ⊢ (λ a : K₀. (λ a : K₁. A₀ (A₁ a$0)) (B₀ a$0)) ⟦B₁⟧ ->* (λ a : K₀. A₀ (A₁ (B₀ a$0))) ⟦B₁⟧]] := by
              refine .listApp ?_ .refl
              refine .lam Δ.typeVarDom ?_ ?_
              · exact .app
                  (.lam (.app
                    (A₀lc.weaken (n := 2))
                    (.app (A₁lc.weaken (n := 2)) (.var_bound Nat.two_pos))))
                  (.app (B₀ki.TypeVarLocallyClosed_of.weaken (n := 1)) (.var_bound Nat.one_pos))
              · intro a anin
                let Δawf := Δwf.typeVarExt anin (K := K₀)
                simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₀lc.weaken (n := 1).TypeVar_open_id,
                      A₁lc.TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
                      B₀lc.TypeVar_open_id]
                have : [[(A₀ (A₁ (B₀ a)))]] = [[((A₀ (A₁ a$0))^^(B₀ a))]] := by
                  simp [Type.Type_open, A₀lc.Type_open_id, A₁lc.Type_open_id]
                rw [this]
                refine .single ?_
                apply SmallStep.lamApp
                · apply Kinding.lam <| a :: Δ.typeVarDom
                  intro a' a'nin
                  let Δaa'wf := Δawf.typeVarExt a'nin (K := K₁)
                  simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id]
                  exact A₀ki.weakening Δaa'wf (Δ' := .typeExt (.typeExt .empty ..) ..)
                    (Δ'' := .empty) |>.app <| A₁ki.weakening Δaa'wf
                      (Δ' := .typeExt (.typeExt .empty ..) ..) (Δ'' := .empty) |>.app <| .var .head
                · exact B₀ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty) |>.app <|
                    .var .head
      | .listAppl A₁st (A' := A₁') =>
        apply Exists.intro [[(λ a : K₁. A₀ (A₁' a$0)) ⟦B'⟧]]
        let A₁lc := A₁ki.TypeVarLocallyClosed_of
        constructor
        · exact .single <| .listAppComp A₀lc <| A₁st.preservation A₁ki
        · refine .listApp ?_ .refl
          refine .lam Δ.typeVarDom ?_ ?_
          · exact A₀lc.weaken (n := 1).app <| A₁lc.weaken (n := 1).app <| .var_bound Nat.one_pos
          · intro a anin
            simp [Type.TypeVar_open, A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id,
                  A₁st.preserve_lc A₁lc |>.TypeVar_open_id]
            refine .app .refl <| .app (.single ?_) .refl
            exact A₁st.weakening (Δwf.typeVarExt anin) (Δ' := .typeExt .empty ..) (Δ'' := .empty)
      | .listAppr B'st (B' := B'') =>
        apply Exists.intro [[(λ a : K₁. A₀ (A₁ a$0)) ⟦B''⟧]]
        constructor
        · exact .single <| .listAppComp A₀lc A₁ki
        · exact .listApp .refl <| .single B'st
    | .listAppl A'st => exact ⟨_, .listApp (.single A'st) .refl, .listApp .refl (.single B'st)⟩
    | .listAppr B'st' =>
      let ⟨_, B'mst, B'mst'⟩ := B'st.local_confluence B'st' B'ki Δwf
      exact ⟨_, .listApp .refl B'mst, .listApp .refl B'mst'⟩
  | .prod A'st, .prod A'st', .prod A'lc =>
    let ⟨_, A'mst, A'mst'⟩ := A'st.local_confluence A'st' A'lc Δwf
    exact ⟨_, .prod A'mst, .prod A'mst'⟩
  | .sum A'st, .sum A'st', .sum A'lc =>
    let ⟨_, A'mst, A'mst'⟩ := A'st.local_confluence A'st' A'lc Δwf
    exact ⟨_, .sum A'mst, .sum A'mst'⟩
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · exact Nat.le_of_lt <| Nat.lt_add_right _ <| List.sizeOf_lt_of_mem <| List.mem_append.mpr <|
      .inr <| .head _
where
  of_eq {B₀ B₁} (eq : B₀ = B₁ := by rfl) : ∃ C, [[Δ ⊢ B₀ ->* C]] ∧ [[Δ ⊢ B₁ ->* C]] := by
    rw [eq]
    exact ⟨_, .refl, .refl⟩

end SmallStep

def SmallStepWithKinding Δ K A B := [[Δ ⊢ A : K]] ∧ [[Δ ⊢ A -> B]]

namespace MultiSmallStep

theorem add_kinding (Amst : [[Δ ⊢ A ->* B]]) (Aki : [[Δ ⊢ A : K]])
  : (SmallStepWithKinding Δ K)∗ A B := go <| Amst.preservation Aki
where
  go (Bki : [[Δ ⊢ B : K]]) : (SmallStepWithKinding Δ K)∗ A B := by
    induction Amst with
    | refl => rfl
    | tail _ st ih =>
      apply st.preservation_rev at Bki
      exact .tail (ih Bki) ⟨Bki, st⟩

theorem remove_kinding (h : (SmallStepWithKinding Δ K)∗ A B) : [[Δ ⊢ A ->* B]] := by
  induction h with
  | refl => rfl
  | tail _ kist ih => exact .tail ih kist.right

end MultiSmallStep

namespace SmallStepWithKinding

theorem strongly_normalizing : Thesis.strongly_normalizing (SmallStepWithKinding Δ K) := sorry

theorem local_confluence (Δwf : [[⊢ Δ]]) :
  Thesis.weakly_confluent (SmallStepWithKinding Δ K) := by
  rintro _ _ _ ⟨⟨ki₀, st₀⟩, ⟨ki₁, st₁⟩⟩
  let ⟨_, mst₀, mst₁⟩ := st₀.local_confluence st₁ ki₀ Δwf
  exact ⟨_, mst₀.add_kinding <| st₀.preservation ki₀, mst₁.add_kinding <| st₁.preservation ki₁⟩

end SmallStepWithKinding

namespace MultiSmallStep

theorem confluence (mst₀ : [[Δ ⊢ A ->* B₀]]) (mst₁ : [[Δ ⊢ A ->* B₁]]) (Aki : [[Δ ⊢ A : K]])
  (Δwf : [[⊢ Δ]]) : ∃ C, [[Δ ⊢ B₀ ->* C]] ∧ [[Δ ⊢ B₁ ->* C]] := by
  let ⟨_, mst₀', mst₁'⟩ := Thesis.Newman.newman (r := SmallStepWithKinding Δ K)
    SmallStepWithKinding.strongly_normalizing (SmallStepWithKinding.local_confluence Δwf)
    ⟨add_kinding mst₀ Aki, add_kinding mst₁ Aki⟩
  exact ⟨_, remove_kinding mst₀', remove_kinding mst₁'⟩

-- Shape Preservation
theorem preserve_shape_arr (ArBmst: [[ Δ ⊢ (A → B) ->* T ]]): ∃ A' B', T = [[ (A' → B') ]] ∧ [[ Δ ⊢ A ->* A' ]] ∧ [[ Δ ⊢ B ->* B' ]] := by
  generalize ArBeq : [[ A → B ]] = ArB at ArBmst
  induction ArBmst using Relation.ReflTransGen.head_induction_on generalizing A B
  . case refl =>
    exact ⟨A, B, ArBeq.symm, .refl, .refl⟩
  . case head ArBst Tmst ih =>
    subst ArBeq
    have ⟨A0, B0, A0rB0eq, Amst, Bmst⟩ := ArBst.inv_arr
    specialize ih A0rB0eq.symm
    aesop (add unsafe apply Relation.ReflTransGen.trans)

theorem preserve_shape_forall (Amst: [[ Δ ⊢ (∀ a? : K. A) ->* T ]]): ∃ A', T = [[∀ a? : K. A']] ∧ (∃I, ∀a ∉ (I: List _), [[ Δ, a : K ⊢ A^a ->* A'^a ]]) :=
by
  generalize LamAeq : [[(∀ a : K. A)]] = LamA at Amst
  induction Amst using Relation.ReflTransGen.head_induction_on generalizing A
  . case refl => aesop (add unsafe tactic guessI, unsafe constructors [SmallStep])
  . case head red mred ih =>
    subst LamAeq
    have ⟨A', eqT2, I, AA'⟩ := red.inv_forall
    have ⟨A'', ih⟩ := ih eqT2.symm
    exists A''
    aesop (add unsafe tactic guessI, unsafe apply Relation.ReflTransGen.trans)

theorem preserve_shape_prod (Amst: [[ Δ ⊢ ⊗A ->* T ]]): ∃ A', T = [[⊗A']] ∧ [[ Δ ⊢ A ->* A' ]] :=
by
  generalize ProdAeq : [[(⊗A)]] = ProdA at Amst
  induction Amst using Relation.ReflTransGen.head_induction_on generalizing A
  . case refl => aesop (add unsafe constructors [Relation.ReflTransGen, SmallStep])
  . case head red mred ih =>
    subst ProdAeq
    have := red.inv_prod
    aesop (add unsafe apply Relation.ReflTransGen.trans)

theorem preserve_shape_sum (Amst: [[ Δ ⊢ ⊕A ->* T ]]): ∃ A', T = [[⊕A']] ∧ [[ Δ ⊢ A ->* A' ]] :=
by
  generalize SumAeq : [[(⊕A)]] = SumA at Amst
  induction Amst using Relation.ReflTransGen.head_induction_on generalizing A
  . case refl => aesop (add unsafe constructors [Relation.ReflTransGen, SmallStep])
  . case head red mred ih =>
    subst SumAeq
    have := red.inv_sum
    aesop (add unsafe apply Relation.ReflTransGen.trans)

theorem preserve_shape_list (Amst: [[ Δ ⊢ { </ A@i // i in [:n] /> </ : K // b /> } ->* T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> </ : K // b /> }]] ∧ [[ </ Δ ⊢ A@i ->* B@i // i in [:n] /> ]] := by
  generalize ListAeq : [[{ </ A@i // i in [:n] /> </ : K // b /> }]] = ListA at Amst
  induction Amst using Relation.ReflTransGen.head_induction_on generalizing A
  . case refl => aesop (add unsafe constructors [Relation.ReflTransGen, SmallStep])
  . case head red mred ih =>
    subst ListAeq
    have ⟨B, eqT2, AB⟩ := red.inv_list
    have ⟨B', ih⟩ := ih eqT2.symm
    exists B'
    aesop (add unsafe apply Relation.ReflTransGen.trans)

end MultiSmallStep

namespace EqSmallStep

instance : IsSymm «Type» (EqSmallStep Δ) where
  symm := .symm

def _root_.Iff.equiv {P : α → Prop} : Equivalence (P · ↔ P ·) := ⟨fun _ => ⟨id, id⟩, .symm, .trans⟩

theorem preserve_lc (est : [[Δ ⊢ A <->* B]])
  : A.TypeVarLocallyClosed ↔ B.TypeVarLocallyClosed :=
  Equivalence.eqvGen_iff Iff.equiv |>.mp <|
    Relation.EqvGen.mono (fun _ _ st => ⟨st.preserve_lc, st.preserve_lc_rev⟩) est

theorem Environment_TypeVar_subst_swap (est : [[Δ, Δ'[B / a] ⊢ A <->* A']])
  : [[Δ, Δ'[B' / a] ⊢ A <->* A']] :=
  Relation.EqvGen.mono (fun _ _ => SmallStep.Environment_TypeVar_subst_swap) est

instance : Coe (MultiSmallStep Δ A B) (EqSmallStep Δ A B) where
  coe := MultiSmallStep.EqSmallStep_of

theorem eta (Aki : [[Δ ⊢ A : K₁ ↦ K₂]]) : [[Δ ⊢ λ a : K₁. A a$0 <->* A]] :=
  .rel _ _ <| .eta Aki

theorem lamApp (Aki : [[Δ ⊢ λ a : K₁. A : K₁ ↦ K₂]]) (Bki : [[Δ ⊢ B : K₁]])
  : [[Δ ⊢ (λ a : K₁. A) B <->* A^^B]] :=
  .rel _ _ <| .lamApp Aki Bki

theorem listAppList {b : Bool} (Aki : [[Δ ⊢ A : K₁ ↦ K₂]])
  : [[Δ ⊢ A ⟦{</ B@i // i in [:n] /> </ : K₁ // b />}⟧ <->* {</ A B@i // i in [:n] /> </ : K₂ // b />}]] :=
  .rel _ _ <| .listAppList Aki

theorem listAppId (Aki : [[Δ ⊢ A : L K]]) : [[Δ ⊢ (λ a : K. a$0) ⟦A⟧ <->* A]] :=
  .rel _ _ <| .listAppId Aki

theorem listAppComp (A₀lc : A₀.TypeVarLocallyClosed) (A₁ki : [[Δ ⊢ A₁ : K₁ ↦ K₂]])
  : [[Δ ⊢ A₀ ⟦A₁ ⟦B⟧⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧]] :=
  .rel _ _ <| .listAppComp A₀lc A₁ki

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
  | rel _ _ st =>
    cases A''eq
    cases A'''eq
    refine .rel _ _ <| .lam Δ.typeVarDom ?_
    intro a' a'nin
    replace st := st.TypeVar_open_swap Alc (a := a') aninA a'nin
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at st
    exact st
  | symm _ _ est ih =>
    cases A''eq
    cases A'''eq
    symm
    replace Alc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc
    let A'lc := preserve_lc est |>.mpr Alc |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact ih A'lc aninA' aninA rfl rfl
  | trans _ _ _ est₀ est₁ ih₀ ih₁ =>
    cases A''eq
    cases A'''eq
    let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc'
    let A''''lc := preserve_lc est₀ |>.mp Alc'
    exact Relation.EqvGen.trans _ _ _
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close rfl
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id A''''lc)) <|
      ih₁ A''''lc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id A''''lc) rfl

theorem app : [[Δ ⊢ A <->* A']] → [[Δ ⊢ B <->* B']] → [[Δ ⊢ A B <->* A' B']] :=
  Relation.EqvGen.map₂ .appl .appr

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
  | rel _ _ st =>
    cases A''eq
    cases A'''eq
    refine .rel _ _ <| .forall Δ.typeVarDom ?_
    intro a' a'nin
    replace st := st.TypeVar_open_swap Alc (a := a') aninA a'nin
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at st
    exact st
  | symm _ _ est ih =>
    cases A''eq
    cases A'''eq
    symm
    replace Alc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc
    let A'lc := preserve_lc est |>.mpr Alc |>.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact ih A'lc aninA' aninA rfl rfl
  | trans _ _ _ est₀ est₁ ih₀ ih₁ =>
    cases A''eq
    cases A'''eq
    let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc'
    let A''''lc := preserve_lc est₀ |>.mp Alc'
    exact Relation.EqvGen.trans _ _ _
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close rfl
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id A''''lc)) <|
      ih₁ A''''lc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        (Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id A''''lc) rfl

theorem arr : [[Δ ⊢ A <->* A']] → [[Δ ⊢ B <->* B']] → [[Δ ⊢ A → B <->* A' → B']] :=
  Relation.EqvGen.map₂ .arrl .arrr

theorem list (Aest : ∀ i ∈ [:n], [[Δ ⊢ A@i <->* A'@i]])
  : [[Δ ⊢ {</ A@i // i in [:n] /> </ : K // b />} <->* {</ A'@i // i in [:n] /> </ : K // b />}]] := by
  rw (occs := .pos [2]) [Range.map]
  rw [← Range.map_append (Nat.zero_le _) Nat.le.refl, ← Range.map, ← Range.map]
  rw (occs := .pos [3]) [Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = A i
    nomatch Nat.not_lt_of_le mem.lower mem.upper
  )]
  generalize meq : n = m
  rw (occs := .pos [1, 4]) [← meq]
  let mlen := Nat.le_refl n
  rw (occs := .pos [1]) [meq] at mlen
  clear meq
  induction m with
  | zero => rw [Range.map_same_eq_nil, List.nil_append]
  | succ m' ih =>
    refine .trans _ _ _ (ih (Nat.le_of_succ_le mlen)) ?_
    rw [Range.map_eq_cons_of_lt <| Nat.lt_of_succ_le mlen,
        Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one,
        List.append_assoc, List.singleton_append,
        ← Range.map_shift (m := m' + 1) (j := m' + 1) Nat.le.refl,
        Nat.sub_self]
    specialize Aest m' ⟨Nat.zero_le _, Nat.lt_of_succ_le mlen, Nat.mod_one _⟩
    generalize A''eq : A m' = A'', A'''eq : A' m' = A'''
    rw [A''eq, A'''eq] at Aest
    clear A''eq A'''eq
    induction Aest with
    | refl => rfl
    | rel _ _ st => exact .rel _ _ <| .list st
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih₀ ih₁ => exact .trans _ _ _ ih₀ ih₁

theorem listApp : [[Δ ⊢ A <->* A']] → [[Δ ⊢ B <->* B']] → [[Δ ⊢ A ⟦B⟧ <->* A' ⟦B'⟧]] :=
  Relation.EqvGen.map₂ .listAppl .listAppr

theorem prod : [[Δ ⊢ A <->* B]] → [[Δ ⊢ ⊗ A <->* ⊗ B]] := Relation.EqvGen.map .prod

theorem sum : [[Δ ⊢ A <->* B]] → [[Δ ⊢ ⊕ A <->* ⊕ B]] := Relation.EqvGen.map .sum

theorem of_EquivalenceI (equ : [[Δ ⊢ A ≡ᵢ B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A <->* B]] := by
  induction equ generalizing K with
  | refl => rfl
  | eta A'ki =>
    rename_i A' _ _
    let .lam I A'aki := Aki
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    specialize A'aki a aninI
    simp [Type.TypeVar_open, A'ki.TypeVarLocallyClosed_of.TypeVar_open_id] at A'aki
    let .app A'ki (.var .head) := A'aki
    exact eta (A'ki.TypeVar_drop_of_not_mem_freeTypeVars aninA' (Δ' := .empty))
  | lamApp A'ki B'ki =>
    let .app A'ki B'ki' := Aki
    cases B'ki.deterministic B'ki'
    exact lamApp A'ki B'ki
  | listAppList A'ki => exact .listAppList A'ki
  | listAppId A'ki => exact listAppId A'ki
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
    exact app (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
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
    exact arr (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
  | list _ ih =>
    rename_i K' b _
    rcases Aki.inv_list' with ⟨K'', rfl, A'ki, h⟩
    have : Option.someIf K' b = Option.someIf K'' b := by
      split at h
      · case isTrue h' => rw [h', Option.someIf_true, Option.someIf_true, h]
      · case isFalse h' =>
        rw [Bool.not_eq_true _ |>.mp h', Option.someIf_false, Option.someIf_false]
    rw [this]
    exact list fun i mem => ih i mem (A'ki i mem) Δwf
  | listApp _ _ ih₀ ih₁ =>
    let .listApp A'ki B'ki := Aki
    exact listApp (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
  | listAppComp _ A₁ki =>
    let .listApp A₀ki (.listApp A₁ki' B'ki) := Aki
    cases A₁ki.deterministic A₁ki'
    exact listAppComp A₀ki.TypeVarLocallyClosed_of A₁ki
  | prod equ' ih =>
    let .prod A'ki := Aki
    exact prod <| ih A'ki Δwf
  | sum equ' ih =>
    let .sum A'ki := Aki
    exact sum <| ih A'ki Δwf

theorem of_EquivalenceS (equ : [[Δ ⊢ A ≡ₛ B]]) (Aki : [[Δ ⊢ A : K]]) (Bki : [[Δ ⊢ B : K]])
  (Δwf : [[⊢ Δ]]) : [[Δ ⊢ A <->* B]] := by
  induction equ with
  | base equ' => exact .of_EquivalenceI equ' Aki Δwf
  | symm equ' => exact symm <| .of_EquivalenceI equ' Bki Δwf
  | trans equ' _ ih₀ ih₁ =>
    exact .trans _ _ _ (ih₀ Aki (equ'.preservation.mp Aki)) (ih₁ (equ'.preservation.mp Aki) Bki)

theorem of_Equivalence (equ : [[Δ ⊢ A ≡ B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A <->* B]] :=
  let eqs := equ.TypeEquivalenceS_of Aki.TypeVarLocallyClosed_of Δwf
  of_EquivalenceS eqs Aki (eqs.preservation.mp Aki) Δwf

theorem preservation (est : [[Δ ⊢ A <->* B]]) : [[Δ ⊢ A : K]] ↔ [[Δ ⊢ B : K]] :=
  Equivalence.eqvGen_iff Iff.equiv |>.mp <|
    Relation.EqvGen.mono (fun _ _ st => ⟨st.preservation, st.preservation_rev⟩) est

def _root_.TabularTypeInterpreter.«F⊗⊕ω».TypeEquivalence.equiv
  : Equivalence (TypeEquivalence Δ) := ⟨fun _ => .refl, .symm, .trans⟩

theorem Equivalence_of (est : [[Δ ⊢ A <->* B]]) : [[Δ ⊢ A ≡ B]] :=
  Equivalence.eqvGen_iff TypeEquivalence.equiv |>.mp <|
    Relation.EqvGen.mono (fun _ _ => SmallStep.Equivalence_of) est

theorem common_reduct (est : [[Δ ⊢ A <->* B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : ∃ C, [[Δ ⊢ A ->* C]] ∧ [[Δ ⊢ B ->* C]] := by
  induction est with
  | refl => exact ⟨_, .refl, .refl⟩
  | rel _ _ st => exact ⟨_, .single st, .refl⟩
  | symm _ _ est ih =>
    let ⟨C, B'mst, A'mst⟩ := ih <| preservation est |>.mpr Aki
    exact ⟨_, A'mst, B'mst⟩
  | trans _ _ _ est₀ est₁ ih₀ ih₁ =>
    let ⟨C₀, A'mst, A''mst₀⟩ := ih₀ Aki
    apply preservation est₀ |>.mp at Aki
    let ⟨C₁, A''mst₁, A'''mst⟩ := ih₁ Aki
    let ⟨C, C₀mst, C₁mst⟩ := A''mst₀.confluence A''mst₁ Aki Δwf
    exact ⟨_, A'mst.trans C₀mst, A'''mst.trans C₁mst⟩

-- ====================


-- Injectivity of Type Constructors.
theorem inj_arr (ArBest: [[ Δ ⊢ (A → B) <->* (A' → B') ]]) (ki : [[Δ ⊢ A → B : K]]) (Δwf : [[⊢ Δ]])
  : [[ Δ ⊢ A <->* A' ]] ∧ [[ Δ ⊢ B <->* B' ]] := by
  have ⟨T, ArB_Tmst, A'rB'_Tmst⟩ := ArBest.common_reduct ki Δwf
  have ⟨A1, B1, Teq1, AA1, BB1⟩ := ArB_Tmst.preserve_shape_arr
  have ⟨A2, B2, Teq2, A'A2, B'B2⟩ := A'rB'_Tmst.preserve_shape_arr
  subst T; cases Teq2; case refl =>
  refine ⟨AA1.est_of.trans _ _ _ A'A2.est_of.symm, BB1.est_of.trans _ _ _ B'B2.est_of.symm⟩

theorem inj_forall (Aest: [[ Δ ⊢ (∀ a? : K. A) <->* (∀ a? : K'. A') ]])
  (ki : [[Δ ⊢ ∀ a? : K. A : K'']]) (Δwf : [[⊢ Δ]])
  : K = K' ∧ ∃I: List _, ∀a ∉ I, [[ Δ, a : K ⊢ A^a <->* A'^a ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct ki Δwf
  have ⟨A1, Teq1, I1, AA1⟩:= AT.preserve_shape_forall
  have ⟨A2, Teq2, I2, A'A2⟩ := A'T.preserve_shape_forall
  subst T; cases Teq2; case refl =>
  exact ⟨
    rfl,
    I1 ++ I2,
    λa nin => AA1 a (by simp_all) |>.est_of.trans _ _ _ <| A'A2 a (by simp_all) |>.est_of.symm
  ⟩

theorem inj_prod (Aest: [[ Δ ⊢ ⊗A <->* ⊗A' ]]) (ki : [[Δ ⊢ ⊗ A : K]]) (Δwf : [[⊢ Δ]])
  : [[ Δ ⊢ A <->* A' ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct ki Δwf
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_prod
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_prod
  subst T; cases Teq2; case refl =>
  exact AA1.est_of.trans _ _ _ A'A2.est_of.symm

theorem inj_sum (Aest: [[ Δ ⊢ ⊕A <->* ⊕A' ]]) (ki : [[Δ ⊢ ⊕ A : K]]) (Δwf : [[⊢ Δ]])
  : [[ Δ ⊢ A <->* A' ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct ki Δwf
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_sum
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_sum
  subst T; cases Teq2; case refl =>
  exact AA1.est_of.trans _ _ _ A'A2.est_of.symm

local instance : Inhabited Kind where
  default := .star
in
theorem inj_list (Aest: EqSmallStep Δ [[{ </ A@i // i in [:n] /> </ : K // b /> }]] (.list ([:n'].map fun i => B i) K?))
  (ki : [[Δ ⊢ { </ A@i // i in [:n] /> </ : K // b /> } : K']]) (Δwf : [[⊢ Δ]])
  : n = n' ∧ [[ </ Δ ⊢ A@i <->* B@i // i in [:n] /> ]] ∧ Option.someIf K b = K? := by
  have ⟨T, AT, BT⟩ := Aest.common_reduct ki Δwf
  have ⟨A1, Teq1, AA1⟩ := AT.preserve_shape_list
  rw [← Option.someIf_get!_eq (x? := K?)] at BT
  have ⟨B1, Teq2, BB1⟩ := BT.preserve_shape_list
  subst T
  injection Teq2 with eq
  have eqn'n := Std.Range.length_eq_of_mem_eq eq; subst eqn'n
  have eqBA := Std.Range.eq_of_mem_of_map_eq eq; clear eq
  simp_all [Option.someIf_get!_eq]
  exact λ x xin => AA1 x xin |>.est_of.trans _ _ _ <| BB1 x xin |>.est_of.symm

end EqSmallStep

end TabularTypeInterpreter.«F⊗⊕ω»
