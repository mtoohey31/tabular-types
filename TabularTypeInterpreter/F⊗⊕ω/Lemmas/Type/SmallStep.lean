import Lott.Elab.NotExistentialJudgement
import TabularTypeInterpreter.Data.List
import TabularTypeInterpreter.Data.Option
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Equivalence
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type.SmallStep
import TabularTypeInterpreter.«F⊗⊕ω».Tactics.Basic
import Thesis.Newman

namespace TabularTypeInterpreter.«F⊗⊕ω»

open Std

namespace Type.IsValue

local
instance : Inhabited Kind where
  default := [[*]]
in
theorem empty_list : IsValue (.list [] K?) := by
  have := list (n := 0) (A := fun _ => .list [] none) (b := K?.isSome) (K := K?.get!) nofun
  rw [Range.map_same_eq_nil, Option.someIf_get!_eq] at this
  exact this

theorem unit : IsValue (.prod (.list [] K?)) := prod empty_list

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

theorem exists_mem_freeTypeVars_of_app (ABv : [[value A B]]) : ∃ a, a ∈ A.freeTypeVars := by
  cases ABv with
  | varApp => exact ⟨_, by simp [freeTypeVars]; exact rfl⟩
  | appApp A₀A₁v =>
    let ⟨_, mem⟩ := exists_mem_freeTypeVars_of_app A₀A₁v
    rw [freeTypeVars]
    exact ⟨_, List.mem_append.mpr <| .inl mem⟩

theorem eq_list_of_Kinding (Av : [[value A]]) (Aki : [[ε ⊢ A : L K]])
  : ∃ Bs K?, A = Type.list Bs K? := by
  cases Aki <;> try cases Av
  case var.var ain => nomatch ain
  case app.varApp aki _ =>
    let .var ain := aki
    nomatch ain
  case app.appApp A₀A₁v A₀A₁ki _ =>
    let ⟨_, mem⟩ := exists_mem_freeTypeVars_of_app A₀A₁v
    nomatch A₀A₁ki.freeTypeVars_in_Δ (by rw [freeTypeVars]; exact List.mem_append.mpr <| .inl mem)
  case list => exact ⟨_, _, rfl⟩
  case listApp.listAppVar aki =>
    let .var ain := aki
    nomatch ain
  case listApp.listAppApp B₀B₁v _ _ B₀B₁ki =>
    let ⟨_, mem⟩ := exists_mem_freeTypeVars_of_app B₀B₁v
    nomatch B₀B₁ki.freeTypeVars_in_Δ (by rw [freeTypeVars]; exact List.mem_append.mpr <| .inl mem)


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

theorem TypeVar_open_swap' (Ast : [[Δ, a : K ⊢ A^a -> A'^a]]) (aninA : a ∉ A.freeTypeVars)
  (aninA' : a ∉ A'.freeTypeVars) (a'ninΔ  : [[a' ∉ dom(Δ)]])
  : [[Δ, a' : K ⊢ A^a' -> A'^a']] := by
  have : A.TypeVar_open a' = (A.TypeVar_open a).TypeVar_subst a (.var a') := by
    rw [Type.Type_open_var, Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA, Type.TypeVar_subst, if_pos rfl]
  rw [this]
  have : A'.TypeVar_open a' = (A'.TypeVar_open a).TypeVar_subst a (.var a') := by
    rw [Type.Type_open_var, Type.Type_open_var,
        Type.TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA', Type.TypeVar_subst, if_pos rfl]
  rw [this]
  exact Ast.TypeVar_subst_var a'ninΔ (Δ' := .empty)

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

theorem LE_weakening (le : Δ ≤ Δ') : [[Δ ⊢ A -> B]] → [[Δ' ⊢ A -> B]]
  | eta A'ki => eta <| A'ki.LE_weakening le
  | lamApp A'ki B'ki => lamApp (A'ki.LE_weakening le) (B'ki.LE_weakening le)
  | listAppList A'ki => listAppList <| A'ki.LE_weakening le
  | listAppId A'ki => listAppId <| A'ki.LE_weakening le
  | listAppComp A₀lc A₁ki => listAppComp A₀lc <| A₁ki.LE_weakening le
  | lam I A'st (K := K) => by
    apply lam <| I ++ Δ'.typeVarDom
    intro a anin
    let ⟨aninI, aninΔ'⟩ := List.not_mem_append'.mp anin
    exact A'st a aninI |>.LE_weakening <| le.extExt aninΔ'
  | appl A'st => appl <| A'st.LE_weakening le
  | appr B'st => appr <| B'st.LE_weakening le
  | «forall» I A'st (K := K) => by
    apply «forall» <| I ++ Δ'.typeVarDom
    intro a anin
    let ⟨aninI, aninΔ'⟩ := List.not_mem_append'.mp anin
    exact A'st a aninI |>.LE_weakening <| le.extExt aninΔ'
  | arrl A'st => arrl <| A'st.LE_weakening le
  | arrr B'st => arrr <| B'st.LE_weakening le
  | list A₁st => list <| A₁st.LE_weakening le
  | listAppl A'st => listAppl <| A'st.LE_weakening le
  | listAppr B'st => listAppr <| B'st.LE_weakening le
  | prod A'st => prod <| A'st.LE_weakening le
  | sum A'st => sum <| A'st.LE_weakening le
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem strengthening (ΔΔ'Δ''wf : [[⊢ Δ, Δ', Δ'']])
  : [[Δ, Δ', Δ'' ⊢ A -> B]] → [[Δ, Δ'' ⊢ A : K]] → [[Δ, Δ'' ⊢ A -> B]]
  | eta Bki (K₁ := K₁), .lam I Baki => by
    apply eta
    let ⟨a, anin⟩ := B.freeTypeVars ++ I ++ [[Δ, Δ', Δ'']].typeVarDom |>.exists_fresh
    let ⟨aninBI, aninΔΔ'Δ''⟩ := List.not_mem_append'.mp anin
    let ⟨aninB, aninI⟩ := List.not_mem_append'.mp aninBI
    specialize Baki a aninI
    simp [Type.TypeVar_open, Bki.TypeVarLocallyClosed_of.TypeVar_open_id] at Baki
    rw [← Environment.append] at Baki
    let .app Bki' (.var .head) := Baki
    let ΔΔ'Δ''awf := ΔΔ'Δ''wf.typeVarExt aninΔΔ'Δ'' (K := K₁)
    replace Bki := Bki.weakening ΔΔ'Δ''awf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
    rw [Environment.append, Environment.append, Environment.append, ← Environment.append,
        ← Environment.append] at Bki
    rw [← Environment.append, ← Environment.append] at ΔΔ'Δ''awf
    let Bki'' := Bki'.weakening ΔΔ'Δ''awf
    cases Bki.deterministic Bki''
    exact Bki'.TypeVar_drop_of_not_mem_freeTypeVars aninB (Δ' := .empty)
  | lamApp A'ki B'ki, .app A'ki' B'ki' => by
    cases A'ki.deterministic <| A'ki'.weakening ΔΔ'Δ''wf
    cases B'ki.deterministic <| B'ki'.weakening ΔΔ'Δ''wf
    exact lamApp A'ki' B'ki'
  | listAppList A'ki, .listApp A'ki' _ => by
    cases A'ki.deterministic <| A'ki'.weakening ΔΔ'Δ''wf
    exact listAppList A'ki'
  | listAppId A'ki, .listApp _ A'ki' => by
    cases A'ki.deterministic <| A'ki'.weakening ΔΔ'Δ''wf
    exact listAppId A'ki'
  | listAppComp A₀lc A₁ki, .listApp _ (.listApp A₁ki' _) => by
    cases A₁ki.deterministic <| A₁ki'.weakening ΔΔ'Δ''wf
    exact listAppComp A₀lc A₁ki'
  | lam I A'st (K := K), .lam I' A'ki => by
    apply lam <| I ++ I' ++ [[Δ, Δ', Δ'']].typeVarDom
    intro a anin
    let ⟨aninII', aninΔΔ'Δ''⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let ΔΔ'Δ''awf := ΔΔ'Δ''wf.typeVarExt aninΔΔ'Δ'' (K := K)
    rw [← Environment.append] at ΔΔ'Δ''awf ⊢
    rw [← Environment.append] at ΔΔ'Δ''awf
    exact strengthening ΔΔ'Δ''awf (A'st a aninI) (A'ki a aninI')
  | appl A'st, .app A'ki _ => appl <| A'st.strengthening ΔΔ'Δ''wf A'ki
  | appr B'st, .app _ B'ki => appr <| B'st.strengthening ΔΔ'Δ''wf B'ki
  | «forall» I A'st (K := K), .scheme I' A'ki => by
    apply «forall» <| I ++ I' ++ [[Δ, Δ', Δ'']].typeVarDom
    intro a anin
    let ⟨aninII', aninΔΔ'Δ''⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let ΔΔ'Δ''awf := ΔΔ'Δ''wf.typeVarExt aninΔΔ'Δ'' (K := K)
    rw [← Environment.append] at ΔΔ'Δ''awf ⊢
    rw [← Environment.append] at ΔΔ'Δ''awf
    exact strengthening ΔΔ'Δ''awf (A'st a aninI) (A'ki a aninI')
  | arrl A'st, .arr A'ki _ => arrl <| A'st.strengthening ΔΔ'Δ''wf A'ki
  | arrr B'st, .arr _ B'ki => arrr <| B'st.strengthening ΔΔ'Δ''wf B'ki
  | list A₁st (m := m), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki
    rcases Aki.inv_list' with ⟨_, rfl, A'ki, _⟩
    apply list
    apply strengthening ΔΔ'Δ''wf A₁st
    specialize A'ki m ⟨Nat.zero_le _, by simp [Range.length_toList], Nat.mod_one _⟩
    simp at A'ki
    rw [List.getElem?_append_right (by simp [Range.length_toList])] at A'ki
    simp [Range.length_toList] at A'ki
    exact A'ki
  | listAppl A'st, .listApp A'ki _ => listAppl <| A'st.strengthening ΔΔ'Δ''wf A'ki
  | listAppr B'st, .listApp _ B'ki => listAppr <| B'st.strengthening ΔΔ'Δ''wf B'ki
  | prod A'st, .prod A'ki => prod <| A'st.strengthening ΔΔ'Δ''wf A'ki
  | sum A'st, .sum A'ki => sum <| A'st.strengthening ΔΔ'Δ''wf A'ki
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem LE_strengthening (le : Δ ≤ Δ') : [[Δ' ⊢ A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ A -> B]]
  | eta Bki (K₁ := K₁), .lam I Baki => by
    apply eta
    let ⟨a, anin⟩ := B.freeTypeVars ++ I ++ Δ'.typeVarDom |>.exists_fresh
    let ⟨aninBI, aninΔ'⟩ := List.not_mem_append'.mp anin
    let ⟨aninB, aninI⟩ := List.not_mem_append'.mp aninBI
    specialize Baki a aninI
    simp [Type.TypeVar_open, Bki.TypeVarLocallyClosed_of.TypeVar_open_id] at Baki
    let .app Bki' (.var .head) := Baki
    replace Bki := Bki.LE_weakening <| .ext .refl aninΔ' (K := K₁)
    let Bki'' := Bki'.LE_weakening <| le.extExt aninΔ'
    cases Bki.deterministic Bki''
    exact Bki'.TypeVar_drop_of_not_mem_freeTypeVars aninB (Δ' := .empty)
  | lamApp A'ki B'ki, .app A'ki' B'ki' => by
    cases A'ki.deterministic <| A'ki'.LE_weakening le
    cases B'ki.deterministic <| B'ki'.LE_weakening le
    exact lamApp A'ki' B'ki'
  | listAppList A'ki, .listApp A'ki' _ => by
    cases A'ki.deterministic <| A'ki'.LE_weakening le
    exact listAppList A'ki'
  | listAppId A'ki, .listApp _ A'ki' => by
    cases A'ki.deterministic <| A'ki'.LE_weakening le
    exact listAppId A'ki'
  | listAppComp A₀lc A₁ki, .listApp _ (.listApp A₁ki' _) => by
    cases A₁ki.deterministic <| A₁ki'.LE_weakening le
    exact listAppComp A₀lc A₁ki'
  | lam I A'st (K := K), .lam I' A'ki => by
    apply lam <| I ++ I' ++ Δ'.typeVarDom
    intro a anin
    let ⟨aninII', aninΔ'⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact LE_strengthening (le.extExt aninΔ') (A'st a aninI) (A'ki a aninI')
  | appl A'st, .app A'ki _ => appl <| A'st.LE_strengthening le A'ki
  | appr B'st, .app _ B'ki => appr <| B'st.LE_strengthening le B'ki
  | «forall» I A'st (K := K), .scheme I' A'ki => by
    apply «forall» <| I ++ I' ++ Δ'.typeVarDom
    intro a anin
    let ⟨aninII', aninΔ'⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact LE_strengthening (le.extExt aninΔ') (A'st a aninI) (A'ki a aninI')
  | arrl A'st, .arr A'ki _ => arrl <| A'st.LE_strengthening le A'ki
  | arrr B'st, .arr _ B'ki => arrr <| B'st.LE_strengthening le B'ki
  | list A₁st (m := m), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki
    rcases Aki.inv_list' with ⟨_, rfl, A'ki, _⟩
    apply list
    apply LE_strengthening le A₁st
    specialize A'ki m ⟨Nat.zero_le _, by simp [Range.length_toList], Nat.mod_one _⟩
    simp at A'ki
    rw [List.getElem?_append_right (by simp [Range.length_toList])] at A'ki
    simp [Range.length_toList] at A'ki
    exact A'ki
  | listAppl A'st, .listApp A'ki _ => listAppl <| A'st.LE_strengthening le A'ki
  | listAppr B'st, .listApp _ B'ki => listAppr <| B'st.LE_strengthening le B'ki
  | prod A'st, .prod A'ki => prod <| A'st.LE_strengthening le A'ki
  | sum A'st, .sum A'ki => sum <| A'st.LE_strengthening le A'ki
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

theorem TermVar_drop (Ast : [[Δ, x : C, Δ' ⊢ A -> B]])
  : [[Δ, Δ' ⊢ A -> B]] :=
  match Ast with
  | eta A'ki => eta A'ki.TermVar_drop
  | lamApp A'ki B'ki => lamApp A'ki.TermVar_drop B'ki.TermVar_drop
  | listAppList A'ki => listAppList A'ki.TermVar_drop
  | listAppId A'ki => listAppId A'ki.TermVar_drop
  | listAppComp A₀lc A₁ki => listAppComp A₀lc A₁ki.TermVar_drop
  | lam I A'st => by
    apply lam I
    intro a anin
    specialize A'st a anin
    rw [← Environment.append] at A'st ⊢
    exact A'st.TermVar_drop
  | appl A'st => appl A'st.TermVar_drop
  | appr B'st => appr B'st.TermVar_drop
  | «forall» I A'st => by
    apply «forall» I
    intro a anin
    specialize A'st a anin
    rw [← Environment.append] at A'st ⊢
    exact A'st.TermVar_drop
  | arrl A'st => arrl A'st.TermVar_drop
  | arrr B'st => arrr B'st.TermVar_drop
  | list A₁st => list A₁st.TermVar_drop
  | listAppl A'st => listAppl A'st.TermVar_drop
  | listAppr B'st => listAppr B'st.TermVar_drop
  | prod A'st => prod A'st.TermVar_drop
  | sum A'st => sum A'st.TermVar_drop
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  exact List.mem_append.mpr <| .inr <| .head _

theorem enumerably_branching (Aki : [[Δ ⊢ A : K]])
  : ∃ Bs : List «Type», ∀ {B}, B ∈ Bs ↔ [[Δ ⊢ A -> B]] := by
  match A, Aki with
  | _, .var _ => exact ⟨[], nofun, nofun⟩
  | [[λ a : K. A']], .lam I A'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
    let ⟨aninA'I, aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp aninA'I
    specialize A'ki a aninI
    let ⟨Bs', h⟩ := enumerably_branching A'ki
    by_cases ∃ A'' K', A' = [[A'' a$0]] ∧ [[Δ ⊢ A'' : K ↦ K']]
    · case pos h =>
      rcases h with ⟨A'', _, rfl, A''ki⟩
      refine ⟨A'' :: Bs'.map (.lam K <| ·.TypeVar_close a), ?_⟩
      intro B
      constructor
      · rintro (_ | s)
        · case head => exact eta A''ki
        · case tail mem =>
          rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
          apply lam Δ.typeVarDom
          intro a' a'nin
          exact TypeVar_open_swap (h.mp mem')
            (.app (A''ki.TypeVarLocallyClosed_of.weaken (n := 1)) (.var_bound Nat.one_pos)) aninA'
            a'nin
      · intro st
        match st with
        | .eta _ => exact .head _
        | .lam I st' =>
          rename «Type» => A'''
          refine .tail _ ?_
          apply List.mem_map.mpr
          let ⟨a', a'nin⟩ := ↑a :: A''.freeTypeVars ++ A'''.freeTypeVars ++ I |>.exists_fresh
          let ⟨a'ninaA''A''', a'ninI⟩ := List.not_mem_append'.mp a'nin
          let ⟨a'ninaA'', a'ninA'''⟩ := List.not_mem_append'.mp a'ninaA''A'''
          let ⟨ane, a'ninA''⟩ := List.not_mem_cons.mp a'ninaA''
          let mem := h.mpr <| st' a' a'ninI |>.TypeVar_open_swap
            (.app (A''ki.TypeVarLocallyClosed_of.weaken (n := 1)) (.var_bound Nat.one_pos))
            (by simp [Type.freeTypeVars]; exact a'ninA'') aninΔ
          rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA'''] at mem
          refine ⟨_, mem, ?_⟩
          rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars]
          apply Type.not_mem_freeTypeVars_TypeVar_open_drop
          apply st' a' a'ninI |>.preserve_not_mem_freeTypeVars
          simp [Type.TypeVar_open, A''ki.TypeVarLocallyClosed_of.TypeVar_open_id,
                Type.freeTypeVars] at aninA' ⊢
          exact ⟨aninA', ane.symm⟩
    · case neg ne =>
      replace ne A'' K' := not_and.mp (not_exists.mp (not_exists.mp ne A'') K')
      refine ⟨Bs'.map (.lam K <| ·.TypeVar_close a), ?_⟩
      intro B
      let A'lc := A'ki.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
      rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
      constructor
      · intro mem
        rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
        apply lam Δ.typeVarDom
        intro a' a'nin
        exact TypeVar_open_swap (h.mp mem') A'lc aninA' a'nin
      · intro st
        match st with
        | .eta Bki => nomatch ne _ _ rfl Bki
        | .lam I st' =>
          rename «Type» => A'''
          apply List.mem_map.mpr
          let ⟨a', a'nin⟩ := ↑a :: A'.freeTypeVars ++ A'''.freeTypeVars ++ I |>.exists_fresh
          let ⟨a'ninaA'A''', a'ninI⟩ := List.not_mem_append'.mp a'nin
          let ⟨a'ninaA', a'ninA'''⟩ := List.not_mem_append'.mp a'ninaA'A'''
          let ⟨ane, a'ninA'⟩ := List.not_mem_cons.mp a'ninaA'
          let mem := h.mpr <| st' a' a'ninI |>.TypeVar_open_swap A'lc a'ninA' aninΔ
          rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA'''] at mem
          refine ⟨_, mem, ?_⟩
          rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars]
          exact Type.not_mem_freeTypeVars_TypeVar_open_drop <|
            st' a' a'ninI |>.preserve_not_mem_freeTypeVars <|
            Type.not_mem_freeTypeVars_TypeVar_open_intro aninA' ane.symm
  | [[A' B]], .app A'ki Bki =>
    let ⟨A's, A'h⟩ := enumerably_branching A'ki
    let ⟨Bs, Bh⟩ := enumerably_branching Bki
    by_cases ∃ K₁ A'', A' = [[λ a : K₁. A'']]
    · case pos h =>
      rcases h with ⟨K₁, A'', rfl⟩
      refine ⟨A''.Type_open B :: (A's.map (·.app B)) ++ Bs.map ([[λ a : K₁. A'']].app ·), ?_⟩
      intro B'
      constructor
      · intro mem
        cases mem with
        | head =>
          cases A'ki
          case lam I A''ki =>
          exact lamApp (.lam I A''ki) Bki
        | tail _ mem' =>
          match List.mem_append.mp mem' with
          | .inl mem'' =>
            rcases List.mem_map.mp mem'' with ⟨_, mem''', rfl⟩
            exact appl <| A'h.mp mem'''
          | .inr mem'' =>
            rcases List.mem_map.mp mem'' with ⟨_, mem''', rfl⟩
            exact appr <| Bh.mp mem'''
      · intro st
        match st with
        | lamApp .. => exact List.mem_append.mpr <| .inl <| .head ..
        | appl st' =>
          exact List.mem_append.mpr <| .inl <| .tail _ <| List.mem_map.mpr ⟨_, A'h.mpr st', rfl⟩
        | appr st' => exact List.mem_append.mpr <| .inr <| List.mem_map.mpr ⟨_, Bh.mpr st', rfl⟩
    · case neg ne =>
      replace ne A'' K' := not_exists.mp (not_exists.mp ne A'') K'
      refine ⟨(A's.map (·.app B)) ++ Bs.map (A'.app ·), ?_⟩
      intro B'
      constructor
      · intro mem
        match List.mem_append.mp mem with
        | .inl mem' =>
          rcases List.mem_map.mp mem' with ⟨_, mem'', rfl⟩
          exact appl <| A'h.mp mem''
        | .inr mem' =>
          rcases List.mem_map.mp mem' with ⟨_, mem'', rfl⟩
          exact appr <| Bh.mp mem''
      · intro st
        match st with
        | lamApp .. => nomatch ne _ _
        | appl st' => exact List.mem_append.mpr <| .inl <| List.mem_map.mpr ⟨_, A'h.mpr st', rfl⟩
        | appr st' => exact List.mem_append.mpr <| .inr <| List.mem_map.mpr ⟨_, Bh.mpr st', rfl⟩
  | [[∀ a : K. A']], .scheme I A'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
    let ⟨aninA'I, aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp aninA'I
    specialize A'ki a aninI
    let ⟨Bs', h⟩ := enumerably_branching A'ki
    refine ⟨Bs'.map (.forall K <| ·.TypeVar_close a), ?_⟩
    intro B
    let A'lc := A'ki.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    constructor
    · intro mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      apply «forall» Δ.typeVarDom
      intro a' a'nin
      exact TypeVar_open_swap (h.mp mem') A'lc aninA' a'nin
    · intro st
      let .forall I st' (A' := A''') := st
      apply List.mem_map.mpr
      let ⟨a', a'nin⟩ := ↑a :: A'.freeTypeVars ++ A'''.freeTypeVars ++ I |>.exists_fresh
      let ⟨a'ninaA'A''', a'ninI⟩ := List.not_mem_append'.mp a'nin
      let ⟨a'ninaA', a'ninA'''⟩ := List.not_mem_append'.mp a'ninaA'A'''
      let ⟨ane, a'ninA'⟩ := List.not_mem_cons.mp a'ninaA'
      let mem := h.mpr <| st' a' a'ninI |>.TypeVar_open_swap A'lc a'ninA' aninΔ
      rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA'''] at mem
      refine ⟨_, mem, ?_⟩
      rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars]
      exact Type.not_mem_freeTypeVars_TypeVar_open_drop <|
        st' a' a'ninI |>.preserve_not_mem_freeTypeVars <|
        Type.not_mem_freeTypeVars_TypeVar_open_intro aninA' ane.symm
  | [[A' → B]], .arr A'ki Bki =>
    let ⟨A's, A'h⟩ := enumerably_branching A'ki
    let ⟨Bs, Bh⟩ := enumerably_branching Bki
    refine ⟨A's.map (·.arr B) ++ Bs.map (A'.arr ·), ?_⟩
    intro B'
    constructor
    · intro mem
      match List.mem_append.mp mem with
      | .inl mem' =>
        rcases List.mem_map.mp mem' with ⟨_, mem'', rfl⟩
        exact arrl <| A'h.mp mem''
      | .inr mem' =>
        rcases List.mem_map.mp mem' with ⟨_, mem'', rfl⟩
        exact arrr <| Bh.mp mem''
    · intro st
      match st with
      | arrl st' => exact List.mem_append.mpr <| .inl <| List.mem_map.mpr ⟨_, A'h.mpr st', rfl⟩
      | arrr st' => exact List.mem_append.mpr <| .inr <| List.mem_map.mpr ⟨_, Bh.mpr st', rfl⟩
  | _, .list A'ki _ (A := A') (n := n) (K := K') (b := b) =>
    let ⟨A's, A'h⟩ := Range.skolem (enumerably_branching <| A'ki · ·)
    refine ⟨
      [:n].toList.flatMap fun i => A's i |>.map fun B =>
        [[{</ A'@j // j in [:i] />, B, </ A'@k // k in [i+1:n] /> </ : K' // b />}]],
      ?_
    ⟩
    intro B
    constructor
    · intro mem
      let ⟨i, mem', mem''⟩ := List.mem_flatMap.mp mem
      let mem''' := Range.mem_of_mem_toList mem'
      rcases List.mem_map.mp mem'' with ⟨_, mem'''', rfl⟩
      let st := A'h i mem''' |>.mp mem'''' |>.list (A₀ := A') (m := i)
        (A₂ := fun j => A' (j + (i + 1))) (n := n - (i + 1)) (K := K') (b := b)
      rw [Range.map, ← Range.map_append (Nat.zero_le _) mem'''.upper.le, ← Range.map, ← Range.map,
          Range.map_eq_cons_of_lt mem'''.upper, ← Range.map_shift (j := i + 1) Nat.le.refl,
          Nat.sub_self]
      exact st
    · intro st
      generalize A''eq : Type.list .. = A'' at st
      let .list st' (m := i) (n := n') := st
      injection A''eq with A'seq Keq
      rw [Keq]
      let lengths_eq := congrArg List.length A'seq
      simp [Range.length_toList] at lengths_eq
      cases lengths_eq
      rw [Range.map, ← Range.map_append (m := i) (Nat.zero_le _) (Nat.le_add_right ..), ← Range.map,
          ← Range.map, Range.map,
          Range.map_eq_cons_of_lt (Nat.lt_add_of_pos_right (Nat.succ_pos _)), ← Range.map] at A'seq
      let ⟨A₀eq, A'seq'⟩ := List.of_length_eq_of_append_eq_append (by simp [Range.length_toList])
        A'seq
      let mem : i ∈ [:i + (n' + 1)] :=
        ⟨Nat.zero_le _, (Nat.lt_add_of_pos_right (Nat.succ_pos _)), Nat.mod_one _⟩
      rcases List.cons.inj A'seq' with ⟨rfl, A₂eq⟩
      let mem' := A'h i mem |>.mpr st'
      apply List.mem_flatMap.mpr ⟨i, Range.mem_toList_of_mem mem, _⟩
      apply List.mem_map.mpr ⟨_, mem', _⟩
      rw [A₀eq, A₂eq]
  | [[A' ⟦B⟧]], .listApp A'ki Bki (K₁ := K₀) (K₂ := K₂) =>
    let ⟨A's, A'h⟩ := enumerably_branching A'ki
    let ⟨Bs, Bh⟩ := enumerably_branching Bki
    let ⟨K₁, _, hK₁⟩ : ∃ K₁ K₂, ∀ A₁ B', [[A₁ ⟦B'⟧]] = B → [[Δ ⊢ A₁ : K₁ ↦ K₂]] := by
      cases B
      case listApp =>
        let .listApp A₁ki _ (K₁ := K₁) (K₂ := K₂) := Bki
        refine ⟨K₁, K₂, ?_⟩
        intro _ _ eq
        cases eq
        exact A₁ki
      all_goals exact ⟨.star, .star, nofun⟩
    refine ⟨
      (if let .list Bs K? := B then
         [ [[{</ A' Bs.get!@i // i in [:Bs.length] /> </ : K₂ // K?.isSome />}]] ]
       else []) ++
      (if let [[λ a : K. a$0]] := A' then [B] else []) ++
      (if let [[A₁ ⟦B'⟧]] := B then [ [[(λ a : K₁. A' (A₁ a$0)) ⟦B'⟧]] ] else []) ++
       A's.map (·.listApp B) ++ Bs.map (A'.listApp ·), ?_⟩
    intro B'
    constructor
    · intro mem
      match List.mem_append.mp mem with
      | .inl mem' =>
        match List.mem_append.mp mem' with
        | .inl mem'' =>
          match List.mem_append.mp mem'' with
          | .inl mem''' =>
            match List.mem_append.mp mem''' with
            | .inl mem'''' =>
              split at mem''''
              · case _ Bs K? Bki _ _ =>
                cases List.mem_singleton.mp mem''''
                rw (occs := .pos [1]) [← Range.map_get!_eq (as := Bs),
                                       ← Option.someIf_get!_eq (x? := K?)] at Bki ⊢
                have : Option.someIf K?.get! K?.isSome = Option.someIf K₀ K?.isSome := by
                  rcases Bki.inv_list' with ⟨_, eq, _, h⟩
                  cases eq
                  split at h
                  · case isTrue h' => rw [h, h']
                  · case isFalse h' =>
                    rw [Bool.not_eq_true _ |>.mp h', Option.someIf_false, Option.someIf_false]
                rw [this]
                exact listAppList A'ki
              · nomatch mem''''
            | .inr mem'''' =>
              split at mem''''
              · case _ A'ki _ =>
                let .lam .. := A'ki
                cases List.mem_singleton.mp mem''''
                exact listAppId Bki
              · nomatch mem''''
          | .inr mem''' =>
            split at mem'''
            · case _ Bki _ hK₁ =>
              cases List.mem_singleton.mp mem'''
              exact listAppComp A'ki.TypeVarLocallyClosed_of <| hK₁ _ _ rfl
            · nomatch mem'''
        | .inr mem'' =>
          rcases List.mem_map.mp mem'' with ⟨_, mem''', rfl⟩
          exact listAppl <| A'h.mp mem'''
      | .inr mem' =>
        rcases List.mem_map.mp mem' with ⟨_, mem'', rfl⟩
        exact listAppr <| Bh.mp mem''
    · intro st
      cases st with
      | listAppList A'ki' =>
        cases A'ki.deterministic A'ki'
        rename Nat → «Type» => Bs
        apply List.mem_append.mpr <| .inl <| List.mem_append.mpr <| .inl <| List.mem_append.mpr <|
          .inl <| List.mem_append.mpr <| .inl _
        conv => simp_match
        apply List.mem_singleton.mpr
        rw [List.length_map, Range.length_toList, Nat.sub_zero, Range.map,
            Range.map_eq_of_eq_of_mem'' (by
              intro i mem
              show _ = A'.app (Bs i)
              congr
              simp
              rw [List.getElem?_eq_getElem (by rw [Range.length_toList]; exact mem.upper),
                  Range.getElem_toList mem.upper, Nat.zero_add, Option.map, Option.getD]),
            ← Range.map, Option.isSome_someIf]
      | listAppId =>
        exact List.mem_append.mpr <| .inl <| List.mem_append.mpr <| .inl <| List.mem_append.mpr <|
          .inl <| List.mem_append.mpr <| .inr <| .head _
      | listAppComp _ A₁ki =>
        cases hK₁ _ _ rfl |>.deterministic A₁ki
        exact List.mem_append.mpr <| .inl <| List.mem_append.mpr <| .inl <| List.mem_append.mpr <|
          .inr <| .head _
      | listAppl st' =>
        exact List.mem_append.mpr <| .inl <| List.mem_append.mpr <| .inr <|
          List.mem_map.mpr ⟨_, A'h.mpr st', rfl⟩
      | listAppr st' => exact List.mem_append.mpr <| .inr <| List.mem_map.mpr ⟨_, Bh.mpr st', rfl⟩
  | _, .prod A'ki =>
    let ⟨A's, A'h⟩ := enumerably_branching A'ki
    refine ⟨A's.map Type.prod, ?_⟩
    intro B
    constructor
    · intro mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      exact prod <| A'h.mp mem'
    · intro st
      let .prod st' := st
      exact List.mem_map.mpr ⟨_, A'h.mpr st', rfl⟩
  | _, .sum A'ki =>
    let ⟨A's, A'h⟩ := enumerably_branching A'ki
    refine ⟨A's.map Type.sum, ?_⟩
    intro B
    constructor
    · intro mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      exact sum <| A'h.mp mem'
    · intro st
      let .sum st' := st
      exact List.mem_map.mpr ⟨_, A'h.mpr st', rfl⟩
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  apply Nat.lt_add_right
  apply List.sizeOf_lt_of_mem
  apply Range.mem_map_of_mem
  assumption

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

theorem LE_weakening (mst : [[Δ ⊢ A ->* B]]) (le : Δ ≤ Δ') : [[Δ' ⊢ A ->* B]] := by
  induction mst with
  | refl => rfl
  | tail _ st ih => exact .tail ih <| st.LE_weakening le

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

theorem preservation_rev (Amst : [[Δ ⊢ A ->* B]]) (Bki : [[Δ ⊢ B : K]]) : [[Δ ⊢ A : K]] := by
  induction Amst using Relation.ReflTransGen.head_induction_on with
  | refl => exact Bki
  | head st _ ih => exact st.preservation_rev ih

theorem LE_strengthening (mst : [[Δ' ⊢ A ->* B]]) (le : Δ ≤ Δ') (Aki : [[Δ ⊢ A : K]])
  : [[Δ ⊢ A ->* B]] := by
  induction mst with
  | refl => rfl
  | tail _ st ih => exact .tail ih <| st.LE_strengthening le <| ih.preservation Aki

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

theorem to_In (Amst : [[Δ ⊢ A ->* B]]) : ∃ n, [[Δ ⊢n A ->* B]] := by
  induction Amst with
  | refl => exact ⟨_, .refl⟩
  | tail _ st ih =>
    let ⟨_, msti⟩ := ih
    exact ⟨_, msti.tail st⟩

theorem of_In (Amsti : [[Δ ⊢n A ->* B]]) : [[Δ ⊢ A ->* B]] := by
  induction Amsti with
  | refl => rfl
  | tail _ st ih => exact ih.tail st

theorem eq_of_IsValue (Amst : [[Δ ⊢ A ->* B]]) (Av : [[value A]]) : A = B := by
  apply Or.resolve_right <| Relation.ReflTransGen.cases_head Amst
  apply not_exists.mpr
  intro B
  apply not_and.mpr
  intro st
  nomatch Av.not_step st

end MultiSmallStep

namespace SmallStep

theorem TypeVar_subst_out (Bst : [[Δ ⊢ B -> B']]) (Alc : A.TypeVarLocallyClosed)
  (Bki : [[Δ ⊢ B : K]]) : [[Δ ⊢ A[B / a] ->* A[B' / a] ]] := by
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
    replace A'lc := A'lc.Type_open_dec .var_free (B := .var (.free a'))
    rw [← Type.Type_open_var] at A'lc
    exact TypeVar_subst_out (Bst.LE_weakening (.ext .refl a'ninΔ)) A'lc <|
      Bki.weakening_r (fun | _, .head _ => a'ninΔ) (Δ' := .typeExt .empty ..)
  · case app =>
    let .app A'lc B''lc := Alc
    exact .app (TypeVar_subst_out Bst A'lc Bki) (TypeVar_subst_out Bst B''lc Bki)
  · case «forall» K _ =>
    let .forall A'lc := Alc
    let Blc := Bki.TypeVarLocallyClosed_of
    apply MultiSmallStep.forall (a :: Δ.typeVarDom) <| A'lc.TypeVar_subst Blc.weaken
    intro a' a'nin
    let ⟨ane, a'ninΔ⟩ := List.not_mem_cons.mp a'nin
    rw [← Blc.TypeVar_open_TypeVar_subst_comm ane.symm,
        ← Bst.preserve_lc Blc |>.TypeVar_open_TypeVar_subst_comm ane.symm]
    replace A'lc := A'lc.Type_open_dec .var_free (B := .var (.free a'))
    rw [← Type.Type_open_var] at A'lc
    exact TypeVar_subst_out (Bst.LE_weakening (.ext .refl a'ninΔ)) A'lc <|
      Bki.weakening_r (fun | _, .head _ => a'ninΔ) (Δ' := .typeExt .empty ..)
  · case arr =>
    let .arr A'lc B''lc := Alc
    exact .arr (TypeVar_subst_out Bst A'lc Bki) (TypeVar_subst_out Bst B''lc Bki)
  · case list A's K? =>
    let .list Alc' := Alc
    rw [← Range.map_get!_eq (as := A's), List.map_map, List.map_map,
        ← Option.someIf_get!_eq (x? := K?), ← Range.map, ← Range.map]
    apply MultiSmallStep.list
    intro i mem
    exact TypeVar_subst_out Bst (Alc' _ <| List.get!_mem mem.upper) Bki
  · case listApp =>
    let .listApp A'lc B''lc := Alc
    exact .listApp (TypeVar_subst_out Bst A'lc Bki) (TypeVar_subst_out Bst B''lc Bki)
  · case prod =>
    let .prod A'lc := Alc
    exact .prod <| TypeVar_subst_out Bst A'lc Bki
  · case sum =>
    let .sum A'lc := Alc
    exact .sum <| TypeVar_subst_out Bst A'lc Bki
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
  (Bki : [[Δ ⊢ B : K]]) : [[Δ ⊢ A^^B ->* A^^B']] := by
  let ⟨a, anin⟩ := A.freeTypeVars.exists_fresh
  rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars anin,
      ← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars anin]
  let Alc' := Alc.Type_open_dec .var_free (B := .var (.free a))
  rw [← Type.Type_open_var] at Alc'
  exact TypeVar_subst_out Bst Alc' Bki

theorem TypeVar_subst_in (Ast : [[Δ, a : K, Δ' ⊢ A -> A']]) (Alc : A.TypeVarLocallyClosed)
  (Δwf : [[⊢ Δ, a : K, Δ']]) (Bki : [[Δ ⊢ B : K]]) : [[Δ, Δ'[B / a] ⊢ A[B / a] -> A'[B / a] ]] := by
  cases Ast <;> simp [Type.TypeVar_subst]
  · case eta A'ki => exact eta (A'ki.subst' Δwf Bki)
  · case lamApp A'ki B'ki =>
    rw [Bki.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist]
    replace A'ki := A'ki.subst' Δwf Bki
    rw [Type.TypeVar_subst] at A'ki
    exact lamApp A'ki (B'ki.subst' Δwf Bki)
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
    exact listAppList (A'ki.subst' Δwf Bki)
  · case listAppId A'ki => exact listAppId (A'ki.subst' Δwf Bki)
  · case listAppComp A₀lc A₁ki =>
    exact listAppComp (A₀lc.TypeVar_subst Bki.TypeVarLocallyClosed_of) (A₁ki.subst' Δwf Bki)
  · case lam I A'st =>
    let .lam A'lc := Alc
    apply lam <| a :: I ++ [[Δ, a : K, Δ']].typeVarDom
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
    exact .appl <| TypeVar_subst_in A'st A'lc Δwf Bki
  · case appr B'st =>
    let .app _ B'lc := Alc
    exact .appr <| TypeVar_subst_in B'st B'lc Δwf Bki
  · case «forall» I A'st =>
    let .forall A'lc := Alc
    apply «forall» <| a :: I ++ [[Δ, a : K, Δ']].typeVarDom
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
    exact .arrl <| TypeVar_subst_in A'st A'lc Δwf Bki
  · case arrr B'st =>
    let .arr _ B'lc := Alc
    exact .arrr <| TypeVar_subst_in B'st B'lc Δwf Bki
  · case list A₁st =>
    apply list
    let .list A'lc := Alc
    let A₁lc := A'lc _ <| List.mem_append.mpr <| .inr <| .head ..
    exact TypeVar_subst_in A₁st A₁lc Δwf Bki
  · case listAppl A'st =>
    let .listApp A'lc _ := Alc
    exact .listAppl <| TypeVar_subst_in A'st A'lc Δwf Bki
  · case listAppr B'st =>
    let .listApp _ B'lc := Alc
    exact .listAppr <| TypeVar_subst_in B'st B'lc Δwf Bki
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
  (aninA' : a ∉ A'.freeTypeVars) : [[Δ, Δ'[B / a] ⊢ A^^B -> A'^^B]] := by
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
          .single <| Type_open_in (A'st' a aninI) A'lc B'ki (Δwf.typeVarExt aninΔ) aninA' aninA''
            (Δ' := .empty),
          .single <| lamApp (preservation (.lam I A'st') A'ki) B'ki
        ⟩
    | .appr B'st =>
      exact ⟨_, Type_open_out B'st A'lc B'ki, lamApp A'ki (B'st.preservation B'ki)⟩
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
          .single <| Type_open_in (A'st' a aninI) A'lc' B'ki (Δwf.typeVarExt aninΔ) aninA'' aninA'''
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
        Type_open_out B'st A'lc' B'ki
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

namespace MultiSmallStep

-- Shape Preservation
theorem preserve_shape_var {a : TypeVarId} (amst: [[ Δ ⊢ a ->* T ]]): T = (.var (.free a)) := by
  generalize Aeq : Type.var (.free a) = A at amst
  induction amst using Relation.ReflTransGen.head_induction_on
  . case refl => rfl
  . case head ast Tmst ih =>
    subst Aeq
    nomatch ast

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

def SmallStepWithKinding Δ K A B := [[Δ ⊢ A : K]] ∧ [[Δ ⊢ A -> B]]

theorem StronglyNormalizing'.add_Kinding (Asn : [[Δ ⊢ SN(A)]])
  : Acc (Rel.inv (SmallStepWithKinding Δ K)) A := by
  apply Subrelation.accessible _ Asn
  rintro _ _ ⟨_, st⟩
  exact st

namespace StronglyNormalizing

theorem add_Kinding (Asn : [[SN(A)]]) : Acc (Rel.inv (SmallStepWithKinding .empty K)) A := by
  apply Subrelation.accessible _ Asn
  rintro _ _ ⟨_, st⟩
  exact st

theorem remove_Kinding (Asn : Acc (Rel.inv (SmallStepWithKinding .empty K)) A) (Aki : [[ε ⊢ A : K]])
  : [[SN(A)]] := by
  induction Asn with
  | intro _ _ ih =>
    constructor
    intro _ st
    exact ih _ ⟨Aki, st⟩ <| st.preservation Aki

theorem preservation (Asn : [[SN(A)]]) (Ast : [[ε ⊢ A -> B]]) : [[SN(B)]] := by
  induction Asn generalizing B with
  | intro _ _ ih =>
    constructor
    intro B' st
    apply ih
    · rw [Rel.inv, flip]
      exact Ast
    · rw [Rel.inv, flip] at st
      exact st

theorem preservation_rev (h : ∀ B, [[ε ⊢ A -> B]] → [[SN(B)]]) : [[SN(A)]] := by
  constructor
  intro A' st
  rw [Rel.inv, flip] at st
  specialize h A' st
  exact h

theorem arr (Asn : [[SN(A)]]) (Bsn : [[SN(B)]]) : [[SN(A → B)]] := by
  induction Asn generalizing B with
  | intro A' _ ihA =>
    induction Bsn with
    | intro B' B'sn ihB =>
      constructor
      intro C st
      rw [Rel.inv, flip] at st
      match st with
      | .arrl A'st => exact ihA _ A'st <| .intro _ B'sn
      | .arrr B'st => exact ihB _ B'st

theorem list (Asn : ∀ i ∈ [:n], [[SN(A@i)]]) : [[SN({</ A@i // i in [:n] /> </ : K // b />})]] := by
  induction n with
  | zero =>
    constructor
    intro _ st
    generalize A'seq : [:_].map _ = A's, Option.someIf .. = K? at st
    let .list _ := st
    let lengths_eq := congrArg List.length A'seq
    simp [Range.length_toList] at lengths_eq
    nomatch lengths_eq
  | succ n' ih =>
    specialize ih fun _ mem => Asn _ ⟨Nat.zero_le _, Nat.lt_succ_of_lt mem.upper, Nat.mod_one _⟩
    generalize A'eq : Type.list .. = A' at ih
    induction ih generalizing A with
    | intro _ _ ih' =>
      let An'sn := Asn n' ⟨Nat.zero_le _, Nat.le.refl, Nat.mod_one _⟩
      generalize A''eq : A n' = A''
      rw [A''eq] at An'sn
      induction An'sn generalizing A with
      | intro _ An'sn' ih'' =>
        cases A''eq
        constructor
        intro B st
        generalize A'''seq : [:_].map _ = A''', K?eq : Option.someIf .. = K? at st
        let .list st' (A₀ := A₀) (A₁' := A₁') (A₂ := A₂) (m := m) (n := n'') := st
        let lengths_eq := congrArg List.length A'''seq
        simp [Range.length_toList] at lengths_eq
        by_cases m = n'
        · case pos h =>
          cases h
          simp at lengths_eq
          cases lengths_eq
          rw [← K?eq]
          rw [Range.map_same_eq_nil] at A'''seq ⊢
          rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one] at A'''seq
          let ⟨A'''seq', An'eq⟩ := List.of_length_eq_of_append_eq_append (by simp) A'''seq
          cases An'eq
          specialize ih'' _ st' (A := fun i => if i = n' then A₁' else A i) (by
            intro i mem
            simp
            split
            · case isTrue => exact An'sn' _ st'
            · case isFalse => exact Asn i mem
          ) (by
            rw [← A'eq]
            apply Type.list.injEq .. |>.mpr ⟨_, rfl⟩
            apply Range.map_eq_of_eq_of_mem
            intro i mem
            rw [if_neg (Nat.ne_of_lt mem.upper)]
          ) (if_pos rfl)
          rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one, if_pos rfl,
              Range.map_eq_of_eq_of_mem'' (fun i mem => if_neg (Nat.ne_of_lt mem.upper)),
              A'''seq'] at ih''
          exact ih''
        · case neg h =>
          let st'' := st'.list (A₀ := A₀) (A₂ := A₂) (m := m) (n := n''.pred) (K := K) (b := b)
          rw [Nat.pred_eq_sub_one] at st''
          let n''pos : 0 < n'' := by
            apply Nat.pos_of_ne_zero
            intro eq
            apply h
            cases eq
            simp_arith at lengths_eq
            symm
            exact lengths_eq
          let A'''seq' := A'''seq
          rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one,
              Range.map_eq_snoc_of_lt n''pos, ← List.cons_append, ← List.append_assoc] at A'''seq'
          let ⟨A'''seq', An'eq⟩ := List.of_length_eq_of_append_eq_append (by
            simp [Range.length_toList]
            apply Nat.succ_inj.mp
            rw [Nat.succ_eq_add_one, lengths_eq, Nat.sub_add_cancel n''pos]
            simp_arith
          ) A'''seq'
          rw [← A'''seq', A'eq] at st''
          specialize ih' _ st'' (A := fun i => if i = m then A₁' else A i) (by
            intro i mem
            simp
            split
            · case isTrue h =>
              cases h
              apply Asn _ mem |>.preservation
              convert st'
              rw [Range.map, ← Range.map_append (Nat.zero_le (m + 1)) (by
                apply Nat.succ_le.mpr
                apply Nat.succ_lt_succ_iff.mp
                rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, lengths_eq]
                linarith), ← Range.map, ← Range.map, ← List.singleton_append,
                ← List.append_assoc] at A'''seq'
              let ⟨A'''seq'', _⟩ := List.of_length_eq_of_append_eq_append
                (by simp [Range.length_toList]) A'''seq'
              rw [Range.map_eq_snoc_of_lt (Nat.succ_pos _), Nat.succ_sub_one] at A'''seq''
              let ⟨_, eq⟩ := List.of_length_eq_of_append_eq_append (by simp [Range.length_toList])
                A'''seq''
              cases eq
              rfl
            · case isFalse => exact Asn i mem
          ) (by
            congr
            rw [Range.map, ← Range.map_append (Nat.zero_le (m + 1)) (by
              apply Nat.succ_le.mpr
              apply Nat.succ_lt_succ_iff.mp
              rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, lengths_eq]
              linarith), ← Range.map, ← Range.map, ← List.singleton_append,
              ← List.append_assoc] at A'''seq'
            let ⟨A'''seq'', A'''seq'''⟩ := List.of_length_eq_of_append_eq_append
              (by simp [Range.length_toList]) A'''seq'
            rw [Range.map_eq_snoc_of_lt (Nat.succ_pos _), Nat.succ_sub_one] at A'''seq''
            let ⟨A'''seq'''', _⟩ := List.of_length_eq_of_append_eq_append
              (by simp [Range.length_toList]) A'''seq''
            rw [← A'''seq''', ← A'''seq'''']
            rw [Range.map, ← Range.map_append (Nat.zero_le m) (by linarith), ← Range.map,
                ← Range.map,
                Range.map_eq_of_eq_of_mem'' (fun i mem => if_neg (Nat.ne_of_lt mem.upper)),
                Range.map_eq_cons_of_lt (m := m) (by linarith),
                Range.map_eq_of_eq_of_mem''
                  (fun i mem => if_neg (Ne.symm (Nat.ne_of_lt (Nat.lt_of_add_one_le mem.lower))))]
            simp
          )
          rw [K?eq] at ih'
          convert ih'
          symm
          rw [Range.map, ← Range.map_append (m := m) (Nat.zero_le _) (by linarith), ← Range.map,
              ← Range.map, Range.map, Range.map_eq_cons_of_lt (by linarith), ← Range.map,
              if_pos rfl,
              Range.map_eq_of_eq_of_mem'' (fun i mem => if_neg (Nat.ne_of_lt mem.upper)),
              Range.map_eq_of_eq_of_mem''
                (fun i mem => if_neg (Ne.symm (Nat.ne_of_lt (Nat.lt_of_add_one_le mem.lower))))]
          rw [Range.map, ← Range.map_append (m := m) (Nat.zero_le _) (by linarith), ← Range.map,
              ← Range.map, Range.map, Range.map_eq_cons_of_lt (by linarith), ← Range.map] at A'''seq
          let ⟨A'''seq', A'''seq''⟩ := List.of_length_eq_of_append_eq_append (by simp) A'''seq
          rw [A'''seq', And.right <| List.cons.inj A'''seq'']

theorem list' (Asn : ∀ A ∈ As, [[SN(A)]]) : StronglyNormalizing (Type.list As K?) := by
  rw [← Range.map_get!_eq (as := As), ← Option.someIf_get!_eq (x? := K?)]
  apply list
  intro i mem
  exact Asn _ <| List.get!_mem mem.upper

theorem list_inversion' (h : StronglyNormalizing (Type.list As K?)) : ∀ A ∈ As, [[SN(A)]] := by
  intro A mem
  generalize A'eq : Type.list .. = A' at h
  induction h generalizing As A with
  | intro _ _ ih =>
    cases A'eq
    constructor
    intro B st
    rcases List.eq_append_cons_of_mem mem with ⟨A₀, A₂, rfl, nin⟩
    rw [← Range.map_get!_eq (as := A₀), ← Range.map_get!_eq (as := A₂),
        ← Option.someIf_get!_eq (x? := K?)] at ih
    apply ih _ st.list (As := A₀ ++ B :: A₂) _ <| List.mem_append.mpr <| .inr <| .head ..
    rw [Range.map_get!_eq, Range.map_get!_eq]

theorem app_inversion (ABsn : [[SN(A B)]]) : [[SN(A)]] ∧ [[SN(B)]] := by
  generalize Ceq : [[A B]] = C at ABsn
  induction ABsn generalizing A B with
  | intro _ _ ih =>
    cases Ceq
    constructor
    · constructor
      intro _ st
      exact ih _ (.appl st) rfl |>.left
    · constructor
      intro _ st
      exact ih _ (.appr st) rfl |>.right

theorem lam (ABsn : [[SN(A^^B)]]) (Alc : A.TypeVarLocallyClosed 1) (Bki : [[ε ⊢ B : K]])
  : [[SN(λ a : K. A)]] := by
  generalize Ceq : A.Type_open B = C at ABsn
  induction ABsn generalizing A with
  | intro _ ABsn' ih =>
    cases Ceq
    constructor
    intro _ st
    cases st with
    | eta A'ki =>
      let ABsn := Acc.intro _ ABsn'
      simp [Type.Type_open, A'ki.TypeVarLocallyClosed_of.Type_open_id] at ABsn
      exact app_inversion ABsn |>.left
    | lam I st' =>
      rename «Type» => A'
      let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
      let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
      let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
      specialize st' a aninI
      let st'' := st'.Type_open_in (Δ' := .empty) (B := B) Alc Bki (.typeVarExt .empty nofun) aninA
        aninA'
      apply ih _ st'' _ rfl
      apply Type.TypeVarLocallyClosed.Type_open_drop Nat.one_pos
      rw [← Type.Type_open_var]
      apply Type.TypeVarLocallyClosed.weaken (n := 1) <| st'.preserve_lc _
      rw [Type.Type_open_var]
      exact Type.TypeVarLocallyClosed.Type_open_dec Alc .var_free

theorem listApp_inversion (ABsn : [[SN(A ⟦B⟧)]]) : [[SN(A)]] ∧ [[SN(B)]] := by
  generalize Ceq : [[A ⟦B⟧]] = C at ABsn
  induction ABsn generalizing A B with
  | intro _ _ ih =>
    cases Ceq
    constructor
    · constructor
      intro _ st
      exact ih _ (.listAppl st) rfl |>.left
    · constructor
      intro _ st
      exact ih _ (.listAppr st) rfl |>.right

theorem not_lam_app (A_not_mst_lam : ∀ K A', ¬[[ε ⊢ A ->* λ a : K. A']])
  (Asn : [[SN(A)]]) (Bsn : [[SN(B)]]) : [[SN(A B)]] := by
  induction Asn generalizing B with
  | intro A' _ ihA =>
    induction Bsn with
    | intro B' B'sn ihB =>
      constructor
      intro C st
      rw [Rel.inv, flip] at st
      match st with
      | .lamApp .. =>
        nomatch A_not_mst_lam _ _ .refl
      | .appl A'st =>
        apply ihA _ A'st _ <| .intro _ B'sn
        intro K A'' mst
        exact A_not_mst_lam K A'' <| mst.head A'st
      | .appr B'st => exact ihB _ B'st

theorem prod (Asn : [[SN(A)]]) : [[SN(⊗ A)]] := by
  induction Asn with
  | intro _ _ ih =>
    constructor
    intro C st
    rw [Rel.inv, flip] at st
    let .prod Ast := st
    exact ih _ Ast

theorem sum (Asn : [[SN(A)]]) : [[SN(⊕ A)]] := by
  induction Asn with
  | intro _ _ ih =>
    constructor
    intro C st
    rw [Rel.inv, flip] at st
    let .sum Ast := st
    exact ih _ Ast

theorem to_In (Asn : [[SN(A)]]) (Aki : [[ε ⊢ A : K]]) : ∃ n, [[SN n (A)]] := by
  induction Asn with
  | intro A _ ih =>
    let ⟨Bs, eb⟩ := SmallStep.enumerably_branching Aki
    let ⟨Bns, eq, sn⟩ : ∃ Bns : List («Type» × Nat), Bns.map Prod.fst = Bs ∧
      ∀ Bn ∈ Bns, StronglyNormalizingIn Bn.snd Bn.fst := by
      generalize Cseq : Bs = Cs
      rw [Cseq] at eb
      rw [← Cseq]
      replace Cseq : ∃ C's, C's ++ Bs = Cs := ⟨[], by rw [Cseq]; exact List.nil_append _⟩
      induction Bs with
      | nil =>
        let ⟨_, Cseq'⟩ := Cseq
        rw [List.append_nil] at Cseq'
        cases Cseq'
        exact ⟨[], rfl, nofun⟩
      | cons B Bs' ih' =>
        let ⟨C's, Cseq'⟩ := Cseq
        let ⟨Bns', eq, sni'⟩ := ih' <| by
          refine ⟨C's ++ [B], ?_⟩
          rw [List.append_assoc, List.singleton_append, Cseq']
        let st : [[ε ⊢ A -> B]] := by
          apply eb.mp
          rw [← Cseq']
          apply List.mem_append.mpr
          exact .inr <| .head ..
        let ⟨n, sni⟩ := ih B st (st.preservation Aki)
        refine ⟨(B, n) :: Bns', ?_, ?_⟩
        · rw [List.map_cons, eq]
        · rintro ⟨B', n'⟩ mem
          cases mem with
          | head => exact sni
          | tail _ mem' => exact sni' _ mem'
    refine ⟨_, .intro Bns ?_ sn⟩
    intro B
    constructor
    · rintro ⟨_, mem⟩
      apply eb.mp
      rw [← eq]
      exact List.mem_map.mpr ⟨_, mem, rfl⟩
    · intro st
      let mem := eb.mpr st
      rw [← eq] at mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      exact ⟨_, mem'⟩

theorem of_In (Asni : [[SN n (A)]]) : [[SN(A)]] := by
  induction Asni with
  | intro _ eb _ ih =>
    constructor
    intro B st
    let ⟨_, mem⟩ := eb.mpr st
    exact ih (_, _) mem

end StronglyNormalizing

namespace MultiSmallStepIn

theorem list
  : [[Δ ⊢i A₁ ->* A₁']] →
    [[Δ ⊢i {</ A₀@i // i in [:m] />, A₁, </ A₂@j // j in [:n] /> </ : K // b />} ->* {</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] /> </ : K // b />}]] :=
  Relation.IndexedReflTransGen.map (r := SmallStep Δ) <| .list (A₀ := A₀) (A₂ := A₂)

theorem list' {m : Nat → Nat} (Amsti : ∀ i ∈ [:n], [[Δ ⊢(m i) A@i ->* A'@i]])
  : [[Δ ⊢(([:n].map m).sum) {</ A@i // i in [:n] /> </ : K // b />} ->* {</ A'@i // i in [:n] /> </ : K // b />}]] := by
  rw (occs := .pos [1]) [Range.map]
  rw (occs := .pos [2]) [Range.map]
  rw [← Range.map, ← Range.map_append (Nat.zero_le _) Nat.le.refl,
      Range.map_eq_of_eq_of_mem (m := n) (by
    intro i mem
    show A' i = A i
    nomatch Nat.not_le_of_lt mem.upper mem.lower
  ), ← Range.map, ← Range.map]
  generalize oeq : n = o
  rw (occs := .pos [2, 5]) [← oeq]
  let ole := Nat.le_refl o
  rw (occs := .pos [2]) [← oeq] at ole
  clear oeq
  induction o with
  | zero => rw [Range.map_same_eq_nil, List.sum_nil, Range.map_same_eq_nil, List.nil_append]
  | succ o' ih =>
    rw [Range.map_eq_snoc_of_lt (Nat.succ_pos _), Nat.succ_sub_one, List.sum_append,
        List.sum_singleton]
    apply ih (Nat.le_of_succ_le ole) |>.trans
    rw [Range.map_eq_cons_of_lt (Nat.lt_of_succ_le ole), Range.map_eq_snoc_of_lt (Nat.succ_pos _),
        Nat.succ_sub_one, List.append_assoc, List.singleton_append,
        ← Range.map_shift (j := o' + 1) Nat.le.refl, Nat.sub_self]
    exact list <| Amsti o' ⟨Nat.zero_le _, Nat.lt_of_succ_le ole, Nat.mod_one _⟩

theorem listApp : [[Δ ⊢i A ->* A']] → [[Δ ⊢j B ->* B']] → [[Δ ⊢(i + j) A ⟦B⟧ ->* A' ⟦B'⟧]] :=
  Relation.IndexedReflTransGen.map₂ .listAppl .listAppr

end MultiSmallStepIn

namespace StronglyNormalizingIn

theorem preservation (Asni : [[SN n (A)]]) (Ast : [[ε ⊢ A -> B]]) : ∃ m, [[SN m (B)]] ∧ m < n := by
  let .intro Bns eb sni := Asni
  let ⟨n, mem⟩ := eb.mpr Ast
  refine ⟨_, sni _ mem, ?_⟩
  clear eb sni
  induction Bns with
  | nil => nomatch mem
  | cons _ _ ih =>
    rw [List.map, List.max?_cons, Option.map, Option.getD, Option.elim.eq_def]
    split
    · case _ h =>
      cases mem with
      | head => exact Nat.lt_succ_of_le <| Nat.le_max_left ..
      | tail _ mem' =>
        specialize ih mem'
        rw [h, Option.map, Option.getD] at ih
        apply Nat.lt_succ_of_le
        simp_arith
        exact .inr <| Nat.le_of_lt_succ ih
    · case _ h =>
      cases List.map_eq_nil_iff.mp <| List.max?_eq_none_iff.mp h
      cases List.mem_singleton.mp mem
      exact Nat.le.refl

theorem MultiStep_preservation (Asni : [[SN n (A)]]) (Amst : [[ε ⊢ A ->* B]])
  : ∃ m, [[SN m (B)]] ∧ m ≤ n := by
  induction Amst with
  | refl => exact ⟨_, Asni, Nat.le.refl⟩
  | tail _ st ih =>
    let ⟨_, sni', le⟩ := ih
    let ⟨_, sni, lt⟩ := preservation sni' st
    exact ⟨_, sni, Nat.le_of_lt <| Nat.lt_of_lt_of_le lt le⟩

theorem to_MultiStepIn (Asni : [[SN n (A)]]) : ∃ B, [[ε ⊢n A ->* B]] := by
  let .intro Bns eb sni := Asni
  match Bns with
  | [] => exact ⟨_, .refl⟩
  | Bn :: Bns' =>
    let ne_none : List.max? (List.map Prod.snd (Bn :: Bns')) ≠ none := by
      intro eq
      rw [List.map_cons] at eq
      nomatch List.max?_eq_none_iff.mp eq
    let ⟨n, eq⟩ := Option.isSome_iff_exists.mp <|
      not_not.mp (ne_none <| Option.not_isSome_iff_eq_none.mp ·)
    rw [eq, Option.map, Option.getD]
    let mem := List.max?_mem (by simp [Nat.le_total]) eq
    rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
    let ⟨_, msti⟩ := sni _ mem' |>.to_MultiStepIn
    exact ⟨_, msti.head <| eb.mp ⟨_, mem'⟩⟩
termination_by n
decreasing_by
  let le := List.le_max?_getD_of_mem mem (k := 0)
  rw [eq] at le ⊢
  rw [Option.map]
  rw [Option.getD] at le ⊢
  exact Nat.lt_succ_of_le le

theorem In_le_of_MultiStepIn (Asni : [[SN n (A)]]) (Amsti : [[ε ⊢m A ->* B]]) : m ≤ n := by
  rcases Amsti.cases_head with ⟨rfl, rfl⟩ | ⟨_, _, rfl, st, msti'⟩
  · exact Nat.zero_le _
  · let .intro Bns eb sni := Asni
    let ⟨_, mem⟩ := eb.mpr st
    let le := sni _ mem |>.In_le_of_MultiStepIn msti'
    let ⟨n, eq⟩ := Option.isSome_iff_exists.mp <|
      List.isSome_max?_of_mem (l := List.map Prod.snd Bns) <| List.mem_map.mpr ⟨_, mem, rfl⟩
    let le' := List.le_max?_getD_of_mem (l := List.map Prod.snd Bns) (k := 0) <|
      List.mem_map.mpr ⟨_, mem, rfl⟩
    rw [eq] at le' ⊢
    rw [Option.map]
    rw [Option.getD] at le' ⊢
    apply Nat.succ_le_succ
    exact le.trans le'

theorem deterministic (Asni₀ : [[SN m (A)]]) (Asni₁ : [[SN n (A)]]) : m = n := by
  let .intro _ eb₀ sni₀ := Asni₀
  let .intro _ eb₁ sni₁ := Asni₁
  apply congrArg <| (Option.map _ · |>.getD 0)
  apply List.max?_eq_of_subset
  · intro _ mem
    rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
    let ⟨_, mem''⟩ := eb₁.mpr <| eb₀.mp ⟨_, mem'⟩
    specialize sni₀ _ mem'
    specialize sni₁ _ mem''
    simp at sni₁
    cases sni₀.deterministic sni₁
    exact List.mem_map.mpr ⟨_, mem'', rfl⟩
  · intro _ mem
    rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
    let ⟨_, mem''⟩ := eb₀.mpr <| eb₁.mp ⟨_, mem'⟩
    specialize sni₀ _ mem''
    specialize sni₁ _ mem'
    simp at sni₀
    cases sni₀.deterministic sni₁
    exact List.mem_map.mpr ⟨_, mem'', rfl⟩
termination_by m
decreasing_by
  all_goals simp_arith
  · apply Option.lt_getD
    · intro _ eq
      rcases Option.map_eq_some.mp eq with ⟨_, eq', rfl⟩
      apply Nat.lt_succ_of_le
      apply List.max?_eq_some_iff Nat.le_refl Nat.max_eq_or Nat.max_le_iff |>.mp eq' |>.right
      exact mem
    · intro eq
      rw [List.max?_eq_none_iff.mp <| Option.map_eq_none.mp eq] at mem
      cases mem
  · apply Option.lt_getD
    · intro _ eq
      rcases Option.map_eq_some.mp eq with ⟨_, eq', rfl⟩
      apply Nat.lt_succ_of_le
      apply List.max?_eq_some_iff Nat.le_refl Nat.max_eq_or Nat.max_le_iff |>.mp eq' |>.right
      exact List.mem_map.mpr ⟨_, mem'', rfl⟩
    · intro eq
      cases List.map_eq_nil_iff.mp <| List.max?_eq_none_iff.mp <| Option.map_eq_none.mp eq
      cases mem''

theorem list_inversion (Asni : [[SN i ({</ A@i // i in [:n] /> </ : K // b />})]])
  (Aki : ∀ i ∈ [:n], [[ε ⊢ A@i : K]])
  : ∃ m : Nat → Nat, (∀ i ∈ [:n], [[SN (m i) (A@i)]]) ∧ ([:n].map m).sum ≤ i := by
  let Asn i mem := (StronglyNormalizing.list_inversion' <| StronglyNormalizing.of_In Asni) (A i) <|
    Range.mem_map_of_mem mem
  let ⟨m, sni⟩ := Range.skolem (fun i mem => Asn i mem |>.to_In <| Aki i mem)
  let ⟨_, msti⟩ := Range.skolem (sni · · |>.to_MultiStepIn)
  exact ⟨m, sni, In_le_of_MultiStepIn Asni <| MultiSmallStepIn.list' msti⟩

theorem listApp_inversion (ABsni : [[SN n (A ⟦B⟧)]]) (Aki : [[ε ⊢ A : K₁ ↦ K₂]])
  (Bki : [[ε ⊢ B : L K₁]]) : ∃ i j, [[SN i (A)]] ∧ [[SN j (B)]] ∧ i + j ≤ n := by
  let ⟨Asn, Bsn⟩ := StronglyNormalizing.of_In ABsni |>.listApp_inversion
  let ⟨_, Asni⟩ := Asn.to_In Aki
  let ⟨_, Bsni⟩ := Bsn.to_In Bki
  refine ⟨_, _, Asni, Bsni, ?_⟩
  let ⟨_, Amsti⟩ := Asni.to_MultiStepIn
  let ⟨_, Bmsti⟩ := Bsni.to_MultiStepIn
  exact In_le_of_MultiStepIn ABsni <| .listApp Amsti Bmsti

end StronglyNormalizingIn

judgement_syntax "SN" K "(" A ")" : IndexedStronglyNormalizing

mutual

abbrev IndexedStronglyNormalizing : Kind → «Type» → Prop
  | [[*]], A => [[ε ⊢ A : *]] ∧ [[SN(A)]]
  | [[K₁ ↦ K₂]], A => [[ε ⊢ A : K₁ ↦ K₂]] ∧ ∀ B, [[SN K₁ (B)]] → [[SN K₂ (A B)]]
  | [[L K]], A =>
    [[ε ⊢ A : L K]] ∧ (StronglyNormalizingToList (fun B => [[SN K (B)]])) A ∧
      ∀ A' B' K', [[ε ⊢ A ->* A' ⟦B'⟧]] → [[ε ⊢ A' : K' ↦ K]] →
        ∃ C, [[ε ⊢ C : K']] ∧ [[SN(C)]] ∧ [[SN K (A' C)]]

end

nosubst
nonterminal Subst, δ :=
  | "ε"              : empty
  | δ ", " A " / " a : ext (id a)

namespace Subst

def find? (δ : Subst) (a : TypeVarId) : Option «Type» := match δ with
  | .empty => none
  | .ext δ' A a' => if a = a' then A else find? δ' a

def apply (δ : Subst) : «Type» → «Type»
  | .var a => match a with
    | .bound n => .var <| .bound n
    | .free a => if let some A := δ.find? a then
        A
      else
        .var <| .free a
  | .lam K A => .lam K <| apply δ A
  | .app A B => .app (apply δ A) (apply δ B)
  | .forall K A => .forall K <| apply δ A
  | .arr A B => .arr (apply δ A) (apply δ B)
  | .list As K? => .list (As.mapMem fun A _ => apply δ A) K?
  | .listApp A B => .listApp (apply δ A) (apply δ B)
  | .prod A => .prod <| apply δ A
  | .sum A => .sum <| apply δ A

instance : CoeFun Subst (fun _ => «Type» → «Type») where
  coe := Subst.apply

def «dom» : Subst → List TypeVarId
  | .empty => []
  | .ext δ _ a => a :: δ.dom

def freeTypeVars : Subst → List TypeVarId
  | .empty => []
  | .ext δ A _ => A.freeTypeVars ++ δ.freeTypeVars

end Subst

judgement_syntax δ " ⊨ " Δ : SubstSatisfies

judgement SubstSatisfies := fun (δ : Subst) Δ => δ.dom.Unique ∧ δ.dom = Δ.typeVarDom ∧
    ∀ a K, [[a : K ∈ Δ]] → IndexedStronglyNormalizing K (δ (Type.var a))

theorem IndexedStronglyNormalizing.to_Kinding (Aisn : [[SN K (A)]]) : [[ε ⊢ A : K]] := by
  cases K <;> rw [IndexedStronglyNormalizing] at Aisn <;> exact Aisn.left

namespace «Type»

def with_Kind : Kind → «Type»
  | [[*]] => .prod <| .list [] <| some [[*]]
  | [[K₁ ↦ K₂]] =>
    let A := with_Kind K₂
    [[λ a : K₁. A]]
  | [[L K']] => .list [] <| some K'

namespace with_Kind

theorem TypeVarLocallyClosed : TypeVarLocallyClosed (with_Kind K) := by
  match K with
  | [[*]] => exact .prod <| .list nofun
  | [[K₁ ↦ K₂]] => exact .lam <| with_Kind.TypeVarLocallyClosed.weaken (n := 1)
  | [[L K']] => exact .list nofun

theorem not_mem_freeTypeVars : a ∉ freeTypeVars (with_Kind K) := by
  induction K <;> aesop (add simp [freeTypeVars, with_Kind])

theorem freeTypeVars_eq_nil : freeTypeVars (with_Kind K) = [] := by
  induction K <;> aesop (add simp [freeTypeVars, with_Kind])

theorem IsValue : IsValue (with_Kind K) := by
  match K with
  | [[*]] => exact .unit
  | [[K₁ ↦ K₂]] =>
    rw [with_Kind]
    refine .lam [] ?_ ?_
    · intro a anin
      rw [with_Kind.TypeVarLocallyClosed.TypeVar_open_id]
      exact with_Kind.IsValue
    · cases K₂ <;> rw [with_Kind] <;> nofun
  | [[L K']] => exact .empty_list

theorem Kinding : Kinding Δ (with_Kind K) K := by
  match K with
  | [[*]] => exact .unit
  | [[K₁ ↦ K₂]] =>
    rw [with_Kind]
    apply Kinding.lam []
    intros
    rw [with_Kind.TypeVarLocallyClosed.TypeVar_open_id]
    exact Kinding
  | [[L K']] => exact .empty_list

end with_Kind

end «Type»

theorem StronglyNormalizing.forall (ABsn : [[SN(A^^B)]]) (ABki : [[ε ⊢ A^^B : *]])
  (Bki : [[ε ⊢ B : K]]) : [[SN(∀ a : K. A)]] :=
  let ⟨_, ABsni⟩ := to_In ABsn ABki
  go ABsni <| ABki.TypeVarLocallyClosed_of.weaken (n := 1).Type_open_drop Nat.one_pos
where
  go {A n} (ABsni : [[SN n (A^^B)]]) (Alc : A.TypeVarLocallyClosed 1) : [[SN(∀ a : K. A)]] := by
    constructor
    intro _ st
    cases st
    case «forall» A' I st' =>
    let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
    specialize st' a aninI
    let st'' := st'.Type_open_in Alc Bki (.typeVarExt .empty nofun) aninA aninA' (Δ' := .empty)
    replace Alc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var] at Alc
    let A'lc := st'.preserve_lc Alc
    replace A'lc := A'lc.weaken (n := 1) |>.TypeVar_open_drop Nat.one_pos
    rw [Environment.TypeVar_subst, Environment.append] at st''
    let ⟨_, A'Bsni, _⟩ := ABsni.preservation st'' (B := A'.Type_open B)
    exact go A'Bsni A'lc

namespace StronglyNormalizingToList

theorem preservation (Asntl : StronglyNormalizingToList P A) (Ast : [[ε ⊢ A -> B]])
  (P_preservation : ∀ {A' B'}, P A' → [[ε ⊢ A' -> B']] → P B') : StronglyNormalizingToList P B := by
  cases Asntl with
  | refl h =>
    let .list A₁st := Ast
    apply refl
    intro A mem
    cases List.mem_append.mp mem with
    | inl mem =>
      exact h _ <| List.mem_append.mpr <| .inl mem
    | inr mem => cases mem with
      | head =>
        apply P_preservation _ A₁st
        exact h _ <| List.mem_append.mpr <| .inr <| .head ..
      | tail _ mem => exact h _ <| List.mem_append.mpr <| .inr <| .tail _ mem
  | step h nv => exact h _ Ast

theorem imp (Asntl : StronglyNormalizingToList P A) (imp : ∀ {B}, P B → Q B)
  : StronglyNormalizingToList Q A := by
  induction Asntl with
  | refl h => exact .refl (imp <| h · ·)
  | step _ ne ih => exact .step (ih · ·) ne

theorem imp' (Asntl : StronglyNormalizingToList P A)
  (imp : ∀ {Bs K? B}, MultiSmallStep .empty A (.list Bs K?) → B ∈ Bs → P B → Q B)
  : StronglyNormalizingToList Q A := by
  induction Asntl with
  | refl h =>
    refine .refl ?_
    intro _ mem
    exact imp .refl mem <| h _ mem
  | step _ ne ih =>
    refine .step ?_ ne
    intro _ st
    apply ih _ st
    intro _ _ _ mst
    apply imp
    exact .head st mst

end StronglyNormalizingToList

namespace IndexedStronglyNormalizing

theorem preservation (Aisn : [[SN K (A)]]) (Ast : [[ε ⊢ A -> B]]) : [[SN K (B)]] := by
  cases K <;> rw [IndexedStronglyNormalizing] at Aisn ⊢
  case star =>
    let ⟨Aki, Asn⟩ := Aisn
    exact ⟨Ast.preservation Aki, Asn.preservation Ast⟩
  case arr =>
    let ⟨Aki, h⟩ := Aisn
    refine ⟨Ast.preservation Aki, ?_⟩
    intro B' B'isn
    exact h B' B'isn |>.preservation <| .appl Ast
  case list =>
    let ⟨Aki, h₀, h₁⟩ := Aisn
    refine ⟨Ast.preservation Aki, StronglyNormalizingToList.preservation h₀ Ast preservation, ?_⟩
    intro _ _ _ mst
    exact h₁ _ _ _ <| .head Ast mst

theorem MultiStep_preservation (Aisn : [[SN K (A)]]) (Ast : [[ε ⊢ A ->* B]]) : [[SN K (B)]] := by
  induction Ast with
  | refl => exact Aisn
  | tail _ st ih => exact preservation ih st

end IndexedStronglyNormalizing

theorem Type.Neutral.app : Neutral [[A B]] := by
  rw [Neutral]
  exact ⟨nofun, nofun, nofun⟩

mutual

theorem Type.with_Kind.IndexedStronglyNormalizing
  : IndexedStronglyNormalizing K (Type.with_Kind K) := by
  open «Type» in
  open Type.with_Kind in
  match K with
  | [[*]] => exact ⟨with_Kind.Kinding, .intro _ fun _ st => nomatch IsValue.not_step IsValue st⟩
  | [[K₁ ↦ K₂]] =>
    let h := Type.with_Kind.IndexedStronglyNormalizing (K := K₂)
    refine ⟨with_Kind.Kinding, ?_⟩
    intro _ Bisn
    induction StronglyNormalizing.of_Indexed Bisn with
    | intro _ _ ih =>
      apply IndexedStronglyNormalizing.preservation_rev .app _ <|
        .app with_Kind.Kinding Bisn.to_Kinding
      intro _ st
      cases st with
      | lamApp =>
        rw [with_Kind.TypeVarLocallyClosed.Type_open_id]
        exact h
      | appl Ast => nomatch IsValue.not_step IsValue Ast
      | appr Bst => exact ih _ Bst <| Bisn.preservation Bst
  | [[L K']] =>
    rw [IndexedStronglyNormalizing]
    refine ⟨with_Kind.Kinding, .refl nofun, ?_⟩
    intro _ _ _ mst
    nomatch mst.eq_of_IsValue with_Kind.IsValue
termination_by (sizeOf K, 0)
decreasing_by
  all_goals (
    apply Prod.Lex.left
    simp_arith
  )

theorem IndexedStronglyNormalizing.preservation_rev (An : A.Neutral)
  (h : ∀ B, [[ε ⊢ A -> B]] → [[SN K (B)]]) (Aki : [[ε ⊢ A : K]]) : [[SN K (A)]] := by
  open IndexedStronglyNormalizing in
  rw [Type.Neutral] at An
  match K with
  | [[*]] =>
    rw [IndexedStronglyNormalizing]
    refine ⟨Aki, ?_⟩
    apply StronglyNormalizing.preservation_rev
    intro A' st
    exact .of_Indexed <| h A' st
  | [[K₁ ↦ K₂]] =>
    rw [IndexedStronglyNormalizing]
    refine ⟨Aki, ?_⟩
    intro B' B'isn
    induction StronglyNormalizing.of_Indexed B'isn with
    | intro _ _ ih =>
      apply IndexedStronglyNormalizing.preservation_rev .app _ <| .app Aki B'isn.to_Kinding
      intro _ st
      cases st with
      | lamApp => nomatch An.left _ _
      | appl A'st =>
        specialize h _ A'st
        rw [IndexedStronglyNormalizing] at h
        exact h.right _ B'isn
      | appr B'st => exact ih _ B'st <| preservation B'isn B'st
  | [[L K']] =>
    rw [IndexedStronglyNormalizing]
    refine ⟨Aki, ?_, ?_⟩
    · by_cases ∃ As K?, A = Type.list As K?
      · case pos h =>
        rcases h with ⟨As, K?, rfl⟩
        refine .refl ?_
        rw [← Range.map_get!_eq (as := As)] at An Aki h ⊢
        rw [← Option.someIf_get!_eq (x? := K?)] at An Aki h
        intro _ mem
        rcases Range.mem_of_mem_map mem with ⟨i, mem', rfl⟩
        apply IndexedStronglyNormalizing.preservation_rev (An.right.left _ _ _ _ (.refl _) _ mem') _
          (Aki.inv_list.left _ mem')
        intro _ st
        rw [Range.map, ← Range.map_append (Nat.zero_le _) mem'.upper.le, ← Range.map,
            ← Range.map, Range.map_eq_cons_of_lt mem'.upper,
            ← Range.map_shift (m := i + 1) Nat.le.refl, Nat.sub_self] at h
        cases h _ (.list st) |>.right.left with
        | refl h => exact h _ <| List.mem_append.mpr <| .inr <| .head ..
        | step _ ne => nomatch ne _ _
      · case neg ne => exact .step (h · · |>.right.left) (not_exists.mp <| not_exists.mp ne ·)
    · intro A' B K'' mst
      rcases Relation.ReflTransGen.cases_head mst with rfl | ⟨_, st, mst'⟩
      · nomatch An.right.right _ _
      · exact h _ st |>.right.right _ _ _ mst'
termination_by (sizeOf K, 1)
decreasing_by
  · exact Prod.Lex.right _ Nat.one_pos
  · apply Prod.Lex.left
    simp_arith
  · apply Prod.Lex.left
    simp_arith
  · apply Prod.Lex.left
    simp_arith

theorem StronglyNormalizing.of_Indexed (Aisn : [[SN K (A)]]) : [[SN(A)]] := by
  open StronglyNormalizing in
  cases K with
  | star => exact Aisn.right
  | arr K₁ =>
    rw [IndexedStronglyNormalizing] at Aisn
    let ⟨Asn, _⟩ := app_inversion <| StronglyNormalizing.of_Indexed <|
      Aisn.right (Type.with_Kind K₁) Type.with_Kind.IndexedStronglyNormalizing
    exact Asn
  | list =>
    rw [IndexedStronglyNormalizing] at Aisn
    replace Aisn := Aisn.right.left
    induction Aisn with
    | refl h => exact list' (.of_Indexed <| h · ·)
    | step _ _ ih =>
      constructor
      intro _ st
      exact ih _ st
termination_by (sizeOf K, 0)
decreasing_by
  all_goals (
    rename K = _ => eq
    cases eq
    apply Prod.Lex.left
    simp_arith
  )

end

theorem Type.with_Kind.StronglyNormalizing : StronglyNormalizing (with_Kind K) :=
  .of_Indexed IndexedStronglyNormalizing

namespace Subst

theorem apply_empty_id : apply empty A = A := by
  induction A using Type.rec_uniform <;> aesop (add simp [Subst.apply, find?], safe cases TypeVar)

theorem find?_eq_none_of_not_mem (anin : a ∉ «dom» δ) : find? δ a = none := by
  induction δ with
  | empty => rw [find?]
  | ext _ _ _ ih =>
    let ⟨ane, anin'⟩ := List.not_mem_cons.mp anin
    rw [find?, if_neg ane, ih anin']

theorem mem_of_find?_eq_some (eq : find? δ a = some A) : a ∈ «dom» δ := by
  induction δ with
  | empty =>
    rw [find?] at eq
    nomatch eq
  | ext _ _ _ ih =>
    rw [find?] at eq
    split at eq
    · case isTrue h =>
      cases h
      exact .head _
    · case isFalse h => exact .tail _ <| ih eq

theorem not_mem_freeTypeVars_of_find?_eq_some (anin : a ∉ freeTypeVars δ) (eq : find? δ a' = some A)
  : a ∉ A.freeTypeVars := by
  induction δ with
  | empty =>
    rw [find?] at eq
    nomatch eq
  | ext _ _ _ ih =>
    rw [freeTypeVars] at anin
    rw [find?] at eq
    split at eq
    · case isTrue h =>
      cases h
      cases eq
      exact List.not_mem_append'.mp anin |>.left
    · case isFalse h =>
      let ⟨_, anin'⟩ := List.not_mem_append'.mp anin
      exact ih anin' eq

theorem apply_var_id_of_not_mem (anin : a ∉ «dom» δ) : δ (.var (.free a)) = .var a := by
  rw [apply, find?_eq_none_of_not_mem anin]

theorem apply_eq_id_of_freeTypeVars_disjoint_dom
  (dj : List.Disjoint (Type.freeTypeVars A) («dom» δ)) : δ A = A := by
  induction A using Type.rec_uniform
  case var a =>
    cases a with
    | free =>
      apply apply_var_id_of_not_mem <| dj _
      simp [Type.freeTypeVars]
    | bound => rw [apply]
  case list ih =>
    rw [apply, List.mapMem_eq_map]
    apply Type.list.injEq .. |>.mpr ⟨_, rfl⟩
    apply List.map_eq_id_of_eq_id_of_mem
    intro A mem
    apply ih _ mem
    intro a mem'
    apply dj
    rw [Type.freeTypeVars, List.mapMem_eq_map]
    exact List.mem_flatten_of_mem (List.mem_map.mpr ⟨_, mem, rfl⟩) mem'
  all_goals aesop (add simp [Type.freeTypeVars, «dom», Subst.apply])

theorem not_mem_freeTypeVars_apply (aninA : a ∉ A.freeTypeVars) (aninδ : a ∉ freeTypeVars δ)
  : a ∉ Type.freeTypeVars (δ A) := by
  induction A using Type.rec_uniform
  case var a' =>
    match a' with
    | .free a' =>
      rw [apply]
      split
      · case _ h => exact not_mem_freeTypeVars_of_find?_eq_some aninδ h
      · case _ => exact aninA
    | .bound _ =>
      rw [apply]
      exact aninA
  all_goals aesop (add simp [Subst.apply, Type.TypeVar_subst, Type.freeTypeVars])

theorem apply_ext_eq_TypeVar_subst_apply (uni : (ext δ A a).dom.Unique) (anin : a ∉ freeTypeVars δ)
  : ext δ A a B = (δ B).TypeVar_subst a A := by
  induction B using Type.rec_uniform
  case var a' =>
    match a' with
    | .free a' =>
      rw [Subst.apply]
      split
      · case _ h =>
        rw [find?] at h
        split at h
        · case isTrue h' =>
          cases h'
          rw [«dom»] at uni
          cases h
          let .cons anin _ := uni
          rw [apply_var_id_of_not_mem anin, Type.TypeVar_subst, if_pos rfl]
        · case isFalse h' =>
          rw [apply, h]
          conv => simp_match
          rw [Type.TypeVar_subst_id_of_not_mem_freeTypeVars <|
                not_mem_freeTypeVars_of_find?_eq_some anin h]
      · case _ h =>
        rw [Subst.apply]
        split
        · case _ h' =>
          rename «Type» => A'
          exfalso
          apply h <| if a = a' then A else A'
          rw [find?]
          split
          · case isTrue h'' =>
            cases h''
            rw [«dom»] at uni
            rw [if_pos rfl]
          · case isFalse h'' =>
            rw [if_neg (Ne.symm h'')]
            exact h'
        · case _ =>
          rw [Type.TypeVar_subst]
          split
          · case isTrue h' =>
            cases h'
            rw [find?, if_pos rfl] at h
            nomatch h _
          · case isFalse => rfl
    | .bound _ =>
      rw [Subst.apply, Subst.apply, Type.TypeVar_subst, if_neg nofun]
  all_goals aesop (add simp [Subst.apply, Type.TypeVar_subst])

def synthetic : Environment → Subst
  | .empty => .empty
  | .typeExt Δ a K => synthetic Δ |>.ext (Type.with_Kind K) a
  | .termExt Δ .. => synthetic Δ

theorem synthetic.not_mem_freeTypeVars : a ∉ freeTypeVars (synthetic Δ) := by
  induction Δ with
  | empty => nofun
  | typeExt _ _ _ ih =>
    rw [synthetic, freeTypeVars]
    exact List.not_mem_append'.mpr ⟨Type.with_Kind.not_mem_freeTypeVars, ih⟩
  | termExt _ _ _ ih =>
    rw [synthetic]
    exact ih

end Subst

namespace SubstSatisfies

theorem TypeVar_ext (δsat : [[δ ⊨ Δ]]) (aninδd : a ∉ δ.dom) (aninδfv : a ∉ δ.freeTypeVars)
  (Aisn : [[SN K (A)]]) : [[δ, A / a ⊨ Δ, a : K]] := by
  refine ⟨
    δsat.left.cons aninδd,
    List.cons.injEq .. |>.mpr ⟨rfl, δsat.right.left⟩,
    ?_
  ⟩
  intro a' K' a'K'inΔa
  cases a'K'inΔa with
  | head =>
    rw [Subst.apply, Subst.find?, if_pos rfl]
    conv => simp_match
    exact Aisn
  | typeVarExt a'K'inΔ ane =>
    rw [Subst.apply_ext_eq_TypeVar_subst_apply (.cons aninδd δsat.left) aninδfv,
        Type.TypeVar_subst_id_of_not_mem_freeTypeVars <| Subst.not_mem_freeTypeVars_apply _ aninδfv]
    · exact δsat.right.right a' K' a'K'inΔ
    · rw [Type.freeTypeVars]
      exact List.not_mem_singleton.mpr ane.symm

theorem TermVar_ext (δsat : [[δ ⊨ Δ]]) : [[δ ⊨ Δ, x : A]] := ⟨
    δsat.left,
    δsat.right.left,
    fun _ _ aKin => let .termVarExt aKin' := aKin; δsat.right.right _ _ aKin'
  ⟩

theorem TermVar_drop (δsat : [[δ ⊨ Δ, x : A]]) : [[δ ⊨ Δ]] := ⟨
    δsat.left,
    δsat.right.left,
    fun _ _ aKin => δsat.right.right _ _ <| .termVarExt aKin
  ⟩

theorem empty : [[ε ⊨ ε]] := ⟨.nil, rfl, nofun⟩

theorem empty_inversion (δsat : [[δ ⊨ ε]]) : δ = .empty :=
  match δ with
  | .empty => rfl
  | .ext .. => nomatch δsat.right.left

theorem synthetic (Δwf : [[⊢ Δ]]) : SubstSatisfies (Subst.synthetic Δ) Δ := by
  induction Δwf with
  | empty => exact empty
  | typeVarExt _ anin ih =>
    let ⟨uni, eq, isn⟩ := ih
    rw [Environment.TypeVarNotInDom, Environment.TypeVarInDom, ← eq] at anin
    let uni' := uni.cons anin
    refine ⟨uni', List.cons.injEq .. |>.mpr ⟨rfl, eq⟩, ?_⟩
    intro _ _ aKin
    cases aKin with
    | head =>
      rw [Subst.synthetic,
          Subst.apply_ext_eq_TypeVar_subst_apply uni' Subst.synthetic.not_mem_freeTypeVars,
          Subst.apply_var_id_of_not_mem anin, Type.TypeVar_subst, if_pos rfl]
      exact Type.with_Kind.IndexedStronglyNormalizing
    | typeVarExt aKin' ane =>
      rw [Subst.synthetic,
          Subst.apply_ext_eq_TypeVar_subst_apply uni' Subst.synthetic.not_mem_freeTypeVars,
          Type.TypeVar_subst_id_of_not_mem_freeTypeVars]
      · exact isn _ _ aKin'
      · apply Subst.not_mem_freeTypeVars_apply _ Subst.synthetic.not_mem_freeTypeVars
        simp [Type.freeTypeVars, ane.symm]
  | termVarExt _ _ _ ih =>
    let ⟨uni, eq, isn⟩ := ih
    exact ⟨uni, eq, fun | _, _, .termVarExt aKin => isn _ _ aKin⟩

mutual

theorem apply_TypeVar_open_comm' (δsat : [[δ ⊨ Δ]]) (anin : a ∉ δ.dom)
  (a'in : ∀ a' ∈ A.freeTypeVars, [[a' ∈ dom(Δ)]])
  : δ (A.TypeVar_open a n) = (δ A).TypeVar_open a n := by
  induction A using Type.rec_uniform generalizing n
  case var a' =>
    rw [Type.TypeVar_open]
    split
    · case isTrue h =>
      cases h
      rw [Subst.apply_var_id_of_not_mem anin, Subst.apply, Type.TypeVar_open, if_pos rfl]
    · case isFalse h =>
      match a' with
      | .free _ =>
        rw [Subst.apply]
        split
        · case _ h' =>
          symm
          apply Type.TypeVarLocallyClosed.TypeVar_open_id
          let ⟨_, A'sin⟩ := of_eq h' <| a'in _ <| by simp [Type.freeTypeVars]
          let A'lc := A'sin.to_Kinding.TypeVarLocallyClosed_of.weaken (n := n)
          rw [Nat.zero_add] at A'lc
          exact A'lc
        · case _ h' =>
          rw [Type.TypeVar_open, if_neg nofun]
      | .bound _ => rw [Subst.apply, Type.TypeVar_open, if_neg h]
  all_goals aesop (add simp [Subst.apply, Type.TypeVar_open, Type.freeTypeVars])
where
  of_eq {a A} (eq : δ.find? a = some A) (ain : [[a ∈ dom(Δ)]])
    : ∃ K, [[SN K (A)]] := by
    let ⟨_, aKin⟩ := TypeVarInDom.TypeVarInEnvironment_of ain
    have := δsat.right.right _ _ aKin
    rw [Subst.apply, eq] at this
    exact ⟨_, this⟩

theorem preservation (δsat : [[δ ⊨ Δ]]) (Aki : [[Δ ⊢ A : K]]) : Kinding .empty (δ A) K := by
  induction Aki generalizing δ
  case var ain => exact δsat.right.right _ _ ain |>.to_Kinding
  case lam Δ K₁ A' _ I A'ki ih =>
    rw [Subst.apply]
    apply Kinding.lam <| A'.freeTypeVars ++ (δ A').freeTypeVars ++ I ++ δ.dom ++ δ.freeTypeVars ++
      Δ.typeVarDom
    intro a anin
    let ⟨aninA'δA'Iδdfv, aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA'δA'Iδd, aninδfv⟩ := List.not_mem_append'.mp aninA'δA'Iδdfv
    let ⟨aninA'δA'I, aninδd⟩ := List.not_mem_append'.mp aninA'δA'Iδd
    let ⟨aninA'δA', aninI⟩ := List.not_mem_append'.mp aninA'δA'I
    let ⟨aninA', aninδA'⟩ := List.not_mem_append'.mp aninA'δA'
    let δ'sat := δsat.TypeVar_ext aninδd aninδfv Type.with_Kind.IndexedStronglyNormalizing (K := K₁)
    specialize ih a aninI δ'sat
    apply Kinding.Type_open_preservation_rev _ Type.with_Kind.Kinding (.typeVarExt .empty nofun)
      (Δ' := .empty)
    rw [Subst.apply_ext_eq_TypeVar_subst_apply δ'sat.left aninδfv] at ih
    rw [apply_TypeVar_open_comm' δsat aninδd] at ih
    · rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninδA']
      exact ih
    · intro a' a'inA'
      by_cases a = a'
      · case pos h =>
        cases h
        nomatch aninA' a'inA'
      · case neg ane =>
        apply not_not.mp
        intro a'nin
        apply Type.not_mem_freeTypeVars_TypeVar_open_drop <|
          A'ki a aninI |>.not_mem_freeTypeVars_of <| List.not_mem_cons.mpr ⟨Ne.symm ane, a'nin⟩
        exact a'inA'
  case scheme Δ K₁ A' I A'ki ih =>
    rw [Subst.apply]
    apply Kinding.scheme <| A'.freeTypeVars ++ (δ A').freeTypeVars ++ I ++ δ.dom ++ δ.freeTypeVars ++
      Δ.typeVarDom
    intro a anin
    let ⟨aninA'δA'Iδdfv, aninΔ⟩ := List.not_mem_append'.mp anin
    let ⟨aninA'δA'Iδd, aninδfv⟩ := List.not_mem_append'.mp aninA'δA'Iδdfv
    let ⟨aninA'δA'I, aninδd⟩ := List.not_mem_append'.mp aninA'δA'Iδd
    let ⟨aninA'δA', aninI⟩ := List.not_mem_append'.mp aninA'δA'I
    let ⟨aninA', aninδA'⟩ := List.not_mem_append'.mp aninA'δA'
    let δ'sat := δsat.TypeVar_ext aninδd aninδfv Type.with_Kind.IndexedStronglyNormalizing (K := K₁)
    specialize ih a aninI δ'sat
    apply Kinding.Type_open_preservation_rev _ Type.with_Kind.Kinding (.typeVarExt .empty nofun)
      (Δ' := .empty)
    rw [Subst.apply_ext_eq_TypeVar_subst_apply δ'sat.left aninδfv] at ih
    rw [apply_TypeVar_open_comm' δsat aninδd] at ih
    · rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninδA']
      exact ih
    · intro a' a'inA'
      by_cases a = a'
      · case pos h =>
        cases h
        nomatch aninA' a'inA'
      · case neg ane =>
        apply not_not.mp
        intro a'nin
        apply Type.not_mem_freeTypeVars_TypeVar_open_drop <|
          A'ki a aninI |>.not_mem_freeTypeVars_of <| List.not_mem_cons.mpr ⟨Ne.symm ane, a'nin⟩
        exact a'inA'
  all_goals aesop (add simp Subst.apply, safe constructors Kinding)

end

theorem apply_TypeVar_open_comm (δsat : [[δ ⊨ Δ]]) (anin : a ∉ δ.dom)
  (Aki : [[Δ ⊢ A^a : K]]) : δ (A.TypeVar_open a n) = (δ A).TypeVar_open a n := by
  apply apply_TypeVar_open_comm' δsat anin
  intro a' a'inA
  apply not_not.mp
  intro a'nin
  apply Type.not_mem_freeTypeVars_TypeVar_open_drop <| Aki.not_mem_freeTypeVars_of a'nin
  exact a'inA

theorem apply_TypeVar_open_comm'' (δsat : [[δ ⊨ Δ]]) (aninδ : a ∉ δ.dom)
  (Aki : [[Δ, a : K' ⊢ A^a : K]]) (aninA : a ∉ A.freeTypeVars)
  : δ (A.TypeVar_open a n) = (δ A).TypeVar_open a n := by
  apply apply_TypeVar_open_comm' δsat aninδ
  intro a' a'inA
  apply not_not.mp
  intro a'nin
  by_cases a = a'
  · case pos h =>
    cases h
    nomatch aninA a'inA
  · case neg h =>
    apply Type.not_mem_freeTypeVars_TypeVar_open_drop <| Aki.not_mem_freeTypeVars_of <|
      List.not_mem_cons.mpr ⟨Ne.symm h, a'nin⟩
    exact a'inA

end SubstSatisfies

theorem Subst.apply_TypeVar_subst_comm (aninδd : a ∉ δ.dom) (aninδfv : a ∉ δ.freeTypeVars)
  (ninB : ∀ {a}, a ∉ B.freeTypeVars)
  : δ (A.TypeVar_subst a B) = (Subst.apply δ A).TypeVar_subst a B := by
  induction A using Type.rec_uniform
  case var a' =>
    rw [Type.TypeVar_subst]
    split
    · case isTrue h =>
      subst h
      rw [Subst.apply_var_id_of_not_mem aninδd, Type.TypeVar_subst, if_pos rfl,
          Subst.apply_eq_id_of_freeTypeVars_disjoint_dom (fun _ inB => nomatch ninB inB)]
    · case isFalse h =>
      rw [Type.TypeVar_subst_id_of_not_mem_freeTypeVars]
      apply Subst.not_mem_freeTypeVars_apply _ aninδfv
      cases a' with
      | free =>
        rw [Type.freeTypeVars]
        exact List.not_mem_singleton.mpr (nomatch h <| TypeVar.free.injEq .. |>.mpr ·)
      | bound =>
        rw [Type.freeTypeVars]
        nofun
  all_goals aesop (add simp [Subst.apply, Type.TypeVar_subst, Type.freeTypeVars])

theorem SubstSatisfies.synthetic_SmallStep_preservation (Δwf : [[⊢ Δ]])
  (Alc : A.TypeVarLocallyClosed) (Ast : [[Δ ⊢ A -> B]])
  : SmallStep .empty ((Subst.synthetic Δ) A) ((Subst.synthetic Δ) B) := by
  cases Δwf with
  | empty =>
    rw [Subst.synthetic, Subst.apply_empty_id, Subst.apply_empty_id]
    exact Ast
  | typeVarExt Δ'wf anin =>
    rename Kind => K
    let ⟨uni, eq, _⟩ := synthetic <| .typeVarExt Δ'wf anin (K := K)
    let anin' := by
      rw [Environment.TypeVarNotInDom, Environment.TypeVarInDom,
          ← And.right <| List.cons.inj eq] at anin
      exact anin
    rw [Subst.synthetic,
        Subst.apply_ext_eq_TypeVar_subst_apply uni Subst.synthetic.not_mem_freeTypeVars,
        Subst.apply_ext_eq_TypeVar_subst_apply uni Subst.synthetic.not_mem_freeTypeVars,
        ← Subst.apply_TypeVar_subst_comm anin' Subst.synthetic.not_mem_freeTypeVars
          Type.with_Kind.not_mem_freeTypeVars,
        ← Subst.apply_TypeVar_subst_comm anin' Subst.synthetic.not_mem_freeTypeVars
          Type.with_Kind.not_mem_freeTypeVars]
    exact synthetic_SmallStep_preservation Δ'wf
      (Alc.TypeVar_subst Type.with_Kind.TypeVarLocallyClosed) <|
      Ast.TypeVar_subst_in Alc (.typeVarExt Δ'wf anin) Type.with_Kind.Kinding (Δ' := .empty)
  | termVarExt Δ'wf =>
    rw [Subst.synthetic]
    exact synthetic_SmallStep_preservation Δ'wf Alc <| Ast.TermVar_drop (Δ' := .empty)

namespace IndexedStronglyNormalizing

def to_In (Aisn : [[SN K (A)]]) : ∃ n, [[SN n (A)]] :=
  StronglyNormalizing.of_Indexed Aisn |>.to_In Aisn.to_Kinding

theorem lam_app (AopBisn : [[SN K₂ (A^^B)]]) (Bki : [[ε ⊢ B : K₁]]) (Bsn : [[SN(B)]])
  : [[SN K₂ ((λ a : K₁. A) B)]] :=
  let ⟨_, AopBsni⟩ := AopBisn.to_In
  let ⟨_, Bsni⟩ := Bsn.to_In Bki
  go AopBisn AopBsni Bki Bsni
where
  go {A B m n} (AopBisn : [[SN K₂ (A^^B)]]) (AopBsni : [[SN m (A^^B)]]) (Bki : [[ε ⊢ B : K₁]])
    (Bsni : [[SN n (B)]]) : [[SN K₂ ((λ a : K₁. A) B)]] := by
    apply preservation_rev .app _ <| by
      apply Kinding.app _ Bki
      apply Kinding.lam []
      intro a anin
      exact AopBisn.to_Kinding.Type_open_preservation_rev Bki (.typeVarExt .empty nofun)
        (Δ' := .empty) (a := a)
    intro _ st
    cases st with
    | lamApp => exact AopBisn
    | appl Ast =>
      cases Ast with
      | eta Aki =>
        simp [Type.Type_open, Aki.TypeVarLocallyClosed_of.Type_open_id] at AopBisn
        exact AopBisn
      | lam I Ast' =>
        rename «Type» => A'
        let ⟨a, anin⟩ := A.freeTypeVars ++ A'.freeTypeVars ++ I |>.exists_fresh
        let ⟨aninAA', aninI⟩ := List.not_mem_append'.mp anin
        let ⟨aninA, aninA'⟩ := List.not_mem_append'.mp aninAA'
        let Alc := AopBisn.to_Kinding.TypeVarLocallyClosed_of.weaken (n := 1).Type_open_drop
          Nat.one_pos
        let st' := Ast' a aninI |>.Type_open_in Alc Bki (.typeVarExt .empty nofun) aninA aninA'
          (Δ' := .empty)
        let ⟨_, A'opBsni, _⟩ := AopBsni.preservation st'
        exact go (AopBisn.preservation st') A'opBsni Bki Bsni
    | appr Bst =>
      rename «Type» => B'
      let mst : [[ε ⊢ A^^B ->* A^^B']] := by
        apply SmallStep.Type_open_out Bst _ Bki
        exact AopBisn.to_Kinding.TypeVarLocallyClosed_of.weaken (n := 1).Type_open_drop Nat.one_pos
      let AopB'isn : [[SN K₂ (A^^B')]] := MultiStep_preservation AopBisn mst
      let ⟨_, AopB'sni, _⟩ := AopBsni.MultiStep_preservation mst
      let ⟨_, Bsni, _⟩ := Bsni.preservation Bst
      exact go AopB'isn AopB'sni (Bst.preservation Bki) Bsni
  termination_by (m, n)
  decreasing_by
    · apply Prod.Lex.left
      assumption
    · apply Prod.Lex.right' <;> assumption

theorem arr (Aisn : [[SN * (A)]]) (Bisn : [[SN * (B)]]) : [[SN * (A → B)]] := by
  rw [IndexedStronglyNormalizing]
  refine ⟨Aisn.to_Kinding.arr Bisn.to_Kinding, ?_⟩
  exact .arr (.of_Indexed Aisn) (.of_Indexed Bisn)

theorem list {b : Bool} (Aisn : ∀ i ∈ [:n], [[SN K (A@i)]]) (h : n ≠ 0 ∨ b)
  : [[SN L K ({</ A@i // i in [:n] /> </ : K // b />})]] := by
  refine ⟨.list (Aisn · · |>.to_Kinding) h, ?_, ?_⟩
  · refine .refl ?_
    intro A mem
    rcases Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
    exact Aisn _ mem'
  · intro _ _ _ mst
    let ⟨_, eq, _⟩ := mst.preserve_shape_list
    nomatch eq

theorem prod (Aisn : [[SN L * (A)]]) : [[SN * (⊗ A)]] := by
  rw [IndexedStronglyNormalizing]
  refine ⟨Aisn.to_Kinding.prod, ?_⟩
  exact .prod <| .of_Indexed Aisn

theorem sum (Aisn : [[SN L * (A)]]) : [[SN * (⊕ A)]] := by
  rw [IndexedStronglyNormalizing]
  refine ⟨Aisn.to_Kinding.sum, ?_⟩
  exact .sum <| .of_Indexed Aisn

theorem comp (Aisn : [[SN K₂ ↦ K₃ (A)]]) (Bisn : [[SN K₁ ↦ K₂ (B)]])
  : [[SN K₁ ↦ K₃ (λ a : K₁. A (B a$0))]] := by
  rw [IndexedStronglyNormalizing]
  let Alc := Aisn.to_Kinding.TypeVarLocallyClosed_of
  let Blc := Bisn.to_Kinding.TypeVarLocallyClosed_of
  let ABaki : ∀ a ∉ [], [[ε, a : K₁ ⊢ (A (B a$0))^a : K₃]] := by
    intro a
    simp [Type.TypeVar_open, Alc.TypeVar_open_id, Blc.TypeVar_open_id]
    exact Aisn.to_Kinding.LE_weakening (.ext .refl nofun) |>.app <|
      Bisn.to_Kinding.LE_weakening (.ext .refl nofun) |>.app <| .var .head
  refine ⟨.lam [] ABaki, ?_⟩
  intro B' B'isn
  rw [IndexedStronglyNormalizing] at Aisn
  rw [IndexedStronglyNormalizing] at Bisn
  apply lam_app _ B'isn.to_Kinding <| .of_Indexed B'isn
  · simp [Type.Type_open, Alc.Type_open_id, Blc.Type_open_id]
    exact Aisn.right _ <| Bisn.right _ B'isn

end IndexedStronglyNormalizing

@[simp]
def Type.right_nested_listApps : «Type» → Nat
  | .listApp _ A => A.right_nested_listApps + 1
  | _ => 0

namespace IndexedStronglyNormalizing

theorem listApp (Aisn : [[SN K₁ ↦ K₂ (A)]]) (Bisn : [[SN L K₁ (B)]])
  : [[SN L K₂ (A ⟦B⟧)]] := by
  rw [IndexedStronglyNormalizing]
  refine ⟨.listApp Aisn.to_Kinding Bisn.to_Kinding, ?_, ?_⟩
  · let ⟨_, Asni⟩ := Aisn.to_In
    let ⟨_, Bsni⟩ := Bisn.to_In
    apply go₀ Asni Aisn.to_Kinding (Bisn.right.left.imp (Aisn.right _ ·)) Bsni Bisn.to_Kinding
    intro B₀ B₁ K' mst B₀ki
    let ⟨C, Cki, Csn, B₀Cisn⟩ := Bisn.right.right _ _ _ mst B₀ki
    exact ⟨_, Cki, Csn, Aisn.right _ B₀Cisn⟩
  · intro A' B' K' mst A'ki
    let ⟨_, msti⟩ := mst.to_In
    apply go₁ Aisn Bisn msti A'ki
    -- generalize Ceq : [[A ⟦B⟧]] = C, C'eq : [[A' ⟦B'⟧]] = C' at mst
    -- induction mst using Relation.ReflTransGen.head_induction_on generalizing A B with
    -- | refl =>
    --   cases Ceq
    --   cases C'eq
    --   cases Aisn.to_Kinding.deterministic B'ki
    --   exact ⟨
    --     _,
    --     Type.with_Kind.Kinding,
    --     Type.with_Kind.StronglyNormalizing,
    --     Aisn.right _ Type.with_Kind.IndexedStronglyNormalizing
    --   ⟩
    -- | head st mst' ih =>
    --   cases Ceq
    --   cases C'eq
    --   cases st with
    --   | listAppList =>
    --     let ⟨_, eq, _⟩ := MultiSmallStep.preserve_shape_list mst'
    --     nomatch eq
    --   | listAppId => sorry
    --   | listAppComp _ A₁ki =>
    --     let .listApp A₁ki' _ := Bisn.to_Kinding
    --     cases A₁ki.deterministic A₁ki'
    --     let ⟨C, Cki, Csn, isn⟩ := Bisn.right.right _ _ _ .refl A₁ki
    --     apply ih _ _ rfl
    --     -- exact ⟨_, Aisn.right _ A₁B''isn⟩
    --   | listAppl Ast => exact ih (Aisn.preservation Ast) Bisn rfl
    --   | listAppr Bst => exact ih Aisn (Bisn.preservation Bst) rfl
where
  go₁ {A B A' B' n K'} (Aisn : [[SN K₁ ↦ K₂ (A)]]) (Bisn : [[SN L K₁ (B)]])
    (msti : [[ε ⊢n A ⟦B⟧ ->* A' ⟦B'⟧]]) (A'ki : [[ε ⊢ A' : K' ↦ K₂]])
    : ∃ C, [[ε ⊢ C : K']] ∧ [[SN(C)]] ∧ [[SN K₂ (A' C)]] := by
    rcases msti.cases_head with ⟨rfl, eq⟩ | ⟨_, _, rfl, st, msti'⟩
    -- cases Relation.IndexedReflTransGen.cases_head msti with
    · cases eq
      cases Aisn.to_Kinding.deterministic A'ki
      exact ⟨
        _,
        Type.with_Kind.Kinding,
        Type.with_Kind.StronglyNormalizing,
        Aisn.right _ Type.with_Kind.IndexedStronglyNormalizing
      ⟩
    · cases st with
      | listAppList =>
        let ⟨_, eq, _⟩ := MultiSmallStep.preserve_shape_list <| .of_In msti'
        nomatch eq
      | listAppId => sorry
      | listAppComp _ A₁ki =>
        let .listApp A₁ki' _ := Bisn.to_Kinding
        cases A₁ki.deterministic A₁ki'
        let ⟨C, Cki, Csn, isn⟩ := Bisn.right.right _ _ _ .refl A₁ki
        apply go₁
        -- refine ⟨_, ?_, ?_, Aisn.right _ isn⟩
        -- apply ih _ _ rfl
        -- exact ⟨_, Aisn.right _ A₁B''isn⟩
      | listAppl Ast => exact ih (Aisn.preservation Ast) Bisn rfl
      | listAppr Bst => exact ih Aisn (Bisn.preservation Bst) rfl
  go₀ {A B m n K₁} (Asni : [[SN m (A)]]) (Aki : [[ε ⊢ A : K₁ ↦ K₂]])
    (Bsntl : StronglyNormalizingToList (fun B' => [[SN K₂ (A B')]]) B) (Bsni : [[SN n (B)]])
    (Bki : [[ε ⊢ B : L K₁]])
    (h : ∀ B₀ B₁ K', [[ε ⊢ B ->* B₀ ⟦B₁⟧]] → [[ε ⊢ B₀ : K' ↦ K₁]] → ∃ C, [[ε ⊢ C : K']] ∧ [[SN(C)]] ∧ [[SN K₂ (A (B₀ C))]])
    : StronglyNormalizingToList (fun B => [[SN K₂ (B)]]) [[A ⟦B⟧]] := by
    refine .step ?_ nofun
    intro _ st
    cases st with
    | listAppList =>
      refine .refl ?_
      intro _ mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      cases Bsntl
      case step ne => nomatch ne _ _
      case refl ABisn =>
      exact ABisn _ <| Range.mem_map_of_mem <| Range.mem_of_mem_toList mem'
    | listAppId Bki' =>
      apply Bsntl.imp'
      intro B's K? B' mst mem isn
      apply IndexedStronglyNormalizing.preservation isn
      have : B' = (Type.var (.bound 0)).Type_open B' := by
        rw [Type.Type_open, if_pos rfl]
      rw (occs := .pos [2]) [this]
      let B'ski := mst.preservation Bki'
      rw [← Range.map_get!_eq (as := B's), ← Option.someIf_get!_eq (x? := K?)] at B'ski
      apply SmallStep.lamApp .id
      rcases List.exists_mem_iff_getElem.mp ⟨_, mem, rfl⟩ with ⟨_, lt, rfl⟩
      convert B'ski.inv_list.left _ ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
      simp [List.getElem?_eq_getElem lt]
    | listAppComp _ A₁ki =>
      rename_i K₁' _ _ _
      let .listApp A₁ki' B'ki (A := A₁) := Bki
      cases A₁ki.deterministic A₁ki'
      let ⟨_, _, _, B'isn, _⟩ := Bsni.listApp_inversion A₁ki B'ki
      let ⟨C, Cki, Csn, AA₁Cisn⟩ := h _ _ _ .refl A₁ki
      apply StronglyNormalizing.of_Indexed at AA₁Cisn
      let Alc := Aki.TypeVarLocallyClosed_of
      let A₁lc := A₁ki.TypeVarLocallyClosed_of
      have : [[A (A₁ C)]] = [[((A (A₁ a$0))^^C)]] := by
        simp [Type.Type_open, Alc.Type_open_id, A₁lc.Type_open_id]
      rw [this] at AA₁Cisn
      let AA₁ki : [[ε ⊢ λ a : K₁'. A (A₁ a$0) : K₁' ↦ K₂]] := by
        apply Kinding.lam []
        intro a anin
        simp [Type.TypeVar_open, Alc.TypeVar_open_id, A₁lc.TypeVar_open_id]
        exact Aki.LE_weakening (.ext .refl nofun) |>.app <|
          A₁ki.LE_weakening (.ext .refl nofun) |>.app <| .var .head
      let ⟨_, compsni⟩ := AA₁Cisn.lam
        (.app (Alc.weaken (n := 1)) (.app (A₁lc.weaken (n := 1)) (.var_bound Nat.one_pos))) Cki
        |>.to_In AA₁ki
      apply go₀ compsni AA₁ki _ B'isn B'ki _
      · clear * - Bsntl A₁ki B'ki
        rename_i B'
        generalize Ceq : [[A₁ ⟦B'⟧]] = C at Bsntl
        induction Bsntl generalizing B' with
        | refl => nomatch Ceq
        | step sntl ne ih =>
          cases Ceq
          by_cases ∃ B's K?, B' = .list B's K?
          · case pos h =>
            rcases h with ⟨B's, K?, rfl⟩
            refine .refl ?_
            rw [← Range.map_get!_eq (as := B's), ← Option.someIf_get!_eq (x? := K?)] at sntl B'ki
            have : Option.someIf K?.get! K?.isSome = Option.someIf K₁' K?.isSome := by
              let h := B'ki.inv_list.right
              split at h
              · case isTrue =>
                rw [h]
              · case isFalse h' =>
                rw [Bool.not_eq_true _ |>.mp h', Option.someIf_false, Option.someIf_false]
            rw [this] at sntl
            cases sntl _ (.listAppList A₁ki)
            case step ne => nomatch ne _ _
            case refl h =>
            intro _ mem
            rcases List.exists_mem_iff_getElem.mp ⟨_, mem, rfl⟩ with ⟨_, lt, rfl⟩
            specialize h _ <| Range.mem_map_of_mem ⟨Nat.zero_le _, lt, Nat.mod_one _⟩
            simp [List.getElem?_eq_getElem lt] at h
            let .app A₀ki (.app A₁ki' B'ki) := h.to_Kinding
            cases A₁ki.deterministic A₁ki'
            let B'sn := And.right <| StronglyNormalizing.app_inversion <| And.right <|
              StronglyNormalizing.app_inversion <| .of_Indexed h
            apply lam_app _ B'ki B'sn
            simp [Type.Type_open, A₀ki.TypeVarLocallyClosed_of.Type_open_id,
                  A₁ki.TypeVarLocallyClosed_of.Type_open_id]
            exact h
          · case neg ne =>
            refine .step ?_ (not_exists.mp <| not_exists.mp ne ·)
            intro _ st
            exact ih _ (.listAppr st)  (st.preservation B'ki) rfl
      · intro B₀ B₁ K' mst B₀ki
        let B₀lc := B₀ki.TypeVarLocallyClosed_of
        let A₁B₀ki : [[ε ⊢ λ a : K'. A₁ (B₀ a$0) : K' ↦ K₁]] := by
          apply Kinding.lam []
          intro a anin
          simp [Type.TypeVar_open, A₁lc.TypeVar_open_id, B₀lc.TypeVar_open_id]
          exact A₁ki.LE_weakening (.ext .refl nofun) |>.app <|
            B₀ki.LE_weakening (.ext .refl nofun) |>.app <| .var .head
        let ⟨C, Cki, Csn, isn⟩ := h _ _ _
          (MultiSmallStep.listApp .refl mst |>.tail <| .listAppComp A₁lc B₀ki) A₁B₀ki
        refine ⟨C, Cki, Csn, ?_⟩
        replace isn := isn.preservation <| .appr <| .lamApp A₁B₀ki Cki
        simp [Type.Type_open, A₁lc.Type_open_id, B₀lc.Type_open_id] at isn
        apply lam_app _ (.app B₀ki Cki) <| StronglyNormalizing.of_Indexed isn
          |>.app_inversion.right.app_inversion.right
        simp [Type.Type_open, Alc.Type_open_id, A₁lc.Type_open_id]
        exact isn
    | listAppl Ast =>
      let ⟨_, Asni', _⟩ := Asni.preservation Ast
      apply go₀ Asni' (Ast.preservation Aki) (Bsntl.imp (·.preservation <| .appl Ast)) Bsni Bki
      intro _ _ _ mst ki
      let ⟨C, Cki, Csn, isn⟩ := h _ _ _ mst ki
      exact ⟨_, Cki, Csn, isn.preservation <| .appl Ast⟩
    | listAppr Bst =>
      let ⟨_, Bsni', _⟩ := Bsni.preservation Bst
      apply go₀ Asni Aki _ Bsni' (Bst.preservation Bki) (h · · · <| .head Bst ·)
      apply StronglyNormalizingToList.preservation Bsntl Bst
      intro _ _ isn st
      exact isn.preservation <| .appr st
  termination_by (n, B.right_nested_listApps, m)
  decreasing_by
    · apply Prod.Lex.right'
      · rename _ ≤ n => le
        exact Nat.le_trans (Nat.le_add_left ..) le
      · apply Prod.Lex.left
        rename B = _ => eq
        cases eq
        simp
    · apply Prod.Lex.right _ <| Prod.Lex.right ..
      assumption
    · apply Prod.Lex.left
      assumption

theorem of_Kinding (δsat : [[δ ⊨ Δ]]) (Aki : [[Δ ⊢ A : K]])
  : IndexedStronglyNormalizing K (δ A) := by
  open StronglyNormalizing in
  induction Aki generalizing δ with
  | var ain => exact δsat.right.right _ _ ain
  | lam I A'ki ih =>
    rename_i Δ K₁ A' _
    rw [Subst.apply, IndexedStronglyNormalizing]
    let Aki := δsat.preservation <| .lam I A'ki
    rw [Subst.apply] at Aki
    refine ⟨Aki, ?_⟩
    intro B Bisn
    let .lam I' A'ki' := Aki
    apply IndexedStronglyNormalizing.lam_app _ Bisn.to_Kinding <| .of_Indexed Bisn
    · let ⟨a, anin⟩ := A'.freeTypeVars ++ (δ A').freeTypeVars ++ δ.dom ++ δ.freeTypeVars ++ I ++
        Δ.typeVarDom |>.exists_fresh
      let ⟨aninA'δA'δdδfvI, aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninA'δA'δdδfv, aninI⟩ := List.not_mem_append'.mp aninA'δA'δdδfvI
      let ⟨aninA'δA'δd, aninδfv⟩ := List.not_mem_append'.mp aninA'δA'δdδfv
      let ⟨aninA'δA', aninδd⟩ := List.not_mem_append'.mp aninA'δA'δd
      let ⟨aninA', aninδA'⟩ := List.not_mem_append'.mp aninA'δA'
      rw [← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninδA',
          ← SubstSatisfies.apply_TypeVar_open_comm'' δsat aninδd (A'ki a aninI) aninA',
          ← Subst.apply_ext_eq_TypeVar_subst_apply (.cons aninδd δsat.left) aninδfv]
      exact ih a aninI <| δsat.TypeVar_ext aninδd aninδfv Bisn
  | app A'ki Bki ih₀ ih₁ =>
    rw [Subst.apply]
    let A'isn := ih₀ δsat
    rw [IndexedStronglyNormalizing] at A'isn
    exact A'isn.right _ <| ih₁ δsat
  | scheme I A'ki ih =>
    rename_i Δ K' A'
    rw [Subst.apply, IndexedStronglyNormalizing]
    let Aki := δsat.preservation <| .scheme I A'ki
    rw [Subst.apply] at Aki
    refine ⟨Aki, ?_⟩
    apply StronglyNormalizing.forall _ _ <| Type.with_Kind.Kinding (K := K')
    · let ⟨a, anin⟩ := A'.freeTypeVars ++ (δ A').freeTypeVars ++ δ.dom ++ δ.freeTypeVars ++ I
        |>.exists_fresh
      let ⟨aninA'δA'δdfv, aninI⟩ := List.not_mem_append'.mp anin
      let ⟨aninA'δA'δd, aninδfv⟩ := List.not_mem_append'.mp aninA'δA'δdfv
      let ⟨aninA'δA', aninδd⟩ := List.not_mem_append'.mp aninA'δA'δd
      let ⟨aninA', aninδA'⟩ := List.not_mem_append'.mp aninA'δA'
      let δ'sat := δsat.TypeVar_ext aninδd aninδfv <|
        Type.with_Kind.IndexedStronglyNormalizing (K := K')
      specialize ih a aninI δ'sat
      rw [Subst.apply_ext_eq_TypeVar_subst_apply δ'sat.left aninδfv,
          SubstSatisfies.apply_TypeVar_open_comm'' δsat aninδd (A'ki a aninI) aninA',
          Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninδA'] at ih
      exact .of_Indexed ih
    · let ⟨a, anin⟩ := A'.freeTypeVars ++ (δ A').freeTypeVars ++ δ.dom ++ δ.freeTypeVars ++ I
        |>.exists_fresh
      let ⟨aninA'δA'δdfv, aninI⟩ := List.not_mem_append'.mp anin
      let ⟨aninA'δA'δd, aninδfv⟩ := List.not_mem_append'.mp aninA'δA'δdfv
      let ⟨aninA'δA', aninδd⟩ := List.not_mem_append'.mp aninA'δA'δd
      let ⟨aninA', aninδA'⟩ := List.not_mem_append'.mp aninA'δA'
      let δ'sat := δsat.TypeVar_ext aninδd aninδfv <|
        Type.with_Kind.IndexedStronglyNormalizing (K := K')
      let A'ki' := δ'sat.preservation <| A'ki a aninI
      rw [Subst.apply_ext_eq_TypeVar_subst_apply δ'sat.left aninδfv,
          SubstSatisfies.apply_TypeVar_open_comm'' δsat aninδd (A'ki a aninI) aninA',
          Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninδA'] at A'ki'
      exact A'ki'
  | arr A'ki Bki ih₀ ih₁ =>
    rw [Subst.apply]
    exact .arr (ih₀ δsat) (ih₁ δsat)
  | list A'ki h ih =>
    rw [Subst.apply, List.mapMem_eq_map, Range.map, List.map_map, ← Range.map,
        Range.map_eq_of_eq_of_mem'' (fun _ _ => Function.comp.eq_def ..)]
    exact .list (ih · · δsat) h
  | listApp A'ki B'ki ih₀ ih₁ =>
    rw [Subst.apply]
    exact .listApp (ih₀ δsat) (ih₁ δsat)
  | prod A'ki ih =>
    rw [Subst.apply]
    exact .prod <| ih δsat
  | sum A'ki ih =>
    rw [Subst.apply]
    exact .sum <| ih δsat

end IndexedStronglyNormalizing

namespace StronglyNormalizing'

theorem of_synthetic (Δwf : [[⊢ Δ]]) (Alc : A.TypeVarLocallyClosed)
  (Asn : StronglyNormalizing ((Subst.synthetic Δ) A)) : [[Δ ⊢ SN(A)]] := by
  generalize A'eq : (Subst.synthetic Δ) A = A' at Asn
  induction Asn generalizing A with
  | intro _ _ ih =>
    cases A'eq
    constructor
    intro _ st
    apply ih _ _ (st.preserve_lc Alc) rfl
    rw [Rel.inv, flip] at st ⊢
    exact SubstSatisfies.synthetic_SmallStep_preservation Δwf Alc st

theorem of_Kinding (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]]) : [[Δ ⊢ SN(A)]] :=
  of_synthetic Δwf Aki.TypeVarLocallyClosed_of <| StronglyNormalizing.of_Indexed <|
    .of_Kinding (SubstSatisfies.synthetic Δwf) Aki

end StronglyNormalizing'

namespace MultiSmallStep

theorem add_Kinding (Amst : [[Δ ⊢ A ->* B]]) (Aki : [[Δ ⊢ A : K]])
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

theorem strongly_normalizing (Δwf : [[⊢ Δ]])
  : Thesis.strongly_normalizing (SmallStepWithKinding Δ K) := by
  apply Thesis.sn_iff_wf_inv _ |>.mp
  constructor
  intro A
  constructor
  intro B kist
  rw [Rel.inv, flip, SmallStepWithKinding] at kist
  let ⟨Aki, Ast⟩ := kist
  let Asn := StronglyNormalizing'.of_Kinding Aki Δwf
  rw [StronglyNormalizing'] at Asn
  exact StronglyNormalizing'.add_Kinding <| Acc.inv Asn Ast

theorem local_confluence (Δwf : [[⊢ Δ]]) :
  Thesis.weakly_confluent (SmallStepWithKinding Δ K) := by
  rintro _ _ _ ⟨⟨ki₀, st₀⟩, ⟨ki₁, st₁⟩⟩
  let ⟨_, mst₀, mst₁⟩ := st₀.local_confluence st₁ ki₀ Δwf
  exact ⟨_, mst₀.add_Kinding <| st₀.preservation ki₀, mst₁.add_Kinding <| st₁.preservation ki₁⟩

end SmallStepWithKinding

theorem MultiSmallStep.confluence (mst₀ : [[Δ ⊢ A ->* B₀]]) (mst₁ : [[Δ ⊢ A ->* B₁]])
  (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]]) : ∃ C, [[Δ ⊢ B₀ ->* C]] ∧ [[Δ ⊢ B₁ ->* C]] := by
  let ⟨_, mst₀', mst₁'⟩ := Thesis.Newman.newman (r := SmallStepWithKinding Δ K)
    (SmallStepWithKinding.strongly_normalizing Δwf) (SmallStepWithKinding.local_confluence Δwf)
    ⟨add_Kinding mst₀ Aki, add_Kinding mst₁ Aki⟩
  exact ⟨_, remove_kinding mst₀', remove_kinding mst₁'⟩

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
  : [[Δ ⊢ A₀ ⟦A₁ ⟦B⟧ ⟧ <->* (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧]] :=
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
