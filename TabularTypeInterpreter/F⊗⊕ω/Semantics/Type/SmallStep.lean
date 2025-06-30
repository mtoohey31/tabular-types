import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Equivalence
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax A " ≠ " B : Type.Ne

def Type.Ne := _root_.Ne (α := «Type»)

open Std

judgement_syntax "value " A : Type.IsValue

judgement Type.IsValue where

-- TODO: we have to disallow bound vars here, and then do opening in lam and forall

─────── var -- {a : TypeVarId}
value a

value A
────────────────── lam
value λ a : K. A

value A
──────────────── «forall»
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
───────── varApp
value a A

value A₀ A₁
value B
─────────────── appApp
value (A₀ A₁) B

value A
value B
──────────────────── forallApp
value (∀ a : K. A) B

∀ K, A ≠ λ a : K. a$0
value A
───────────────────── listAppVar
value A ⟦a⟧

∀ K, A ≠ λ a : K. a$0
value A
value B₀ B₁
───────────────────── listAppApp
value A ⟦B₀ B₁⟧

∀ K, A ≠ λ a : K. a$0
value A
value B
───────────────────── listAppForall
value A ⟦∀ a : K. B⟧

∀ K, A₀ ≠ λ a : K. a$0
∀ K A₁', A₁ ≠ λ a : K. A₁'
value A₀
value A₁ ⟦B⟧
────────────────────────── listAppListApp
value A₀ ⟦A₁ ⟦B⟧⟧

judgement_syntax A " -> " B : SmallStep

judgement SmallStep where

value A
value B
────────────────────────── lamApp
(λ a : K. A) B -> A^^B

∀ K, A ≠ λ a : K. a$0
value A
</ value B@i // i in [:n] />
────────────────────────────────────────────────────────── listAppList
A ⟦{</ B@i // i in [:n] />}⟧ -> {</ A B@i // i in [:n] />}

value A
─────────────────────── listAppId
(λ a : K. a$0) ⟦A⟧ -> A

∀ K', A₀ ≠ λ a : K'. a$0
value A₀
value (λ a : K. A₁) ⟦B⟧
────────────────────────────────────────────── listAppComp
A₀ ⟦(λ a : K. A₁) ⟦B⟧⟧ -> (λ a : K. A₀ A₁) ⟦B⟧

∀ a ∉ I, A^a -> A'^a
───────────────────────── lam (I : List TypeVarId)
λ a : K. A -> λ a : K. A'

A -> A'
─────────── appl
A B -> A' B

value A
B -> B'
─────────── appr
A B -> A B'

∀ a ∉ I, A^a -> A'^a
───────────────────────── «forall» (I : List TypeVarId)
∀ a : K. A -> ∀ a : K. A'

A -> A'
─────────────── arrl
A → B -> A' → B

value A
B -> B'
─────────────── arrr
A → B -> A → B'

</ value A₀@i // i in [:m] />
A₁ -> A₁'
───────────────────────────────────────────────────────────────────────────────────────────────────────────────── list
{</ A₀@i // i in [:m] />, A₁, </ A₂@j // j in [:n] />} -> {</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] />}

A -> A'
─────────────── listAppl
A ⟦B⟧ -> A' ⟦B⟧

value A
B -> B'
─────────────── listAppr
A ⟦B⟧ -> A ⟦B'⟧

A -> A'
─────────── prod
⊗ A -> ⊗ A'

A -> A'
─────────── sum
⊕ A -> ⊕ A'

judgement_syntax A " ->* " B : MultiSmallStep

judgement MultiSmallStep where

─────── refl
A ->* A

A₀ -> A₁
A₁ ->* A₂
───────── step
A₀ ->* A₂

judgement_syntax A " <->* " B : EqSmallStep

judgement EqSmallStep where

──────── refl
A <->* A

A -> B
──────── step
A <->* B

B <->* A
──────── symm
A <->* B

A <->* A'
A' <->* A''
─────────── trans
A <->* A''

namespace Type.IsValue

theorem list_inversion (h : [[value {</ A@i // i in [:n] />}]]) : ∀ i ∈ [:n], [[value A@i]] := by
  generalize Aseq : [:n].map _ = As at h
  let .list Asv := h
  let lengths_eq : ([:n].map _).length = _ := by rw [Aseq]
  rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at lengths_eq
  cases lengths_eq
  intro i mem
  rw [Range.eq_of_mem_of_map_eq Aseq i mem]
  exact Asv i mem

theorem TypeVar_close_intro : IsValue A → IsValue (A.TypeVar_close a n) := sorry

theorem TypeVar_open_intro : IsValue A → IsValue (A.TypeVar_open a n) := by
  induction A using Type.rec_uniform generalizing n
  case app => sorry
  case list => sorry -- trivial but messy
  case listApp A' _ ih₀ ih₁ =>
    intro v
    cases v with
    | listAppVar ne A'v =>
      rw [TypeVar_open, TypeVar_open]
      all_goals (
        apply listAppVar _ (ih₀ A'v)
        intro K A'eq
        specialize ne K
        cases A'
        case lam A'' =>
          rw [TypeVar_open] at A'eq
          let ⟨_, A''eq⟩ := Type.lam.inj A'eq
          cases A''
          case var a' =>
            rw [TypeVar_open] at A''eq
            split at A''eq
            · case isTrue h =>
              cases h
              rw [TypeVar_open, if_pos rfl] at A'eq
              nomatch A'eq
            · case isFalse h =>
              cases A''eq
              rw [TypeVar_open, if_neg h] at A'eq
              nomatch ne A'eq
          all_goals rw [TypeVar_open] at A''eq; nomatch A''eq
        all_goals rw [TypeVar_open] at A'eq; nomatch A'eq
      )
    | listAppApp ne A'v =>
      rw [TypeVar_open]
      sorry
    | listAppForall => sorry
    | listAppListApp => sorry
  all_goals aesop (add simp [TypeVar_open], unsafe cases IsValue, safe constructors IsValue)

theorem TypeVar_open_drop : IsValue (A.TypeVar_open a n) → IsValue A := by
  induction A using Type.rec_uniform generalizing n
  case app ih₀ ih₁ =>
    rename_i A' _
    rw [TypeVar_open]
    intro v
    generalize A''eq : A'.TypeVar_open a n = A'' at v
    cases v with
    | varApp B'v =>
      cases A'
      case var => exact varApp <| ih₁ B'v
      all_goals rw [TypeVar_open] at A''eq; nomatch A''eq
    | appApp A₀A₁v B'v =>
      cases A'
      case app =>
        refine appApp (ih₀ (n := n) ?_) <| ih₁ B'v
        rw [A''eq]
        exact A₀A₁v
      all_goals rw [TypeVar_open] at A''eq; nomatch A''eq
    | forallApp => sorry
  case list => sorry -- trivial but messy
  case listApp ih₀ ih₁ =>
    rename «Type» => B'
    rw [TypeVar_open]
    intro v
    generalize B''eq : B'.TypeVar_open a n = B'' at v
    cases v with
    | listAppVar ne A'v =>
      cases B'
      case var =>
        apply listAppVar _ <| ih₀ A'v
        intro K A'eq
        specialize ne K
        cases A'eq
        simp [TypeVar_open] at ne
        nomatch ne
      all_goals rw [TypeVar_open] at B''eq; nomatch B''eq
    | listAppApp ne A'v B₀B₁v =>
      cases B'
      case app =>
        refine listAppApp ?_ (ih₀ A'v) <| ih₁ (n := n) ?_
        · intro K A'eq
          specialize ne K
          cases A'eq
          simp [TypeVar_open] at ne
          nomatch ne
        · rw [B''eq]
          exact B₀B₁v
      all_goals rw [TypeVar_open] at B''eq; nomatch B''eq
    | listAppForall => sorry
    | listAppListApp => sorry
  all_goals aesop (add simp [TypeVar_open], unsafe cases IsValue, safe constructors IsValue)

theorem TypeVar_subst_var {a' : TypeVarId}
  : IsValue A → IsValue (A.TypeVar_subst a (.var a')) := by
  induction A using rec_uniform
  case app ih₀ ih₁ =>
    intro v
    rw [TypeVar_subst]
    cases v with
    | varApp B'v =>
      rw [TypeVar_subst]
      split <;> exact varApp <| ih₁ B'v
    | appApp A'v B'v =>
      let A'v' := ih₀ A'v
      rw [TypeVar_subst] at A'v' ⊢
      exact appApp A'v' <| ih₁ B'v
    | forallApp A'v B'v =>
      let A'v' := ih₀ A'v.forall
      rw [TypeVar_subst] at A'v' ⊢
      let .forall A'v'' := A'v'
      exact forallApp A'v'' <| ih₁ B'v
  case list => sorry -- trivial but messy
  case listApp A' B' ih₀ ih₁ =>
    intro v
    rw [TypeVar_subst]
    cases v with
    | listAppVar ne A'v =>
      rw [TypeVar_subst]
      split
      all_goals exact listAppVar (ne_preservation ne) <| ih₀ A'v
    | listAppApp ne A'v B'v =>
      let B'v' := ih₁ B'v
      rw [TypeVar_subst] at B'v' ⊢
      exact listAppApp (ne_preservation ne) (ih₀ A'v) B'v'
    | listAppForall ne A'v B'v =>
      let B'v' := ih₁ <| .forall B'v
      rw [TypeVar_subst] at B'v' ⊢
      let .forall B'v'' := B'v'
      exact listAppForall (ne_preservation ne) (ih₀ A'v) B'v''
    | listAppListApp ne ne' A'v B'v =>
      rename_i A₁ B''
      let B'v' := ih₁ B'v
      rw [TypeVar_subst] at B'v' ⊢
      apply listAppListApp (ne_preservation ne) _ (ih₀ A'v) B'v'
      intro K A₁' eq
      specialize ne' K
      cases A₁
      all_goals rw [TypeVar_subst] at eq
      case var => split at eq <;> nomatch eq
      case lam K A₁'' =>
        rcases Type.lam.inj eq with ⟨rfl, eq'⟩
        nomatch ne' A₁''
      all_goals nomatch eq
  all_goals aesop (add simp [TypeVar_subst], unsafe cases IsValue, safe constructors IsValue)
where
  ne_preservation {A} (ne : ∀ K, A ≠ [[λ a : K. a$0]])
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

theorem not_step (v : IsValue A) : ¬[[A -> B]] := by
  intro st
  cases v <;> try cases st
  · case lam v' _ I st' =>
    let ⟨a, anin⟩ := I.exists_fresh
    apply v' |>.TypeVar_open_intro.not_step
    exact st' a anin
  · case «forall» v' _ I st' =>
    let ⟨a, anin⟩ := I.exists_fresh
    apply v' |>.TypeVar_open_intro.not_step
    exact st' a anin
  · case arr.arrl v' _ _ st' => exact not_step v' st'
  · case arr.arrr _ v' _ _ st' => exact not_step v' st'
  · case list => sorry -- trivial but messy
  · case prod v' _ st' => exact not_step v' st'
  · case sum v' _ st' => exact not_step v' st'
  · case varApp.appl st' => exact not_step var st'
  · case varApp.appr v' _ _ st' => exact not_step v' st'
  · case appApp.appl v' _ _ st' => exact not_step v' st'
  · case appApp.appr v' _ _ st' => exact not_step v' st'
  · case forallApp.appl v' _ _ st' => exact not_step v'.forall st'
  · case forallApp.appr v' _ _ st' => exact not_step v' st'
  · case listAppVar.listAppId K' ne _ _ => nomatch ne K'
  · case listAppVar.listAppl v' _ st' => exact not_step v' st'
  · case listAppVar.listAppr st' => exact not_step var st'
  · case listAppApp.listAppId K' ne _ _ => nomatch ne K'
  · case listAppApp.listAppl v' _ _ st' => exact not_step v' st'
  · case listAppApp.listAppr v' _ _ st' => exact not_step v' st'
  · case listAppForall.listAppId K' ne _ _ => nomatch ne K'
  · case listAppForall.listAppl v' _ _ st' => exact not_step v' st'
  · case listAppForall.listAppr v' _ _ st' => exact not_step v'.forall st'
  · case listAppListApp.listAppId K' ne _ _ => nomatch ne K'
  · case listAppListApp.listAppComp K' A₁ _ _ ne' _ _ => nomatch ne' K' A₁
  · case listAppListApp.listAppl v' _ _ st' => nomatch not_step v' st'
  · case listAppListApp.listAppr v' _ _ st' => nomatch not_step v' st'

end Type.IsValue

namespace SmallStep

open «Type» in
theorem TypeVar_subst_var_preservation_of_not_mem_freeTypeVars {a' : TypeVarId} (Ast : [[A -> B]])
  : [[A[a' / a] -> B[a' / a] ]] := by match Ast with
  | .lamApp A'v B'v =>
    rw [TypeVar_subst, TypeVar_subst, TypeVarLocallyClosed.Type_open_TypeVar_subst_dist .var_free]
    exact lamApp A'v.TypeVar_subst_var B'v.TypeVar_subst_var
  | .listAppList .. => sorry
  | .listAppId A'v =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, if_neg nofun]
    exact .listAppId A'v.TypeVar_subst_var
  | .listAppComp ne A₀v A₁B'v =>
    rw [TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst, TypeVar_subst]
    apply Type.IsValue.TypeVar_subst_var at A₁B'v
    rw [TypeVar_subst, TypeVar_subst] at A₁B'v
    exact .listAppComp sorry A₀v.TypeVar_subst_var A₁B'v
  | .lam .. => sorry
  | .appl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .appl A'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars
  | .appr A'v B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .appr A'v.TypeVar_subst_var B'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars
  | .forall .. => sorry
  | .arrl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .arrl A'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars
  | .arrr A'v B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .arrr A'v.TypeVar_subst_var B'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars
  | .list .. => sorry
  | .listAppl A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .listAppl A'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars
  | .listAppr A'v B'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact .listAppr A'v.TypeVar_subst_var
      B'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars
  | .prod A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact A'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars.prod
  | .sum A'st =>
    rw [TypeVar_subst, TypeVar_subst]
    exact A'st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars.sum

theorem preserve_lc (st : [[A -> B]]) (Alc : A.TypeVarLocallyClosed) : B.TypeVarLocallyClosed := by
  sorry
  -- induction st
  -- case lamApp =>
  --   let .app (.lam W₀lc) W₁lc := Alc
  --   let f := W₀lc.Type_open_dec W₁lc
  --   sorry
  -- case listAppList => sorry
  -- case listAppComp =>
  --   let .listApp W₀lc (.listApp (.lam W₁lc) W₂lc) := Alc
  --   exact .listApp (.lam (.app W₀lc.weaken W₁lc)) W₂lc
  -- case lam I _ ih =>
  --   let .lam A'lc := Alc
  --   let ⟨a, anin⟩ := I.exists_fresh
  --   refine .lam <| .TypeVar_open_drop (Nat.zero_lt_succ _) <| ih a anin ?_
  --   rw [Type.Type_open_var]
  --   exact A'lc.Type_open_intro .var_free
  -- case «forall» I _ ih =>
  --   let .forall A'lc := Alc
  --   let ⟨a, anin⟩ := I.exists_fresh
  --   refine .forall <| .TypeVar_open_drop (Nat.zero_lt_succ _) <| ih a anin ?_
  --   rw [Type.Type_open_var]
  --   exact A'lc.Type_open_intro .var_free
  -- all_goals aesop
  --   (add unsafe cases Type.TypeVarLocallyClosed, safe constructors Type.TypeVarLocallyClosed)

theorem deterministic : [[A -> B]] → [[A -> C]] → B = C
  | .lamApp A'v B'v, st => match st with
    | .appl A'st => nomatch A'v.lam.not_step A'st
    | .appr _ B'st => nomatch B'v.not_step B'st
    | .lamApp _ _ => rfl
  | .listAppList ne A'v B'v (n := n), st => by
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
    | .listAppId _ (K := K) => nomatch ne K
    | .listAppl A'st => nomatch A'v.not_step A'st
    | .listAppr _ B'st =>
      cases Bseq
      nomatch Type.IsValue.not_step (.list B'v) B'st
  | .listAppId B'v (K := K), st => match st with
    | .listAppList ne _ _ => nomatch ne K
    | .listAppId _ => rfl
    | .listAppComp ne _ _ => nomatch ne K
    | .listAppl A'st => nomatch Type.IsValue.not_step (.lam .var) A'st
    | .listAppr _ B'st => nomatch B'v.not_step B'st
  | .listAppComp ne A₀v A₁Bv, st => match st with
    | .listAppId _ (K := K') => nomatch ne K'
    | .listAppComp .. => rfl
    | .listAppl A₀st => nomatch A₀v.not_step A₀st
    | .listAppr _ A₁Bst => nomatch A₁Bv.not_step A₁Bst
  | .lam I A'st, .lam I' A''st => by
    rename_i A' _ A''
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
    | .lamApp A'v _ => nomatch A'v.lam.not_step A'st
  | .appr A'v B'st, st => match st with
    | .appl A'st => nomatch A'v.not_step A'st
    | .appr _ B'st' => Type.app.injEq .. |>.mpr ⟨rfl, B'st.deterministic B'st'⟩
    | .lamApp _ B'v => nomatch B'v.not_step B'st
  | .forall I A'st, .forall I' A''st => by
    rename_i A' _ A''
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
  | .list .., st => sorry
  | .listAppl A'st, st => match st with
    | .listAppList _ A'v _ => nomatch A'v.not_step A'st
    | .listAppId B'v => nomatch Type.IsValue.not_step (.lam .var) A'st
    | .listAppComp _ A'v _ => nomatch A'v.not_step A'st
    | .listAppl A'st' => Type.listApp.injEq .. |>.mpr ⟨A'st.deterministic A'st', rfl⟩
    | .listAppr A'v _ => nomatch A'v.not_step A'st
  | .listAppr A'v B'st, st => match st with
    | .listAppList _ _ B'v => nomatch Type.IsValue.not_step (.list B'v) B'st
    | .listAppId B'v => nomatch B'v.not_step B'st
    | .listAppComp _ _ B'v => nomatch B'v.not_step B'st
    | .listAppl A'st => nomatch A'v.not_step A'st
    | .listAppr _ B'st' => Type.listApp.injEq .. |>.mpr ⟨rfl, B'st.deterministic B'st'⟩
  | .prod st, .prod st' => Type.prod.injEq .. |>.mpr <| st.deterministic st'
  | .sum st, .sum st' => Type.sum.injEq .. |>.mpr <| st.deterministic st'

theorem progress (Aki : [[Δ ⊢ A : K]]) : A.IsValue ∨ ∃ B, [[A -> B]] := match A, Aki with
  | .var _, .var _ => .inl .var
  | .lam K A', .lam I A'ki => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    match progress <| A'ki a aninI with
    | .inl A'v => exact .inl <| .lam A'v.TypeVar_open_drop
    | .inr ⟨A'', A'st⟩ =>
      refine .inr ⟨.lam K (A''.TypeVar_close a), .lam (a :: I) ?_⟩
      intro a' a'nin
      let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
      let A'lc := A'ki a aninI |>.TypeVarLocallyClosed_of
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst <|
            A'st.preserve_lc A'lc,
          ← Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA' (n := 0),
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst A'lc]
      exact TypeVar_subst_var_preservation_of_not_mem_freeTypeVars A'st
  | .app A' B', .app A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => by
        cases A'ki with
        | var => exact .inl <| .varApp B'v
        | lam =>
          let .lam A''v := A'v
          exact .inr ⟨_, .lamApp A''v B'v⟩
        | app => exact .inl <| .appApp A'v B'v
        | scheme =>
          let .forall A''v := A'v
          exact .inl <| .forallApp A''v B'v
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .appr A'v B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .appl A'st⟩
  | .forall K A', .scheme I A'ki => by
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    match progress <| A'ki a aninI with
    | .inl A'v => exact .inl <| .forall A'v.TypeVar_open_drop
    | .inr ⟨A'', A'st⟩ =>
      refine .inr ⟨.forall K (A''.TypeVar_close a), .forall (a :: I) ?_⟩
      intro a' a'nin
      let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
      let A'lc := A'ki a aninI |>.TypeVarLocallyClosed_of
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst <|
            A'st.preserve_lc A'lc,
          ← Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA' (n := 0),
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst A'lc]
      exact TypeVar_subst_var_preservation_of_not_mem_freeTypeVars A'st
  | .arr A' B', .arr A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => .inl <| .arr A'v B'v
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .arrr A'v B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .arrl A'st⟩
  | .list A', _ => sorry -- TODO: Just step by step, needs annoying induction though.
  | .listApp A' B', .listApp A'ki B'ki => match progress A'ki with
    | .inl A'v => match progress B'ki with
      | .inl B'v => by
        by_cases ∃ K', A' = [[λ a : K'. a$0]]
        · case pos h =>
          rcases h with ⟨_, rfl⟩
          exact .inr ⟨_, .listAppId B'v⟩
        · case neg ne =>
          apply not_exists.mp at ne
          cases B'ki with
          | var => exact .inl <| .listAppVar ne A'v
          | app => exact .inl <| .listAppApp ne A'v B'v
          | scheme =>
            let .forall B''v := B'v
            exact .inl <| .listAppForall ne A'v B''v
          | list => exact .inr ⟨_, .listAppList ne A'v B'v.list_inversion⟩
          | listApp =>
            rename_i A₁ _ B _ _
            by_cases ∃ K' A₁', A₁ = [[λ a : K'. A₁']]
            · case pos h =>
              rcases h with ⟨K', _, rfl⟩
              exact .inr ⟨_, .listAppComp ne A'v B'v⟩
            · case neg ne' =>
              exact .inl <| .listAppListApp ne (not_exists.mp <| not_exists.mp ne' ·) A'v B'v
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .listAppr A'v B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .listAppl A'st⟩
  | .prod A', .prod A'ki => match progress A'ki with
    | .inl A'v => .inl <| .prod A'v
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .prod A'stB'⟩
  | .sum A', .sum A'ki => match progress A'ki with
    | .inl A'v => .inl <| .sum A'v
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .sum A'stB'⟩

instance : Inhabited «Type» where
  default := .list []
in
theorem preservation (Δwf : [[⊢ Δ]]) : [[A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ B : K]]
  | .lamApp A'v B'v (A := A'), .app (.lam I A'ki) B'ki =>
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    A'ki a aninI |>.Type_open_preservation aninA' B'ki
  | .listAppList _ A'v B'v, .listApp A'ki B'ki =>
    let B'ki' := B'ki.inv_list
    .list (.app A'ki <| B'ki' · ·)
  | .listAppId A'v, .listApp (.lam I aki) A'ki => by
    let ⟨a, anin⟩ := I.exists_fresh
    specialize aki a anin
    rw [Type.TypeVar_open, if_pos rfl] at aki
    let .var .head := aki
    exact A'ki
  | .listAppComp _ A₀v A₁B'v, .listApp A₀ki (.listApp (.lam I A₁ki) Bki) => by
    refine .listApp (.lam (I ++ Δ.typeVarDom) (fun a anin => ?_)) Bki
    let ⟨aninI, aninΔ⟩ := List.not_mem_append'.mp anin
    rw [Type.TypeVar_open, A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
    exact .app (A₀ki.weakening (Δwf.typeVarExt aninΔ) (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
      A₁ki a aninI
  | .lam I A'st, .lam I' A'ki => .lam (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation (Δwf.typeVarExt aninΔ) (A'st a aninI) <| A'ki a aninI'
  | .appl A'st, .app A'ki B'ki => .app (A'st.preservation Δwf A'ki) B'ki
  | .appr _ B'st, .app A'ki B'ki => .app A'ki <| B'st.preservation Δwf B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.preservation Δwf A'ki) B'ki
  | .arrr _ B'st, .arr A'ki B'ki => .arr A'ki <| B'st.preservation Δwf B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation (Δwf.typeVarExt aninΔ) (A'st a aninI) <| A'ki a aninI'
  | .list _ A'st (m := m) (n := n), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rcases Aki.inv_list' with ⟨_, rfl, Aki'⟩
    apply Kinding.list
    intro i mem
    rw [List.length_append, Range.map, List.length_map, Range.length_toList, List.length_cons,
        Range.map, List.length_map, Range.length_toList, Nat.sub_zero, Nat.sub_zero] at mem
    sorry
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.preservation Δwf A'ki) B'ki
  | .listAppr _ B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.preservation Δwf B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.preservation Δwf A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.preservation Δwf A'ki

-- TODO: Will need to add hypotheses and probably Δ to judgement to make this work.
theorem preservation_rev (Δwf : [[⊢ Δ]]) : [[A -> B]] → [[Δ ⊢ B : K]] → [[Δ ⊢ A : K]]
  | .lamApp .., ki =>
    sorry
    -- let ⟨a, anin⟩ := W₀.val.freeTypeVars ++ I |>.exists_fresh
    -- let ⟨aninW₀, aninI⟩ := List.not_mem_append'.mp anin
    -- W₀ki a aninI |>.Type_open_preservation aninW₀ W₁ki
  | .listAppList .., ki =>
    sorry
    -- let W₁ki' := W₁ki.inv_list
    -- .list (.app W₀ki <| W₁ki' · ·)
  | .listAppId .., Wki => by
    sorry
    -- let ⟨a, anin⟩ := I.exists_fresh
    -- specialize aki a anin
    -- rw [Type.TypeVar_open, if_pos rfl] at aki
    -- let .var .head := aki
    -- exact Wki
  | .listAppComp .., .listApp (.lam I W₀W₁ki) W₂ki => by
    sorry
    -- refine .listApp (.lam (I ++ Δ.typeVarDom) (fun a anin => ?_)) W₂ki
    -- let ⟨aninI, aninΔ⟩ := List.not_mem_append'.mp anin
    -- rw [Type.TypeVar_open, W₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
    -- exact .app (W₀ki.weakening (Δwf.typeVarExt aninΔ) (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
    --   W₁ki a aninI
  | .lam I A'st, .lam I' A'ki => .lam (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation_rev (Δwf.typeVarExt aninΔ) (A'st a aninI) <| A'ki a aninI'
  | .appl A'st, .app A'ki B'ki => .app (A'st.preservation_rev Δwf A'ki) B'ki
  | .appr _ B'st, .app A'ki B'ki => .app A'ki <| B'st.preservation_rev Δwf B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.preservation_rev Δwf A'ki) B'ki
  | .arrr _ B'st, .arr A'ki B'ki => .arr A'ki <| B'st.preservation_rev Δwf B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact preservation_rev (Δwf.typeVarExt aninΔ) (A'st a aninI) <| A'ki a aninI'
  | .list _ A'st (m := m) (n := n), Aki => by
    rw [← Range.map_get!_eq (as := _ ++ _ :: _)] at Aki ⊢
    rcases Aki.inv_list' with ⟨_, rfl, Aki'⟩
    apply Kinding.list
    intro i mem
    rw [List.length_append, Range.map, List.length_map, Range.length_toList, List.length_cons,
        Range.map, List.length_map, Range.length_toList, Nat.sub_zero, Nat.sub_zero] at mem
    sorry
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.preservation_rev Δwf A'ki) B'ki
  | .listAppr _ B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.preservation_rev Δwf B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.preservation_rev Δwf A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.preservation_rev Δwf A'ki

theorem Equivalence_of : [[A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ A ≡ B]]
  | .lamApp .., .app (.lam I _) W₁ki => .lamApp W₁ki
  | .listAppList .., .listApp W₀ki _ => .listAppList W₀ki.TypeVarLocallyClosed_of
  | .listAppId _, .listApp (.lam I aki) Wki => .listAppId Wki
  | .listAppComp .., .listApp W₀ki (.listApp (.lam I W₁ki) W₂ki) =>
    .listAppComp W₀ki.TypeVarLocallyClosed_of
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
    sorry
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.Equivalence_of A'ki) .refl
  | .listAppr _ B'st, .listApp A'ki B'ki => .listApp .refl (B'st.Equivalence_of B'ki)
  | .prod A'st, .prod A'ki => .prod <| A'st.Equivalence_of A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.Equivalence_of A'ki

-- Inversion

-- the conclusion should be the reflexive closure of st but we can use this weaker version.
theorem inv_arr (ArBst: [[ (A → B) -> T ]]): ∃ A' B', T = [[ (A' → B') ]] ∧ [[ A ->* A' ]] ∧ [[ B ->* B' ]] := by
  cases ArBst <;> aesop (add unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_lam (Ast: [[ (λ a? : K. A) -> T ]]): ∃ A', T = [[λ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ A^a ->* A'^a ]] := by
  cases Ast ; aesop (add unsafe tactic guessI, unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_forall (Ast: [[ (∀ a? : K. A) -> T ]]): ∃ A', T = [[∀ a : K. A']] ∧ ∃I: List _, ∀a ∉ I, [[ A^a ->* A'^a ]] := by
  cases Ast ; aesop (add unsafe tactic guessI, unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_prod (Ast: [[ ⊗A -> T ]]): ∃ A', T = [[⊗A']] ∧ [[ A ->* A' ]] := by
  cases Ast ; aesop (add unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_sum (Ast: [[ ⊕A -> T ]]): ∃ A', T = [[⊕A']] ∧ [[ A ->* A' ]] := by
  cases Ast ; aesop (add unsafe constructors [MultiSmallStep, SmallStep])

theorem inv_list (Ast: [[ { </ A@i // i in [:n] /> } -> T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ A@i ->* B@i // i in [:n] /> ]] := by
  generalize T_eq : [[{ </ A@i // i in [:n] /> } ]] = T_ at Ast
  cases Ast <;> try cases T_eq
  . case list n₀ A₀i A₁ A₁' n₂ A₂i A₀V A₁st =>
    injection T_eq with eq
    sorry   -- TODO make a messy sandwich

end SmallStep

namespace MultiSmallStep

theorem trans (A₀mst : [[A₀ ->* A₁]]) (A₁mst : [[A₁ ->* A₂]]) : [[A₀ ->* A₂]] := by
  induction A₀mst with
  | refl => exact A₁mst
  | step A₀st _ ih => exact step A₀st <| ih A₁mst

theorem est_of (st : [[A ->* B]]) : [[A <->* B]] := by
  induction st with
  | refl => exact .refl
  | step Ast _ ih => exact EqSmallStep.step Ast |>.trans ih

open «Type» in
theorem TypeVar_subst_var_preservation_of_not_mem_freeTypeVars {a' : TypeVarId} (Ast : [[A ->* B]])
  : [[A[a' / a] ->* B[a' / a] ]] := by
  induction Ast with
  | refl => exact refl
  | step st _ ih => exact step st.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars ih

theorem preserve_lc (st : [[A ->* B]]) (Alc : A.TypeVarLocallyClosed) : B.TypeVarLocallyClosed := by
  induction st with
  | refl => exact Alc
  | step st _ ih => exact ih <| st.preserve_lc Alc

theorem TypeVar_open_swap (Amst : [[A^a' ->* A']]) (Alc : A.TypeVarLocallyClosed 1)
  (a'ninA : a' ∉ A.freeTypeVars) : [[A^a ->* (\a'^A')^a]] := by
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
  exact Amst.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars

theorem preservation (Amst : [[A ->* B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ B : K]] := by
  induction Amst with
  | refl => exact Aki
  | step Ast _ ih => exact ih <| Ast.preservation Δwf Aki

theorem EqSmallStep_of (Amst : [[A ->* B]]) : [[A <->* B]] := by
  induction Amst with
  | refl => exact .refl
  | step Ast _ ih => exact .trans (.step Ast) ih

theorem Equivalence_of (Amst : [[A ->* B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A ≡ B]] := by
  induction Amst with
  | refl => exact .refl
  | step Ast _ ih => exact .trans (Ast.Equivalence_of Aki) <| ih <| Ast.preservation Δwf Aki

theorem normalization (Aki : [[Δ ⊢ A : K]]) : ∃ B, B.IsValue ∧ [[A ->* B]] := sorry

theorem confluence (mst₀ : [[A ->* B₀]]) (mst₁ : [[A ->* B₁]]) : ∃ C, [[B₀ ->* C]] ∧ [[B₁ ->* C]] := by
  induction mst₀ generalizing B₁ with
  | refl => exact ⟨_, mst₁, refl⟩
  | step st mst₀' ih => cases mst₁ with
    | refl => exact ⟨_, refl, step st mst₀'⟩
    | step st' mst₁' =>
      cases st.deterministic st'
      apply ih mst₁'

-- Shape Preservation
theorem preserve_shape_arr (ArBmst: [[ (A → B) ->* T ]]): ∃ A' B', T = [[ (A' → B') ]] ∧ [[ A ->* A' ]] ∧ [[ B ->* B' ]] := by
  generalize ArBeq : [[ A → B ]] = ArB at ArBmst
  induction ArBmst generalizing A B
  . case refl ArB =>
    exact ⟨A, B, ArBeq.symm, .refl, .refl⟩
  . case step ArB A0rB0 ArB' ArBst Tmst ih =>
    subst ArBeq
    have ⟨A0, B0, A0rB0eq, Amst, Bmst⟩ := ArBst.inv_arr
    specialize ih A0rB0eq.symm
    aesop (add unsafe apply MultiSmallStep.trans)

theorem preserve_shape_forall (Amst: [[ (∀ a? : K. A) ->* T ]]): ∃ A', T = [[∀ a? : K. A']] ∧ (∃I, ∀a ∉ (I: List _), [[ A^a ->* A'^a ]]) :=
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

theorem preserve_shape_prod (Amst: [[ ⊗A ->* T ]]): ∃ A', T = [[⊗A']] ∧ [[ A ->* A' ]] :=
by
  generalize ProdAeq : [[(⊗A)]] = ProdA at Amst
  induction Amst generalizing A
  . case refl => aesop (add unsafe constructors [MultiSmallStep, SmallStep])
  . case step T1 T2 T3 red mred ih =>
    subst ProdAeq
    have := red.inv_prod
    aesop (add unsafe apply MultiSmallStep.trans)

theorem preserve_shape_sum (Amst: [[ ⊕A ->* T ]]): ∃ A', T = [[⊕A']] ∧ [[ A ->* A' ]] :=
by
  generalize SumAeq : [[(⊕A)]] = SumA at Amst
  induction Amst generalizing A
  . case refl => aesop (add unsafe constructors [MultiSmallStep, SmallStep])
  . case step T1 T2 T3 red mred ih =>
    subst SumAeq
    have := red.inv_sum
    aesop (add unsafe apply MultiSmallStep.trans)

theorem preserve_shape_list (Amst: [[ { </ A@i // i in [:n] /> } ->* T ]] ): ∃ B, T = [[{ </ B@i // i in [:n] /> }]] ∧ [[ </ A@i ->* B@i // i in [:n] /> ]] := by
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

theorem preserve_lc (est : [[A <->* B]]) (Alc : A.TypeVarLocallyClosed) : B.TypeVarLocallyClosed := by
  sorry

instance : Trans EqSmallStep EqSmallStep EqSmallStep where
  trans := trans

theorem lam (I : List TypeVarId) (Aest : ∀ a ∉ I, [[A^a <->* A'^a]])
  (Alc : A.TypeVarLocallyClosed 1) : [[λ a : K. A <->* λ a : K. A']] := by
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
    exact refl
  | step st =>
    cases A''eq
    cases A'''eq
    apply step <| .lam I _
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
    exact SmallStep.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars st
  | symm est ih =>
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A'oplc := est.symm.preserve_lc Aoplc
    rw [← A'''eq] at A'oplc
    let A'lc := A'oplc.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact symm <| ih A'lc aninA' aninA A'''eq A''eq
  | trans est₀ est₁ ih₀ ih₁ =>
    rename_i _ A'''' _
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A''''lc := est₀.preserve_lc Aoplc
    exact trans
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close A''eq
        A''''lc.TypeVar_open_TypeVar_close_id)
      (ih₁ A''''lc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        A''''lc.TypeVar_open_TypeVar_close_id A'''eq)

theorem app (Aki : [[Δ ⊢ A : K]]) (Aest : [[A <->* A']]) (Best : [[B <->* B']])
  : [[A B <->* A' B']] := by
  let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization Aki
  clear Aki
  calc
    [[A B <->* A'' B]] := by
      clear Aest A''v
      induction A''mst with
      | refl => exact refl
      | step st _ ih =>
        exact trans (step (.appl st)) ih
    [[A'' B <->* A'' B']] := by
      induction Best with
      | refl => exact refl
      | step st => exact step <| .appr A''v st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁
    [[A'' B' <->* A B']] := by
      apply symm
      clear Aest A''v
      induction A''mst with
      | refl => exact refl
      | step st _ ih =>
        exact trans (step (.appl st)) ih
    [[A B' <->* A' B']] := by
      clear A''mst
      induction Aest with
      | refl => exact refl
      | step st => exact step <| .appl st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem «forall» (I : List TypeVarId) (Aest : ∀ a ∉ I, [[A^a <->* A'^a]])
  (Alc : A.TypeVarLocallyClosed 1) : [[∀ a : K. A <->* ∀ a : K. A']] := by
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
    exact refl
  | step st =>
    cases A''eq
    cases A'''eq
    apply step <| .forall I _
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
    exact SmallStep.TypeVar_subst_var_preservation_of_not_mem_freeTypeVars st
  | symm est ih =>
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A'oplc := est.symm.preserve_lc Aoplc
    rw [← A'''eq] at A'oplc
    let A'lc := A'oplc.TypeVar_close_inc (a := a)
    rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
    exact symm <| ih A'lc aninA' aninA A'''eq A''eq
  | trans est₀ est₁ ih₀ ih₁ =>
    rename_i _ A'''' _
    let Aoplc := Alc.Type_open_dec .var_free (B := .var (.free a))
    rw [← Type.Type_open_var, A''eq] at Aoplc
    let A''''lc := est₀.preserve_lc Aoplc
    exact trans
      (ih₀ Alc aninA Type.not_mem_freeTypeVars_TypeVar_close A''eq
        A''''lc.TypeVar_open_TypeVar_close_id)
      (ih₁ A''''lc.TypeVar_close_inc Type.not_mem_freeTypeVars_TypeVar_close aninA'
        A''''lc.TypeVar_open_TypeVar_close_id A'''eq)

theorem arr (Aki : [[Δ ⊢ A : K]]) (Aest : [[A <->* A']]) (Best : [[B <->* B']])
  : [[A → B <->* A' → B']] := by
  let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization Aki
  clear Aki
  calc
    [[A → B <->* A'' → B]] := by
      clear Aest A''v
      induction A''mst with
      | refl => exact refl
      | step st _ ih =>
        exact trans (step (.arrl st)) ih
    [[A'' → B <->* A'' → B']] := by
      induction Best with
      | refl => exact refl
      | step st => exact step <| .arrr A''v st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁
    [[A'' → B' <->* A → B']] := by
      apply symm
      clear Aest A''v
      induction A''mst with
      | refl => exact refl
      | step st _ ih =>
        exact trans (step (.arrl st)) ih
    [[A → B' <->* A' → B']] := by
      clear A''mst
      induction Aest with
      | refl => exact refl
      | step st => exact step <| .arrl st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem list (Aki : ∀ i ∈ [:n], [[Δ ⊢ A@i : K]]) (Aest : ∀ i ∈ [:n], [[A@i <->* A'@i]])
  : [[{</ A@i // i in [:n] />} <->* {</ A'@i // i in [:n] />}]] := sorry

theorem listApp (Aki : [[Δ ⊢ A : K]]) (Aest : [[A <->* A']]) (Best : [[B <->* B']])
  : [[A ⟦B⟧ <->* A' ⟦B'⟧]] := by
  let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization Aki
  clear Aki
  calc
    [[A ⟦B⟧ <->* A'' ⟦B⟧]] := by
      clear Aest A''v
      induction A''mst with
      | refl => exact refl
      | step st _ ih =>
        exact trans (step (.listAppl st)) ih
    [[A'' ⟦B⟧ <->* A'' ⟦B'⟧]] := by
      induction Best with
      | refl => exact refl
      | step st => exact step <| .listAppr A''v st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁
    [[A'' ⟦B'⟧ <->* A ⟦B'⟧]] := by
      apply symm
      clear Aest A''v
      induction A''mst with
      | refl => exact refl
      | step st _ ih =>
        exact trans (step (.listAppl st)) ih
    [[A ⟦B'⟧ <->* A' ⟦B'⟧]] := by
      clear A''mst
      induction Aest with
      | refl => exact refl
      | step st => exact step <| .listAppl st
      | symm _ ih => exact symm ih
      | trans _ _ ih₀ ih₁ => exact trans ih₀ ih₁

theorem prod (est : [[A <->* B]]) : [[⊗ A <->* ⊗ B]] := by
  induction est with
  | refl => exact .refl
  | step st => exact .step st.prod
  | symm _ ih => exact .symm ih
  | trans _ _ ih₀ ih₁ => exact .trans ih₀ ih₁

theorem sum (est : [[A <->* B]]) : [[⊕ A <->* ⊕ B]] := by
  induction est with
  | refl => exact .refl
  | step st => exact .step st.sum
  | symm _ ih => exact .symm ih
  | trans _ _ ih₀ ih₁ => exact .trans ih₀ ih₁

theorem Type_open_in (Aest : [[A <->* A']]) : [[A^^B <->* A'^^B]] := by
  sorry

open «Type» in
theorem Type_open_out (Best : [[B <->* B']]) (Aki : [[Δ, a : K ⊢ A^a : K']])
  (aninA : a ∉ A.freeTypeVars) (Bki : [[Δ ⊢ B : K]]) : [[A^^B <->* A^^B']] := by
  induction Best with
  | refl => exact .refl
  | step st =>
    induction A using rec_uniform generalizing K' with
    | var =>
      rw [Type_open]
      split
      · case isTrue h =>
        cases h
        rw [Type_open, if_pos rfl]
        exact .step st
      · case isFalse h =>
        rw [Type_open, if_neg h]
        exact .refl
    | lam => sorry
    | app _ _ ih₀ ih₁ =>
      simp [freeTypeVars] at aninA
      let ⟨aninA', aninB'⟩ := aninA
      rw [TypeVar_open] at Aki
      let .app A'ki B'ki := Aki
      rw [Type_open, Type_open]
      exact ih₀ A'ki aninA' |>.app (A'ki.Type_open_preservation aninA' Bki) <| ih₁ B'ki aninB'
    | «forall» => sorry
    | arr _ _ ih₀ ih₁ =>
      simp [freeTypeVars] at aninA
      let ⟨aninA', aninB'⟩ := aninA
      rw [TypeVar_open] at Aki
      let .arr A'ki B'ki := Aki
      rw [Type_open, Type_open]
      exact ih₀ A'ki aninA' |>.arr (A'ki.Type_open_preservation aninA' Bki) <| ih₁ B'ki aninB'
    | list => sorry
    | listApp _ _ ih₀ ih₁ =>
      simp [freeTypeVars] at aninA
      let ⟨aninA', aninB'⟩ := aninA
      rw [TypeVar_open] at Aki
      let .listApp A'ki B'ki := Aki
      rw [Type_open, Type_open]
      exact ih₀ A'ki aninA' |>.listApp (A'ki.Type_open_preservation aninA' Bki) <| ih₁ B'ki aninB'
    | prod _ ih =>
      rw [freeTypeVars] at aninA
      rw [TypeVar_open] at Aki
      let .prod A'ki := Aki
      rw [Type_open, Type_open]
      exact ih A'ki aninA |>.prod
    | sum _ ih =>
      rw [freeTypeVars] at aninA
      rw [TypeVar_open] at Aki
      let .sum A'ki := Aki
      rw [Type_open, Type_open]
      exact ih A'ki aninA |>.sum
  | symm _ ih =>
    exact symm <| ih sorry
  | trans _ _ ih₀ ih₁ => exact trans (ih₀ Bki) (ih₁ sorry)

theorem Type_open (Aest : [[A <->* A']]) (Best : [[B <->* B']]) (Aki : [[Δ, a : K ⊢ A^a : K']])
  (aninA : a ∉ A.freeTypeVars) (Bki : [[Δ ⊢ B : K]]) : [[A^^B <->* A'^^B']] := by
  apply trans
  · apply Type_open_in Aest
  · apply Type_open_out
      Best
      sorry
      sorry
      Bki
    sorry
  -- induction Aest with
  -- | refl => exact Type_open_out Best Aki aninA Bki
  -- | step st =>
  --   sorry
  --   -- induction st with
  --   -- | prod _ ih =>
  --   --   rw [Type.Type_open, Type.Type_open]
  --   --   exact ih.prod
  --   -- | sum _ ih =>
  --   --   rw [Type.Type_open, Type.Type_open]
  --   --   exact ih.sum
  -- | symm st ih =>
  --   rename_i A''' A''
  --   calc
  --     [[A''^^B <->* A''^^B']] := Type_open_out Best sorry sorry sorry
  --     [[A''^^B' <->* A'''^^B]] := symm ih
  --     [[A'''^^B <->* A'''^^B']] := Type_open_out Best sorry sorry sorry
  -- | trans _ est ih₀ => exact trans ih₀ est.Type_open_in

theorem of_EquivalenceI (equ : [[Δ ⊢ A ≡ᵢ B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[A <->* B]] := by
  induction equ generalizing K with
  | refl => exact refl
  | lamApp B'ki =>
    rename_i B' K' A'
    let .app (.lam I A'ki) B'ki := Aki
    let ⟨a, anin⟩ := A'.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninA', aninI⟩ := List.not_mem_append'.mp anin
    let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization <| A'ki a aninI
    let ⟨B'', B''v, B''mst⟩ := MultiSmallStep.normalization B'ki
    calc
      [[(λ a : K'. A') B' <->* (λ a : K'. \a^A'') B'']] := by
        apply app (.lam I A'ki) _ B''mst.EqSmallStep_of
        let A'lc := A'ki a aninI |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a)
        rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninA'] at A'lc
        apply lam (A''.freeTypeVars ++ I) _ A'lc
        intro a' a'nin
        exact A''mst.TypeVar_open_swap A'lc aninA' |>.EqSmallStep_of
      [[(λ a : K'. \a^A'') B'' <->* (\a^A'')^^B'']] := step <| .lamApp A''v.TypeVar_close_intro B''v
      [[(\a^A'')^^B'' <->* A'^^B']] := by
        -- FALSE: Maybe? Gotta figure out how to reduce this cause the opening might break the order... but should still be the same group?
        apply symm
        apply Type_open _ B''mst.EqSmallStep_of (A'ki a aninI) aninA' B'ki
        apply MultiSmallStep.EqSmallStep_of
        sorry -- close A''mst
  | listAppList =>
    rename «Type» => A'
    rename Nat => n
    rename Nat → «Type» => B'
    let .listApp A'ki B'ki (K₁ := K₁) := Aki
    let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization A'ki
    let B'ki' := B'ki.inv_list
    let ⟨B'', B''vB''mst⟩ := Range.skolem (MultiSmallStep.normalization <| B'ki' · ·)
    by_cases ∃ K', A'' = [[λ a : K'. a$0]]
    · case pos h =>
      rcases h with ⟨_, rfl⟩
      cases A''mst.preservation A'ki Δwf
      calc
        [[A' ⟦{</ B'@i // i in [:n] />}⟧ <->* (λ a : K₁. a$0) ⟦{</ B''@i // i in [:n] />}⟧]] :=
          listApp A'ki A''mst.EqSmallStep_of <| list B'ki' (B''vB''mst · · |>.right.EqSmallStep_of)
        [[(λ a : K₁. a$0) ⟦{</ B''@i // i in [:n] />}⟧ <->* {</ B''@i // i in [:n] />}]] :=
          step <| .listAppId <| .list (B''vB''mst · · |>.left)
        [[{</ B''@i // i in [:n] />} <->* {</ (λ a : K₁. a$0) B''@i // i in [:n] />}]] := by
          apply list
          · intro i mem
            exact B''vB''mst i mem |>.right.preservation (B'ki' i mem) Δwf
          · intro i mem
            apply symm
            have : B'' i = Type.Type_open (.var (.bound 0)) (B'' i) := by
              rw [Type.Type_open, if_pos rfl]
            rw (occs := .pos [2]) [this]
            exact step <| SmallStep.lamApp .var <| B''vB''mst i mem |>.left
        [[{</ (λ a : K₁. a$0) B''@i // i in [:n] />} <->* {</ A' B'@i // i in [:n] />}]] :=
          symm <| list (.app A'ki <| B'ki' · ·)
            (app A'ki A''mst.EqSmallStep_of <| B''vB''mst · · |>.right.EqSmallStep_of)
    · case neg ne =>
      calc
        [[A' ⟦{</ B'@i // i in [:n] />}⟧ <->* A'' ⟦{</ B''@i // i in [:n] />}⟧]] :=
          listApp A'ki A''mst.EqSmallStep_of <| list B'ki' (B''vB''mst · · |>.right.EqSmallStep_of)
        [[A'' ⟦{</ B''@i // i in [:n] />}⟧ <->* {</ A'' B''@i // i in [:n] />}]] :=
          step <| .listAppList (not_exists.mp ne) A''v (B''vB''mst · · |>.left)
        [[{</ A'' B''@i // i in [:n] />} <->* {</ A' B'@i // i in [:n] />}]] :=
          symm <| list (.app A'ki <| B'ki' · ·)
            (app A'ki A''mst.EqSmallStep_of <| B''vB''mst · · |>.right.EqSmallStep_of)
  | listAppId =>
    rename_i A' K' _
    let .listApp _ A'ki := Aki
    let ⟨A'', A''v, A''mst⟩ := MultiSmallStep.normalization A'ki
    calc
      [[(λ a : K'. a$0) ⟦A'⟧ <->* (λ a : K'. a$0) ⟦A''⟧]] :=
        listApp .id .refl A''mst.EqSmallStep_of (Δ := .empty)
      [[(λ a : K'. a$0) ⟦A''⟧ <->* A'']] := step <| .listAppId A''v
      [[A'' <->* A']] := A''mst.EqSmallStep_of.symm
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
    exact .app A'ki (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
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
    exact .listApp A'ki (ih₀ A'ki Δwf) (ih₁ B'ki Δwf)
  | listAppComp =>
    rename_i A₀ Δ K' A₁ B' _
    let .listApp A₀ki (.listApp (.lam I A₁ki) B'ki) (K₁ := K₁) (K₂ := K₂) := Aki
    let ⟨A₀', A₀'v, A₀'mst⟩ := MultiSmallStep.normalization A₀ki
    let ⟨A₁B'', A₁B''v, A₁B''mst⟩ := MultiSmallStep.normalization <| .listApp (.lam I A₁ki) B'ki
    by_cases ∃ K'', A₀' = [[λ a : K''. a$0]]
    · case pos h =>
      rcases h with ⟨K'', rfl⟩
      cases A₀'mst.preservation A₀ki Δwf
      case lam I' A₀''ki =>
      let ⟨a, anin⟩ := I'.exists_fresh
      specialize A₀''ki a anin
      rw [Type.TypeVar_open, if_pos rfl] at A₀''ki
      let .var .head := A₀''ki
      let ⟨a', a'nin⟩ := A₁.freeTypeVars ++ I ++ Δ.typeVarDom |>.exists_fresh
      let ⟨a'ninA₁I, a'ninΔ⟩ := List.not_mem_append'.mp a'nin
      let ⟨a'ninA₁, a'ninI⟩ := List.not_mem_append'.mp a'ninA₁I
      let ⟨A₁', A₁'v, A₁'mst⟩ := MultiSmallStep.normalization <| A₁ki a' a'ninI
      let ⟨B'', B''v, B''mst⟩ := MultiSmallStep.normalization B'ki
      let A₀lc := A₀ki.TypeVarLocallyClosed_of
      let A₁lc := A₁ki a' a'ninI |>.TypeVarLocallyClosed_of.TypeVar_close_inc (a := a')
      rw [Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars a'ninA₁] at A₁lc
      calc
        [[A₀ ⟦(λ a : K'. A₁) ⟦B'⟧⟧ <->* (λ a : K₁. a$0) ⟦A₁B''⟧]] :=
          listApp A₀ki  A₀'mst.EqSmallStep_of A₁B''mst.EqSmallStep_of
        [[(λ a : K₁. a$0) ⟦A₁B''⟧ <->* A₁B'']] := step <| .listAppId A₁B''v
        [[A₁B'' <->* (λ a : K'. A₁) ⟦B'⟧]] := A₁B''mst.EqSmallStep_of.symm
        [[(λ a : K'. A₁) ⟦B'⟧ <->* (λ a : K'. \a'^A₁') ⟦B''⟧]] := by
          apply listApp (.lam I A₁ki) _ B''mst.EqSmallStep_of
          apply lam I _ A₁lc
          intro a'' a''nin
          exact A₁'mst.TypeVar_open_swap A₁lc a'ninA₁ |>.EqSmallStep_of
        [[(λ a : K'. \a'^A₁') ⟦B''⟧ <->* (λ a : K'. (λ a : K₁. a$0) \a'^A₁') ⟦B''⟧]] := by
          apply symm
          apply listApp
          · apply Kinding.lam <| a' :: Δ.typeVarDom
            intro a'' a''nin
            let ⟨ane, a''ninΔ⟩ := List.not_mem_cons.mp a''nin
            simp [Type.TypeVar_open]
            apply Kinding.app .id
            let A₁'ki := A₁'mst.preservation (A₁ki a' a'ninI) <| Δwf.typeVarExt a'ninΔ
            rw [Type.Type_open_var,
                A₁'ki.TypeVarLocallyClosed_of.Type_open_TypeVar_close_eq_TypeVar_subst]
            let Δa''a'wf := Δwf.typeVarExt a''ninΔ (K := K') |>.typeVarExt (K := K') <|
              List.not_mem_cons.mpr ⟨ane.symm, a'ninΔ⟩
            exact A₁'ki.weakening Δa''a'wf (Δ' := .typeExt .empty ..) (Δ'' := .typeExt .empty ..)
              |>.subst Δa''a'wf <| .var .head
          · apply lam I _ <| Type.TypeVarLocallyClosed.app (.lam <| .var_bound Nat.zero_lt_two)
              (A₁'mst.preserve_lc <| A₁ki a' a'ninI |>.TypeVarLocallyClosed_of).TypeVar_close_inc
            intro a'' a''nin
            simp [Type.TypeVar_open]
            have : (A₁'.TypeVar_close a').TypeVar_open a'' =
              Type.Type_open (.var (.bound 0)) ((A₁'.TypeVar_close a').TypeVar_open a'') := by
              rw [Type.Type_open, if_pos rfl]
            rw (occs := .pos [2]) [this]
            exact step <| .lamApp .var A₁'v.TypeVar_close_intro.TypeVar_open_intro
          · exact refl
        [[(λ a : K'. (λ a : K₁. a$0) \a'^A₁') ⟦B''⟧ <->* (λ a : K'. A₀ A₁) ⟦B'⟧]] := by
          apply symm
          apply listApp
          · apply Kinding.lam <| I ++ Δ.typeVarDom
            intro a'' a''nin
            let ⟨a''ninI, a''ninΔ⟩ := List.not_mem_append'.mp a''nin
            simp [Type.TypeVar_open]
            apply Kinding.app
            · rw [A₀lc.TypeVar_open_id]
              exact A₀ki.weakening (Δwf.typeVarExt a''ninΔ) (Δ' := .typeExt .empty ..)
                (Δ'' := .empty)
            · exact A₁ki a'' a''ninI
          · apply lam I _ <| A₀lc.weaken (n := 1).app A₁lc
            intro a'' a''nin
            simp [Type.TypeVar_open]
            rw [A₀lc.TypeVar_open_id]
            exact app A₀ki A₀'mst.EqSmallStep_of <|
              A₁'mst.TypeVar_open_swap A₁lc a'ninA₁ |>.EqSmallStep_of
          · exact B''mst.EqSmallStep_of
    · case neg ne =>
      by_cases ∃ A₁' B'', A₁B'' = [[(λ a : K'. A₁') ⟦B''⟧]]
      · case pos h =>
        rcases h with ⟨A₁', B'', rfl⟩
        let ⟨a, anin⟩ := I.exists_fresh
        -- FALSE: This calc is wrong because we're not guaranteed that A₁' and B'' actually
        -- correspond to A₁ and B'.
        calc
          [[A₀ ⟦(λ a : K'. A₁) ⟦B'⟧⟧ <->* A₀' ⟦(λ a : K'. A₁') ⟦B''⟧⟧]] :=
            listApp A₀ki A₀'mst.EqSmallStep_of A₁B''mst.EqSmallStep_of
          [[A₀' ⟦(λ a : K'. A₁') ⟦B''⟧⟧ <->* (λ a : K'. A₀' A₁') ⟦B''⟧]] :=
            step <| .listAppComp (not_exists.mp ne) A₀'v A₁B''v
          [[(λ a : K'. A₀' A₁') ⟦B''⟧ <->* (λ a : K'. A₀ A₁) ⟦B'⟧]] := by
            apply symm
            apply listApp
            apply Kinding.lam <| I ++ Δ.typeVarDom
            intro a anin
            let ⟨aninI, aninΔ⟩ := List.not_mem_append'.mp anin
            rw [Type.TypeVar_open, A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
            exact .app
              (A₀ki.weakening (Δwf.typeVarExt aninΔ) (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
              A₁ki a aninI
            sorry
            sorry
      · case neg h =>
        sorry -- cases to check everything we might've turned into
  | prod equ' ih =>
    let .prod A'ki := Aki
    exact ih A'ki Δwf |>.prod
  | sum equ' ih =>
    let .sum A'ki := Aki
    exact ih A'ki Δwf |>.sum

theorem _root_.TabularTypeInterpreter.«F⊗⊕ω».TypeEquivalenceS.preservation : [[Δ ⊢ A ≡ₛ B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ B : K]] := sorry

theorem of_EquivalenceS (equ : [[Δ ⊢ A ≡ₛ B]]) (Aki : [[Δ ⊢ A : K]]) (Bki : [[Δ ⊢ B : K]])
  (Δwf : [[⊢ Δ]]) : [[A <->* B]] := by
  induction equ with
  | base equ' => exact .of_EquivalenceI equ' Aki Δwf
  | symm equ' => exact .symm <| .of_EquivalenceI equ' Bki Δwf
  | trans equ' _ ih₀ ih₁ =>
    exact .trans (ih₀ Aki (equ'.preservation Aki)) (ih₁ (equ'.preservation Aki) Bki)

theorem preservation (Aest : [[A <->* B]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A : K]] ↔ [[Δ ⊢ B : K]] := by
  induction Aest with
  | refl => exact ⟨id, id⟩
  | step Ast => exact ⟨(Ast.preservation Δwf ·), (Ast.preservation_rev Δwf ·)⟩
  | symm _ ih => exact .symm ih
  | trans _ _ ih₀ ih₁ => exact ⟨(ih₁.mp <| ih₀.mp ·), (ih₀.mpr <| ih₁.mpr ·)⟩

theorem Equivalence_of (Aest : [[A <->* B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A ≡ B]] := by
  induction Aest with
  | refl => exact .refl
  | step A'st => exact A'st.Equivalence_of Aki
  | symm B'st ih => exact .symm <| ih <| symm B'st |>.preservation Δwf |>.mp Aki
  | trans A'st _ ih₀ ih₁ => exact .trans (ih₀ Aki) <| ih₁ <| A'st.preservation Δwf |>.mp Aki

theorem common_reduct (est : [[A <->* B]]) : ∃ C, [[A ->* C]] ∧ [[B ->* C]] := by
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
theorem inj_arr (ArBest: [[ (A → B) <->* (A' → B') ]]): [[ A <->* A' ]] ∧ [[ B <->* B' ]] := by
  have ⟨T, ArB_Tmst, A'rB'_Tmst⟩ := ArBest.common_reduct
  have ⟨A1, B1, Teq1, AA1, BB1⟩ := ArB_Tmst.preserve_shape_arr
  have ⟨A2, B2, Teq2, A'A2, B'B2⟩ := A'rB'_Tmst.preserve_shape_arr
  subst T; cases Teq2; case refl =>
  refine ⟨AA1.est_of.trans A'A2.est_of.symm, BB1.est_of.trans B'B2.est_of.symm⟩

theorem inj_forall (Aest: [[ (∀ a? : K. A) <->* (∀ a? : K'. A') ]]): K = K' ∧ ∃I: List _, ∀a ∉ I, [[ A^a <->* A'^a ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct
  have ⟨A1, Teq1, I1, AA1⟩:= AT.preserve_shape_forall
  have ⟨A2, Teq2, I2, A'A2⟩ := A'T.preserve_shape_forall
  subst T; cases Teq2; case refl =>
  exact ⟨rfl, I1 ++ I2, λa nin => AA1 a (by simp_all) |>.est_of.trans <| A'A2 a (by simp_all) |>.est_of.symm⟩

theorem inj_prod (Aest: [[ ⊗A <->* ⊗A' ]]): [[ A <->* A' ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_prod
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_prod
  subst T; cases Teq2; case refl =>
  exact AA1.est_of.trans A'A2.est_of.symm

theorem inj_sum (Aest: [[ ⊕A <->* ⊕A' ]]): [[ A <->* A' ]] := by
  have ⟨T, AT, A'T⟩ := Aest.common_reduct
  have ⟨A1, Teq1, AA1⟩:= AT.preserve_shape_sum
  have ⟨A2, Teq2, A'A2⟩ := A'T.preserve_shape_sum
  subst T; cases Teq2; case refl =>
  exact AA1.est_of.trans A'A2.est_of.symm

theorem inj_list (Aest: [[ { </ A@i // i in [:n] /> } <->* { </ B@i // i in [:n'] /> } ]]): n = n' ∧ [[ </ A@i <->* B@i // i in [:n] /> ]] := by
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
