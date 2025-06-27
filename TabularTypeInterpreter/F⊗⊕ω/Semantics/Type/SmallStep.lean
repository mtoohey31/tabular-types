import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Kinding
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.TypeValue

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax A " -> " B : SmallStep

judgement SmallStep where

────────────────────────── lamApp
(λ a : K. W₀) W₁ -> W₀^^W₁

──────────────────────────────────────────────────────────── listAppList
W₀ {</ W₁@i // i in [:n] />} -> {</ W₀ W₁@i // i in [:n] />}

─────────────────────── listAppId
(λ a : K. a$0) ⟦W⟧ -> W

──────────────────────────────────────────────── listAppComp
W₀ ⟦(λ a : K. W₁) ⟦W₂⟧⟧ -> (λ a : K. W₀ W₁) ⟦W₂⟧

∀ a ∉ I, A^a -> A'^a
───────────────────────── lam (I : List TypeVarId)
λ a : K. A -> λ a : K. A'

A -> A'
─────────── appl
A B -> A' B

A -> A'
─────────── appr
W A -> W A'

∀ a ∉ I, A^a -> A'^a
───────────────────────── «forall» (I : List TypeVarId)
∀ a : K. A -> ∀ a : K. A'

A -> A'
─────────────── arrl
A → B -> A' → B

A -> A'
─────────────── arrr
W → A -> W → A'

A -> A'
─────────────────────────────────────────────────────────────────────────────────────────────────────────── list
{</ W@i // i in [:m] />, A, </ B@j // j in [:n] />} -> {</ W@i // i in [:m] />, A', </ B@j // j in [:n] />}

A -> A'
─────────────── listAppl
A ⟦B⟧ -> A' ⟦B⟧

A -> A'
─────────────── listAppr
W ⟦A⟧ -> W ⟦A'⟧

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

theorem Type.IsTypeValue.TypeVar_open_drop : IsTypeValue (TypeVar_open A a n) → IsTypeValue A := sorry

theorem Type.IsTypeValue.TypeVar_subst : IsTypeValue A → IsTypeValue B → IsTypeValue (TypeVar_subst A a B) := sorry

namespace SmallStep

theorem TypeVar_subst_preservation_of_not_mem_freeTypeVars (Ast : [[A -> B]])
  : [[A[W / a] -> B[W / a] ]] := by match Ast with
  | .lamApp .. => sorry
  | .listAppList .. => sorry
  | .listAppId .. => sorry
  | .listAppComp .. => sorry
  | .lam .. => sorry
  | .appl A'st =>
    rw [Type.TypeVar_subst, Type.TypeVar_subst]
    exact .appl A'st.TypeVar_subst_preservation_of_not_mem_freeTypeVars
  | .appr B'st (W := W') =>
    rw [Type.TypeVar_subst, Type.TypeVar_subst]
    exact .appr (W := ⟨_, W'.property.TypeVar_subst W.property⟩)
      B'st.TypeVar_subst_preservation_of_not_mem_freeTypeVars
  | .forall .. => sorry
  | .arrl A'st =>
    rw [Type.TypeVar_subst, Type.TypeVar_subst]
    exact .arrl A'st.TypeVar_subst_preservation_of_not_mem_freeTypeVars
  | .arrr B'st (W := W') =>
    rw [Type.TypeVar_subst, Type.TypeVar_subst]
    exact .arrr (W := ⟨_, W'.property.TypeVar_subst W.property⟩)
      B'st.TypeVar_subst_preservation_of_not_mem_freeTypeVars
  | .list .. => sorry
  | .listAppl A'st =>
    rw [Type.TypeVar_subst, Type.TypeVar_subst]
    exact .listAppl A'st.TypeVar_subst_preservation_of_not_mem_freeTypeVars
  | .listAppr B'st (W := W') =>
    rw [Type.TypeVar_subst, Type.TypeVar_subst]
    exact .listAppr (W := ⟨_, W'.property.TypeVar_subst W.property⟩)
      B'st.TypeVar_subst_preservation_of_not_mem_freeTypeVars
  | .prod .. => sorry
  | .sum .. => sorry

theorem progress (Aki : [[Δ ⊢ A : K]]) : A.IsTypeValue ∨ ∃ B, [[A -> B]] := match A, Aki with
  | .var _, .var _ => .inl .var
  | .lam K A', .lam I A'ki => by
    let ⟨a, anin⟩ := I.exists_fresh
    match progress <| A'ki a anin with
    | .inl A'TV => exact .inl <| .lam A'TV.TypeVar_open_drop
    | .inr ⟨A'', A'st⟩ =>
      refine .inr ⟨.lam K (A''.TypeVar_close a), .lam I ?_⟩
      intro a anin
      rw [Type.Type_open_var, Type.Type_open_var,
          Type.TypeVarLocallyClosed.Type_open_TypeVar_close_eq_TypeVar_subst sorry]
      sorry
  | .app A' B', .app A'ki B'ki => match progress A'ki with
    | .inl A'TV => match progress B'ki with
      | .inl B'TV => sorry
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .appr (W := ⟨_, A'TV⟩) B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .appl A'st⟩
  | .forall _ A', _ => sorry
  | .arr A' B', .arr A'ki B'ki => match progress A'ki with
    | .inl A'TV => match progress B'ki with
      | .inl B'TV => .inl <| .arr A'TV B'TV
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .arrr (W := ⟨_, A'TV⟩) B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .arrl A'st⟩
  | .list A', _ => sorry
  | .listApp A' B', .listApp A'ki B'ki => match progress A'ki with
    | .inl A'TV => match progress B'ki with
      | .inl B'TV => sorry
      | .inr ⟨B'', B'st⟩ => .inr ⟨_, .listAppr (W := ⟨_, A'TV⟩) B'st⟩
    | .inr ⟨A'', A'st⟩ => .inr ⟨_, .listAppl A'st⟩
  | .prod A', .prod A'ki => match progress A'ki with
    | .inl A'TV => .inl <| .prod A'TV
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .prod A'stB'⟩
  | .sum A', .sum A'ki => match progress A'ki with
    | .inl A'TV => .inl <| .sum A'TV
    | .inr ⟨B', A'stB'⟩ => .inr ⟨_, .sum A'stB'⟩

theorem Kinding_preservation (Δwf : [[⊢ Δ]]) : [[A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ B : K]]
  | .lamApp (W₀ := W₀), .app (.lam I W₀ki) W₁ki =>
    let ⟨a, anin⟩ := W₀.val.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninW₀, aninI⟩ := List.not_mem_append'.mp anin
    W₀ki a aninI |>.Type_open_preservation aninW₀ W₁ki
  | .listAppList, _ => sorry
  | .listAppId, .listApp (.lam I aki) Wki => by
    let ⟨a, anin⟩ := I.exists_fresh
    specialize aki a anin
    rw [Type.TypeVar_open, if_pos rfl] at aki
    let .var .head := aki
    exact Wki
  | .listAppComp, .listApp W₀ki (.listApp (.lam I W₁ki) W₂ki) => by
    refine .listApp (.lam (I ++ Δ.typeVarDom) (fun a anin => ?_)) W₂ki
    let ⟨aninI, aninΔ⟩ := List.not_mem_append'.mp anin
    rw [Type.TypeVar_open, W₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
    exact .app (W₀ki.weakening (Δwf.typeVarExt aninΔ) (Δ' := .typeExt .empty ..) (Δ'' := .empty)) <|
      W₁ki a aninI
  | .lam I A'st, .lam I' A'ki => .lam (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact Kinding_preservation (Δwf.typeVarExt aninΔ) (A'st a aninI) <| A'ki a aninI'
  | .appl A'st, .app A'ki B'ki => .app (A'st.Kinding_preservation Δwf A'ki) B'ki
  | .appr B'st, .app A'ki B'ki => .app A'ki <| B'st.Kinding_preservation Δwf B'ki
  | .arrl A'st, .arr A'ki B'ki => .arr (A'st.Kinding_preservation Δwf A'ki) B'ki
  | .arrr B'st, .arr A'ki B'ki => .arr A'ki <| B'st.Kinding_preservation Δwf B'ki
  | .forall I A'st, .scheme I' A'ki => .scheme (I ++ I' ++ Δ.typeVarDom) <| by
      intro a anin
      let ⟨aninII', aninΔ⟩ := List.not_mem_append'.mp anin
      let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
      exact Kinding_preservation (Δwf.typeVarExt aninΔ) (A'st a aninI) <| A'ki a aninI'
  | .list A'st, ki => sorry
  | .listAppl A'st, .listApp A'ki B'ki => .listApp (A'st.Kinding_preservation Δwf A'ki) B'ki
  | .listAppr B'st, .listApp A'ki B'ki => .listApp A'ki <| B'st.Kinding_preservation Δwf B'ki
  | .prod A'st, .prod A'ki => .prod <| A'st.Kinding_preservation Δwf A'ki
  | .sum A'st, .sum A'ki => .sum <| A'st.Kinding_preservation Δwf A'ki

theorem Equivalence_of : [[A -> B]] → [[Δ ⊢ A : K]] → [[Δ ⊢ A ≡ B]]
  | .lamApp, .app (.lam I _) W₁ki => TypeEquivalence.lamApp W₁ki
  | .listAppList, _ => sorry
  | .listAppId, .listApp (.lam I aki) Wki => .listAppId Wki
  | .listAppComp, .listApp W₀ki (.listApp (.lam I W₁ki) W₂ki) =>
    .listAppComp W₀ki.TypeVarLocallyClosed_of
  | .lam I A'st, .lam I' A'ki => sorry
  | .appl A'st, .app A'ki B'ki => sorry
  | .appr B'st, .app A'ki B'ki => sorry
  | .arrl A'st, .arr A'ki B'ki => sorry
  | .arrr B'st, .arr A'ki B'ki => sorry
  | .forall I A'st, .scheme I' A'ki => sorry
  | .list A'st, ki => sorry
  | .listAppl A'st, .listApp A'ki B'ki => sorry
  | .listAppr B'st, .listApp A'ki B'ki => sorry
  | .prod A'st, .prod A'ki => sorry
  | .sum A'st, .sum A'ki => sorry

end SmallStep

namespace MultiSmallStep

theorem trans (A₀mst : [[A₀ ->* A₁]]) (A₁mst : [[A₁ ->* A₂]]) : [[A₀ ->* A₂]] := by
  induction A₀mst with
  | refl => exact A₁mst
  | step A₀st _ ih => exact step A₀st <| ih A₁mst

theorem Kinding_preservation (Amst : [[A ->* B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ B : K]] := by
  induction Amst with
  | refl => exact Aki
  | step Ast _ ih => exact ih <| Ast.Kinding_preservation Δwf Aki

theorem EqSmallStep_of (Amst : [[A ->* B]]) : [[A <->* B]] := by
  induction Amst with
  | refl => exact .refl
  | step Ast _ ih => exact .trans (.step Ast) ih

theorem Equivalence_of (Amst : [[A ->* B]]) (Aki : [[Δ ⊢ A : K]]) (Δwf : [[⊢ Δ]])
  : [[Δ ⊢ A ≡ B]] := by
  induction Amst with
  | refl => exact .refl
  | step Ast _ ih => exact .trans (Ast.Equivalence_of Aki) <| ih <| Ast.Kinding_preservation Δwf Aki

theorem of_Equivalence (equ : [[Δ ⊢ A ≡ᵢ B]]) : [[A ->* B]] := by
  induction equ with
  | refl => exact refl
  | prod equ' ih =>
    clear equ'
    induction ih with
    | refl => exact .refl
    | step Ast _ ih => exact .step Ast.prod ih
  | sum equ' ih =>
    clear equ'
    induction ih with
    | refl => exact .refl
    | step Ast _ ih => exact .step Ast.sum ih

end MultiSmallStep

end TabularTypeInterpreter.«F⊗⊕ω»
