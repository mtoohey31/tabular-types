import Mathlib.Tactic
import TabularTypeInterpreter.Data.Range
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Basic

namespace TabularTypeInterpreter.«F⊗⊕ω»

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
      have fresh := wf.append_typeVar_fresh_r a (by constructor)
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
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
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

local instance : Inhabited «Type» where
  default := .list []
in
theorem ind_evidence (Δwf : [[⊢ Δ]])
  (Aki : [[Δ ⊢ A : L K]])
  (Bᵣki : ∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀,
    [[Δ, aₗ : *, aₜ : K, aₚ : L K, aᵢ : L K, aₙ : L K ⊢ Bᵣ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1^aₙ : *]])
  (Bₗki : ∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, [[Δ, aᵢ : L K, aₙ : L K ⊢ Bₗ^aᵢ#1^aₙ : *]])
  : [[Δ ⊢ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → (⊗ { }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1) → (aₘ$0 { }) → aₘ$0 A : *]] := by
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
  rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_id, Bᵣlc.TypeVar_open_id,
      Bₗlc.weaken (n := 3).TypeVar_open_id]
  apply arr
  · apply scheme <| I₀ ++ aₘ :: Δ.typeVarDom
    intro aₗ aₗnin
    let ⟨aₗninI₀, aₗninΔ⟩ := List.not_mem_append'.mp aₗnin
    let Δaₘaₗwf := Δaₘwf.typeVarExt aₗninΔ (K := .star)
    let aₘneaₗ := List.ne_of_not_mem_cons aₗninΔ
    symm at aₘneaₗ
    simp [Type.TypeVar_open]
    rw [Bₗlc.weaken (n := 2).TypeVar_open_id]
    apply scheme <| aₗ :: I₀ ++ aₗ :: aₘ :: Δ.typeVarDom
    intro aₜ aₜnin
    let ⟨aₜninI₀, aₜninΔ⟩ := List.not_mem_append'.mp aₜnin
    let Δaₘaₗaₜwf := Δaₘaₗwf.typeVarExt aₜninΔ (K := K)
    let aₗneaₜ := List.ne_of_not_mem_cons aₜninI₀
    let aₘneaₜ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₜninΔ
    symm at aₗneaₜ aₘneaₜ
    simp [Type.TypeVar_open]
    rw [Bₗlc.weaken (n := 1).TypeVar_open_id]
    apply scheme <| aₜ :: aₗ :: I₀ ++ aₜ :: aₗ :: aₘ :: Δ.typeVarDom
    intro aₚ aₚnin
    let ⟨aₚninI₀, aₚninΔ⟩ := List.not_mem_append'.mp aₚnin
    let Δaₘaₗaₜaₚwf := Δaₘaₗaₜwf.typeVarExt aₚninΔ (K := K.list)
    let aₗneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₚninI₀
    let aₘneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| aₚninΔ
    symm at aₗneaₚ aₘneaₚ
    simp [Type.TypeVar_open]
    rw [Bₗlc.TypeVar_open_id]
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
    let aᵢneaₙ := List.ne_of_not_mem_cons aₙninI₀
    symm at aᵢneaₙ aₚneaₙ aₗneaₙ aₘneaₙ
    simp [Type.TypeVar_open]
    apply arr <| Bᵣki _ aₗninI₀ _ aₜninI₀ _ aₚninI₀ _ aᵢninI₀ _ aₙninI₀ |>.weakening Δaₘaₗaₜaₚaᵢaₙwf
      (Δ := Δ)
      (Δ' := .typeExt .empty ..)
      (Δ'' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
    apply arr <| Bₗki _ aᵢninI₁ _ aₙninI₁ |>.weakening Δaₘaₗaₜaₚaᵢaₙwf
      (Δ := Δ)
      (Δ' := .typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..)
      (Δ'' := .typeExt (.typeExt .empty ..) ..)
    · apply arr .unit
      apply arr
      · apply app
        · exact var <| .typeVarExt (.typeVarExt (.typeVarExt
             (.typeVarExt (.typeVarExt .head aₘneaₗ) aₘneaₜ) aₘneaₚ) aₘneaᵢ) aₘneaₙ
        · exact var <| .typeVarExt (.typeVarExt .head aₚneaᵢ) aₚneaₙ
      · apply app
        · exact var <| .typeVarExt (.typeVarExt (.typeVarExt
             (.typeVarExt (.typeVarExt .head aₘneaₗ) aₘneaₜ) aₘneaₚ) aₘneaᵢ) aₘneaₙ
        · exact var <| .typeVarExt .head aᵢneaₙ
  · apply arr
    · apply app
      · exact var .head
      · rw [← Std.Range.map_get!_eq (as := []), Std.Range.map, ← List.map_singleton_flatten,
            ← Std.Range.map]
        exact list fun _ => (nomatch ·)
    · apply app
      · exact var .head
      · exact Aki.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) Δaₘwf

theorem id : [[Δ ⊢ λ a : K. a$0 : K ↦ K]] := by
  apply lam []
  intro a anin
  rw [Type.TypeVar_open, if_pos rfl]
  exact var .head

end Kinding

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

end TabularTypeInterpreter.«F⊗⊕ω»
