import Aesop
import Lott.Data.Option
import TabularTypeInterpreter.Interpreter.«λπι»
import TabularTypeInterpreter.Interpreter.Basic

namespace TabularTypeInterpreter

namespace Interpreter

abbrev ElabM := StateM Nat

def freshId : ElabM «λπι».Id := do
  let nextFresh ← getModify Nat.succ
  return { val := nextFresh }

instance : Coe MId «λπι».Id where
  coe | { val } => { val }

instance : Coe «λπι».Id MId where
  coe | { val } => { val }

open Std

namespace Monotype

def subst (τ τ' : Monotype) (i : TId) : Monotype := match τ with
  | var i' => if i = i' then τ' else var i'
  | uvar x => uvar x
  | lam i' κ τ'' => lam i' κ <| if i = i' then τ'' else subst τ'' τ' i
  | app ϕ τ'' => app (subst ϕ τ' i) (subst τ'' τ' i)
  | arr τ₀ τ₁ => arr (subst τ₀ τ' i) (subst τ₁ τ' i)
  | label s => label s
  | floor ξ => floor <| subst ξ τ' i
  | comm u => comm u
  | row ξτ''s κ? => row (ξτ''s.mapMem fun (ξ, τ'') _ => (subst ξ τ' i, subst τ'' τ' i)) κ?
  | prodOrSum Ξ μ => prodOrSum Ξ <| subst μ τ' i
  | lift ϕ => lift <| subst ϕ τ' i
  | contain ρ₀ μ ρ₁ => contain (subst ρ₀ τ' i) (subst μ τ' i) (subst ρ₁ τ' i)
  | concat ρ₀ μ ρ₁ ρ₂ => concat (subst ρ₀ τ' i) (subst μ τ' i) (subst ρ₁ τ' i) (subst ρ₂ τ' i)
  | tc s => tc s
  | all ϕ => all <| subst ϕ τ' i
  | ind ρ => ind <| subst ρ τ' i
  | split ϕ ρ₀ ρ₁ ρ₂ => split (subst ϕ τ' i) (subst ρ₀ τ' i) (subst ρ₁ τ' i) (subst ρ₂ τ' i)
  | list => list
  | int => int
  | str => str
  | «alias» s => «alias» s
termination_by sizeOf τ
decreasing_by
  all_goals simp_arith
  all_goals (
    apply Nat.le_add_right_of_le
    apply Nat.le_of_lt <| Nat.lt_of_le_of_lt (m := sizeOf (ξ, τ'')) _ <| List.sizeOf_lt_of_mem ..
    · simp_arith
    · assumption
  )

@[simp]
def solve (τ τ' : Monotype) (x : UId) : Monotype := match τ with
  | var i => var i
  | uvar x' => if x = x' then τ' else uvar x'
  | lam i κ τ'' => lam i κ <| solve τ'' τ' x
  | app ϕ τ'' => app (solve ϕ τ' x) (solve τ'' τ' x)
  | arr τ₀ τ₁ => arr (solve τ₀ τ' x) (solve τ₁ τ' x)
  | label s => label s
  | floor ξ => floor <| solve ξ τ' x
  | comm u => comm u
  | row ξτ''s κ? => row (ξτ''s.mapMem fun (ξ, τ'') _ => (solve ξ τ' x, solve τ'' τ' x)) κ?
  | prodOrSum Ξ μ => prodOrSum Ξ <| solve μ τ' x
  | lift ϕ => lift <| solve ϕ τ' x
  | contain ρ₀ μ ρ₁ => contain (solve ρ₀ τ' x) (solve μ τ' x) (solve ρ₁ τ' x)
  | concat ρ₀ μ ρ₁ ρ₂ => concat (solve ρ₀ τ' x) (solve μ τ' x) (solve ρ₁ τ' x) (solve ρ₂ τ' x)
  | tc s => tc s
  | all ϕ => all <| solve ϕ τ' x
  | ind ρ => ind <| solve ρ τ' x
  | split ϕ ρ₀ ρ₁ ρ₂ => split (solve ϕ τ' x) (solve ρ₀ τ' x) (solve ρ₁ τ' x) (solve ρ₂ τ' x)
  | list => list
  | int => int
  | str => str
  | «alias» s => «alias» s
termination_by sizeOf τ
decreasing_by
  all_goals simp_arith
  all_goals (
    apply Nat.le_add_right_of_le
    apply Nat.le_of_lt <| Nat.lt_of_le_of_lt (m := sizeOf (ξ, τ'')) _ <| List.sizeOf_lt_of_mem ..
    · simp_arith
    · assumption
  )

theorem subst_id_of_not_mem (nmem : i ∉ τ) : subst τ τ' i = τ := by
  induction τ using rec (motive_2 := fun ξτs => ∀ ξτ ∈ ξτs, let (ξ, τ) := ξτ;
      (i ∉ ξ → subst ξ τ' i = ξ) ∧ (i ∉ τ → subst τ τ' i = τ))
    (motive_3 := fun (ξ, τ) => (i ∉ ξ → subst ξ τ' i = ξ) ∧ (i ∉ τ → subst τ τ' i = τ))
  case lam ih =>
    dsimp [Membership.mem.eq_def (self := instMembershipTId), instMembershipTId] at nmem
    rw [freeTIds] at nmem
    rw [subst]
    split
    · case isTrue h => rfl
    · case isFalse h =>
      congr
      exact ih <| List.not_mem_of_not_mem_eraseAll nmem h
  case cons ih₀ ih₁ ξτ mem =>
    let ⟨_, _⟩ := ξτ
    constructor
    · intro nmem
      cases mem with
      | head =>
        exact ih₀ |>.left nmem
      | tail _ mem => exact ih₁ _ mem |>.left nmem
    · intro nmem
      cases mem with
      | head =>
        exact ih₀ |>.right nmem
      | tail _ mem => exact ih₁ _ mem |>.right nmem
  case row ih =>
    rw [subst, List.mapMem_eq_map]
    apply Monotype.row.injEq .. |>.mpr ⟨_, rfl⟩
    apply List.map_eq_id_of_eq_id_of_mem
    rintro ⟨ξ, τ⟩ mem
    congr
    · apply ih _ mem |>.left
      dsimp [Membership.mem.eq_def (self := instMembershipTId), instMembershipTId] at nmem
      rw [freeTIds, List.mapMem_eq_map] at nmem
      apply List.not_mem_append' (ys := τ.freeTIds).mp .. |>.left
      exact List.not_mem_flatten.mp nmem _ <| List.mem_map.mpr ⟨_, mem, rfl⟩
    · apply ih _ mem |>.right
      dsimp [Membership.mem.eq_def (self := instMembershipTId), instMembershipTId] at nmem
      rw [freeTIds, List.mapMem_eq_map] at nmem
      apply List.not_mem_append' (xs := ξ.freeTIds).mp .. |>.right
      exact List.not_mem_flatten.mp nmem _ <| List.mem_map.mpr ⟨_, mem, rfl⟩
  all_goals aesop (add simp
    [subst, (Membership.mem.eq_def (self := instMembershipTId)), instMembershipTId, freeTIds])

theorem solve_subst_distrib (nmem : i ∉ τ'')
  : solve (subst τ τ' i) τ'' x = subst (solve τ τ'' x) (solve τ' τ'' x) i := by
  induction τ using rec (motive_2 := fun ξτs => ∀ ξτ ∈ ξτs, let (ξ, τ) := ξτ;
    solve (subst ξ τ' i) τ'' x = subst (solve ξ τ'' x) (solve τ' τ'' x) i ∧
    solve (subst τ τ' i) τ'' x = subst (solve τ τ'' x) (solve τ' τ'' x) i)
    (motive_3 := fun (ξ, τ) =>
      solve (subst ξ τ' i) τ'' x = subst (solve ξ τ'' x) (solve τ' τ'' x) i ∧
      solve (subst τ τ' i) τ'' x = subst (solve τ τ'' x) (solve τ' τ'' x) i)
  case var =>
    rw [subst]
    split
    · case isTrue h => rw [solve, subst, if_pos h]
    · case isFalse h => rw [solve, subst, if_neg h]
  case uvar =>
    rw [subst, solve]
    split
    · case isTrue h => rw [subst_id_of_not_mem nmem]
    · case isFalse h => rw [subst]
  case row ih =>
    simp [subst, solve]
    intro _ _ mem
    exact ih _ mem
  case cons ih₀ ih₁ _ mem =>
    cases mem with
    | head =>
      exact ih₀
    | tail =>
      apply ih₁
      assumption
  all_goals aesop (add simp [solve, subst])

def multiSubst (τ : Monotype) : List (Monotype × TId) → Monotype
  | [] => τ
  | (τ', i) :: τ'is => τ.subst τ' i |>.multiSubst τ'is

theorem multiSubst_append
  : multiSubst (multiSubst τ τ'is) τ''is = multiSubst τ (τ'is ++ τ''is) := by
  cases τ'is with
  | nil => rw [multiSubst, List.nil_append]
  | cons => rw [multiSubst, List.cons_append, multiSubst, multiSubst_append]

theorem solve_multiSubst_distrib
  (dj : τis.map Prod.snd |>.Disjoint τ'.freeTIds)
  : solve (multiSubst τ τis) τ' x =
    multiSubst (solve τ τ' x) (τis.map fun (τ, i) => (solve τ τ' x, i)) := by
  rcases τis.cases_snoc with rfl | ⟨_, _, rfl⟩
  · rw [multiSubst, List.map_nil, multiSubst]
  · rw [← multiSubst_append, List.map_append, List.map_singleton, ← multiSubst_append, multiSubst,
         multiSubst, solve_subst_distrib, solve_multiSubst_distrib, multiSubst, multiSubst]
    swap
    apply dj
    rw [List.map_append, List.map_singleton]
    exact List.mem_append.mpr <| .inr <| .head _
    intro _ mem
    apply dj
    rw [List.map_append]
    exact List.mem_append.mpr <| .inl mem
termination_by sizeOf τis
decreasing_by
  rename τis = _ => eq
  subst eq
  apply List.sizeOf_lt_sizeOf_append_right
  simp_arith

inductive CommutativityPartialOrdering : Monotype → Monotype → Prop where
  | refl : CommutativityPartialOrdering μ μ
  | non : CommutativityPartialOrdering (comm .non) μ
  | comm : CommutativityPartialOrdering μ (comm .comm)

instance : Decidable (CommutativityPartialOrdering μ₀ μ₁) :=
  if heq : μ₀ = μ₁ then  by cases heq; exact isTrue .refl
  else if hnon : μ₀ = .comm .non then by cases hnon; exact isTrue .non
  else if hcomm : μ₁ = .comm .comm then by cases hcomm; exact isTrue .comm
  else by
    apply isFalse
    intro ordering
    cases ordering with
    | refl => nomatch heq
    | non => nomatch hnon
    | comm => nomatch hcomm

theorem CommutativityPartialOrdering.solve
  : CommutativityPartialOrdering μ₀ μ₁ → CommutativityPartialOrdering (μ₀.solve τ x) (μ₁.solve τ x)
  | .refl => .refl
  | .non => by
    rw [Monotype.solve]
    exact .non
  | .comm => by
    rw [Monotype.solve]
    exact .comm

inductive RowEquivalence : Monotype → Monotype → Monotype → Type where
  | refl : RowEquivalence ρ μ ρ
  | trans : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence ρ₁ μ ρ₂ → RowEquivalence ρ₀ μ ρ₂
  | comm : List.Perm ξτs₀ ξτs₁ → RowEquivalence (row ξτs₀ κ₀?) (comm .comm) (row ξτs₁ κ₁?)
  | liftL : RowEquivalence ((lift ϕ).app (row ξτs κ₀?)) μ
      (row (ξτs.map fun (ξ, τ) => (ξ, ϕ.app τ)) κ₁?)
  | liftR : RowEquivalence (row (ξτs.map fun (ξ, τ) => (ξ, ϕ.app τ)) κ₀?) μ
      ((lift ϕ).app (row ξτs κ₁?))

namespace RowEquivalence

def symm : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence ρ₁ μ ρ₀
  | refl => refl
  | trans ρ₀₁re ρ₁₂re => trans ρ₁₂re.symm ρ₀₁re.symm
  | comm perm => comm perm.symm
  | liftL => liftR
  | liftR => liftL

def prodElab : RowEquivalence ρ₀ μ ρ₁ → ElabM «λπι».Term
  | refl | liftL | liftR => return .id
  | trans ρ₀₁re ρ₁₂re => do
    let i ← freshId
    let F₀₁ ← ρ₀₁re.prodElab
    let F₁₂ ← ρ₁₂re.prodElab
    return .lam i <| F₁₂.app <| F₀₁.app <| .var i
  | comm _ (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) => do
    let i ← freshId
    return .lam i <| .prodIntro <| ξτs₁.map fun (ξ₁, _) =>
      .prodElim (ξτs₀.findIdx (·.fst == ξ₁)) <| .var i

def sumElab : RowEquivalence ρ₀ μ ρ₁ → ElabM «λπι».Term
  | refl | liftL | liftR => return .id
  | trans ρ₀₁re ρ₁₂re => do
    let i ← freshId
    let F₀₁ ← ρ₀₁re.sumElab
    let F₁₂ ← ρ₁₂re.sumElab
    return .lam i <| F₁₂.app <| F₀₁.app <| .var i
  | comm _ (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) => do
    let i ← freshId
    return .lam i <| .sumElim (.var i) <| ← ξτs₀.mapM fun (ξ₀, _) => do
      let i ← freshId
      return .lam i <| .sumIntro (ξτs₁.findIdx (·.fst == ξ₀)) <| .var i

def solve : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence (ρ₀.solve τ x) (μ.solve τ x) (ρ₁.solve τ x)
  | .refl => .refl
  | .trans re₀₁ re₁₂ => re₀₁.solve.trans re₁₂.solve
  | .comm perm => by
    rw [Monotype.solve, Monotype.solve, List.mapMem_eq_map, Monotype.solve, List.mapMem_eq_map]
    exact .comm <| perm.map _
  | .liftL (ϕ := ϕ) (ξτs := ξτs) => by
    rw [Monotype.solve, Monotype.solve, List.mapMem_eq_map, Monotype.solve, List.mapMem_eq_map,
        Monotype.solve, List.map_map,
        List.map_eq_map_iff (f := _ ∘ _)
          (g := (fun (ξ, τ') => (ξ, ((ϕ.solve τ x).app τ'))) ∘
            (fun (ξ, τ') => (ξ.solve τ x, τ'.solve τ x))) (l := ξτs).mpr (by
          intros
          simp
        ), ← List.map_map]
    exact .liftL
  | .liftR (ϕ := ϕ) (ξτs := ξτs) => by
    rw [Monotype.solve, Monotype.solve, List.mapMem_eq_map, Monotype.solve, List.mapMem_eq_map,
        Monotype.solve, List.map_map,
        List.map_eq_map_iff (f := _ ∘ _)
          (g := (fun (ξ, τ') => (ξ, ((ϕ.solve τ x).app τ'))) ∘
            (fun (ξ, τ') => (ξ.solve τ x, τ'.solve τ x))) (l := ξτs).mpr (by
          intros
          simp
        ), ← List.map_map]
    exact .liftR

end RowEquivalence

structure Instance where
  tids : List TId
  prereqs : List Monotype
  mids : List MId
  name : String
  target : Monotype
  memberElab : «λπι».Term
  superclassElab : List «λπι».Term

inductive ConstraintSolution : Monotype → Type where
  | local : «λπι».Id → ConstraintSolution ψ
  | containTrans : ConstraintSolution (contain ρ₀ μ ρ₁) → ConstraintSolution (contain ρ₁ μ ρ₂) →
    ConstraintSolution (contain ρ₀ μ ρ₂)
  | containConcat : ConstraintSolution (concat ρ₀ μ ρ₁ ρ₂) →
    ConstraintSolution (concat ρ₃ μ ρ₄ ρ₅) → ConstraintSolution (contain ρ₀ μ ρ₃) →
    ConstraintSolution (contain ρ₁ μ ρ₄) → ConstraintSolution (contain ρ₂ μ ρ₅)
  | concatConcrete : ConstraintSolution (concat (row ξτs₀ (.someIf b₀ κ)) (comm .non)
      (row ξτs₁ (.someIf b₁ κ)) (row (ξτs₀ ++ ξτs₁) (.someIf b₁ κ)))
  | concatEmptyL : ConstraintSolution (concat (row .nil (some κ)) (comm .non) ρ ρ)
  | concatEmptyR : ConstraintSolution (concat ρ (comm .non) (row .nil (some κ)) ρ)
  | concatAssocL : ConstraintSolution (concat ρ₀ μ ρ₁ ρ₃) → ConstraintSolution (concat ρ₁ μ ρ₂ ρ₄) →
    ConstraintSolution (concat ρ₀ μ ρ₄ ρ₅) → ConstraintSolution (concat ρ₃ μ ρ₂ ρ₅)
  | concatAssocR : ConstraintSolution (concat ρ₀ μ ρ₁ ρ₃) → ConstraintSolution (concat ρ₁ μ ρ₂ ρ₄) →
    ConstraintSolution (concat ρ₃ μ ρ₂ ρ₅) → ConstraintSolution (concat ρ₀ μ ρ₄ ρ₅)
  | concatSwap : ConstraintSolution (concat ρ₀ (comm .comm) ρ₁ ρ₂) →
    ConstraintSolution (concat ρ₁ (comm .comm) ρ₀ ρ₂)
  | concatContainL : ConstraintSolution (concat ρ₀ μ ρ₁ ρ₂) → ConstraintSolution (contain ρ₀ μ ρ₂)
  | concatContainR : ConstraintSolution (concat ρ₀ μ ρ₁ ρ₂) → ConstraintSolution (contain ρ₁ μ ρ₂)
  | containDecay : ConstraintSolution (contain ρ₀ μ₀ ρ₁) → CommutativityPartialOrdering μ₀ μ₁ →
    ConstraintSolution (contain ρ₀ μ₁ ρ₁)
  | concatDecay : ConstraintSolution (concat ρ₀ μ₀ ρ₁ ρ₂) → CommutativityPartialOrdering μ₀ μ₁ →
    ConstraintSolution (concat ρ₀ μ₁ ρ₁ ρ₂)
  | liftContain : ConstraintSolution (contain ρ₀ μ ρ₁) →
    ConstraintSolution (contain ((lift ϕ).app ρ₀) μ ((lift ϕ).app ρ₁))
  | liftConcat : ConstraintSolution (concat ρ₀ μ ρ₁ ρ₂) →
    ConstraintSolution (concat ((lift ϕ).app ρ₀) μ ((lift ϕ).app ρ₁) ((lift ϕ).app ρ₂))
  | tcInst : (inst : Instance) → (τ's : List Monotype) →
    (∀ ψ ∈ inst.prereqs, ConstraintSolution (ψ.multiSubst (τ's.zip inst.tids))) →
    ConstraintSolution ((tc inst.name).app (inst.target.multiSubst (τ's.zip inst.tids)))
  | tcSuper : ConstraintSolution ((tc s₀).app τ) → Nat → ConstraintSolution ((tc s₁).app τ)
  | allEmpty : ConstraintSolution ((all ϕ).app (row .nil (some .constr)))
  | allSingletonIntro : ConstraintSolution (ϕ.app τ) →
    ConstraintSolution ((all ϕ).app (row [(ξ, τ)] κ?))
  | allSingletonElim : ConstraintSolution ((all ϕ).app (row [(ξ, τ)] κ?)) →
    ConstraintSolution (ϕ.app τ)
  | allContain : ConstraintSolution (contain ρ₀ (comm .comm) ρ₁) →
    ConstraintSolution ((all ϕ).app ρ₁) → ConstraintSolution ((all ϕ).app ρ₀)
  | allConcat : ConstraintSolution (concat ρ₀ (comm .comm) ρ₁ ρ₂) →
    ConstraintSolution ((all ϕ).app ρ₀) → ConstraintSolution ((all ϕ).app ρ₁) →
    ConstraintSolution ((all ϕ).app ρ₂)
  | ind : ConstraintSolution (row ξτs κ?)
  | splitEmpty : ConstraintSolution
    (split ϕ (row [] (some κ)) (row [] (some star)) (row [] (some star)))
  | splitSingletonMatch : ConstraintSolution
    (split ϕ (row [(ξ, τ)] (some κ)) (row .nil (some star)) (row [(ξ, ϕ.app τ)] (some star)))
  | splitSingletonRest : ConstraintSolution
    (split ϕ (row [] (some κ)) (row [(ξ, τ)] (some star)) (row [(ξ, τ)] (some star)))
  | splitPiecewise : ConstraintSolution (split ϕ ρ₀ ρ₁ ρ₂) →
    ConstraintSolution (split ϕ ρ₃ ρ₄ ρ₅) →
    ConstraintSolution (concat ((lift ϕ).app ρ₀) (comm .comm) ((lift ϕ).app ρ₃)
      ((lift ϕ).app ρ₆)) →
    ConstraintSolution (concat ρ₁ (comm .comm) ρ₄ ρ₇) →
    ConstraintSolution (concat ρ₂ (comm .comm) ρ₅ ρ₈) →
    ConstraintSolution (concat ((lift ϕ).app ρ₆) (comm .comm) ρ₇ ρ₈) →
    ConstraintSolution (split ϕ ρ₆ ρ₇ ρ₈)
  | splitConcat : ConstraintSolution (split ϕ ρ₀ ρ₁ ρ₂) →
    ConstraintSolution (concat ((lift ϕ).app ρ₀) (comm .comm) ρ₁ ρ₂)

def _root_.Nat.map : Nat → (Nat → α) → List α
  | 0, _ => []
  | n + 1, f => f n :: n.map f

def _root_.Nat.mapM [Monad m] : Nat → (Nat → m α) → m (List α)
  | 0, _ => return []
  | n + 1, f => return (← f n) :: (← n.mapM f)

variable (TC)

namespace ConstraintSolution

def «elab» : ConstraintSolution τ → ElabM «λπι».Term
  | «local» i => return .var i
  | containTrans contain₀₁cs contain₁₂cs => do
    let E ← contain₀₁cs.elab
    let F ← contain₁₂cs.elab
    let i₀ ← freshId
    let i₁ ← freshId
    return .prodIntro [
      .lam i₀ <| (E.prodElim 0).app <| (F.prodElim 0).app <| .var i₀,
      .lam i₁ <| (F.prodElim 1).app <| (E.prodElim 1).app <| .var i₁,
    ]
  | containConcat concat₂cs concat₅cs containₗcs containᵣcs => do
    let E₂ ← concat₂cs.elab
    let E₅ ← concat₅cs.elab
    let Fₗ ← containₗcs.elab
    let Fᵣ ← containᵣcs.elab
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    return .prodIntro [
      .lam i₀ <|
        ((E₂.prodElim 0).app ((Fₗ.prodElim 0).app (((E₅.prodElim 2).prodElim 0).app (.var i₀)))).app
            <| (Fᵣ.prodElim 0).app <| ((E₅.prodElim 3).prodElim 0).app <| .var i₀,
      ((E₂.prodElim 1).app
        (.lam i₁ (((E₅.prodElim 2).prodElim 1).app ((Fₗ.prodElim 1).app (.var i₁))))).app <|
        .lam i₂ <| ((E₅.prodElim 2).prodElim 1).app <| (Fₗ.prodElim 1).app <| .var i₂,
    ]
  | .concatConcrete (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) => concatConcrete ξτs₀.length ξτs₁.length
  | concatEmptyL => do
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    return .prodIntro [
      .lam i₀ <| .lam i₁ <| .var i₁,
      .lam i₂ <| .lam i₃ <| .var i₃,
      .prodIntro [
        .lam i₄ .unit,
        .lam i₅ <| .sumElim (.var i₅) [],
      ],
      .prodIntro [.id, .id],
    ]
  | concatEmptyR => do
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    return .prodIntro [
      .lam i₀ <| .lam i₁ <| .var i₀,
      .lam i₂ <| .lam i₃ <| .var i₂,
      .prodIntro [.id, .id],
      .prodIntro [
        .lam i₄ .unit,
        .lam i₅ <| .sumElim (.var i₅) [],
      ],
    ]
  | concatAssocL concat₀₁cs concat₁₂cs concat₀₄cs => do
    let E₀₁ ← concat₀₁cs.elab
    let E₁₂ ← concat₁₂cs.elab
    let E₀₄ ← concat₀₄cs.elab
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    let i₆ ← freshId
    let i₇ ← freshId
    let i₈ ← freshId
    let i₉ ← freshId
    return .prodIntro [
      .lam i₀ <| .lam i₁ <|
        ((E₀₄.prodElim 0).app (((E₀₁.prodElim 2).prodElim 0).app (.var i₀))).app <|
        ((E₁₂.prodElim 0).app (((E₀₁.prodElim 3).prodElim 0).app (.var i₀))).app <| .var i₁,
      .lam i₂ <| .lam i₃ <|
        ((E₀₄.prodElim 1).app
          (.lam i₄ (.app (.var i₂) (((E₀₁.prodElim 2).prodElim 1).app (.var i₄))))).app <|
        ((E₁₂.prodElim 1).app
          (.lam i₅ (.app (.var i₂) (((E₀₁.prodElim 3).prodElim 1).app (.var i₅))))).app <| .var i₃,
      .prodIntro [
        .lam i₆ <| ((E₀₁.prodElim 0).app (((E₀₄.prodElim 2).prodElim 0).app (.var i₆))).app <|
          ((E₁₂.prodElim 2).prodElim 0).app <| ((E₀₄.prodElim 3).prodElim 0).app <| .var i₆,
        E₀₁.prodElim 1 |>.app ((E₀₄.prodElim 2).prodElim 1) |>.app <| .lam i₇ <|
        ((E₀₄.prodElim 3).prodElim 1).app <| ((E₁₂.prodElim 2).prodElim 1).app <| .var i₇,
      ],
      .prodIntro [
        .lam i₈ <| ((E₁₂.prodElim 3).prodElim 0).app <|
          ((E₀₄.prodElim 3).prodElim 0).app <| .var i₈,
        .lam i₉ <| ((E₀₄.prodElim 3).prodElim 1).app <|
          ((E₁₂.prodElim 3).prodElim 1).app <| .var i₉,
      ],
    ]
  | concatAssocR concat₀₁cs concat₁₂cs concat₃₂cs => do
    let E₀₁ ← concat₀₁cs.elab
    let E₁₂ ← concat₁₂cs.elab
    let E₃₂ ← concat₃₂cs.elab
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    let i₆ ← freshId
    let i₇ ← freshId
    let i₈ ← freshId
    let i₉ ← freshId
    return .prodIntro [
      .lam i₀ <| .lam i₁ <|
        ((E₃₂.prodElim 0).app (((E₁₂.prodElim 3).prodElim 0).app (.var i₁))).app <|
        ((E₀₁.prodElim 0).app (.var i₀)).app <| ((E₁₂.prodElim 2).prodElim 0).app <| .var i₁,
      .lam i₂ <| .lam i₃ <|
        ((E₃₂.prodElim 1).app
          (((E₀₁.prodElim 1).app (.var i₂)).app
            (.lam i₄ (.app (.var i₃) (.app ((E₁₂.prodElim 2).prodElim 1) (.var i₄)))))).app <|
        .lam i₅ <| .app (.var i₃) <| ((E₁₂.prodElim 3).prodElim 1).app <| .var i₅,
      .prodIntro [
        .lam i₆ <| ((E₀₁.prodElim 2).prodElim 0).app <|
          ((E₃₂.prodElim 2).prodElim 0).app <| .var i₆,
        .lam i₇ <| ((E₃₂.prodElim 2).prodElim 1).app <|
          ((E₀₁.prodElim 2).prodElim 1).app <| .var i₇,
      ],
      .prodIntro [
        .lam i₈ <|
          ((E₁₂.prodElim 0).app
            (.app ((E₀₁.prodElim 3).prodElim 0)
              (.app ((E₃₂.prodElim 2).prodElim 0) (.var i₈)))).app <|
          ((E₃₂.prodElim 3).prodElim 0).app <| .var i₈,
        ((E₁₂.prodElim 1).app
          (.lam i₉ (.app ((E₃₂.prodElim 2).prodElim 1)
            (.app ((E₀₁.prodElim 3).prodElim 1) (.var i₉))))).app <|
          (E₃₂.prodElim 3).prodElim 1,
      ],
    ]
  | concatSwap concatcs => do
    let E ← concatcs.elab
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    return .prodIntro [
      .lam i₀ <| .lam i₁ <| ((E.prodElim 0).app (.var i₁)).app (.var i₀),
      .lam i₂ <| .lam i₃ <| ((E.prodElim 1).app (.var i₃)).app (.var i₂),
      E.prodElim 3,
      E.prodElim 2,
    ]
  | concatContainL concatcs => return .prodElim 2 <| ← concatcs.elab
  | concatContainR concatcs => return .prodElim 3 <| ← concatcs.elab
  | containDecay containcs _ => containcs.elab
  | concatDecay concatcs _ => concatcs.elab
  | liftContain containcs => containcs.elab
  | liftConcat concatcs => concatcs.elab
  | tcInst { prereqs, mids, memberElab, superclassElab, .. } τ's ψscs => do
    let Fs ← prereqs.mapMemM fun _ mem => ψscs _ mem |>.elab
    return .prodIntro <| (memberElab.multiSubst (Fs.zip (mids.map (fun | { val } => { val })))) ::
      superclassElab.map fun Eₛ => Eₛ.multiSubst <| Fs.zip <| mids.map fun | { val } => { val }
  | tcSuper tcτcs n => return .prodElim n.succ <| ← tcτcs.elab
  | allEmpty => return .unit
  | allSingletonIntro ϕτcs => return .prodIntro [← ϕτcs.elab]
  | allSingletonElim allcs => return .prodElim 0 <| ← allcs.elab
  | allContain containcs allcs => do
    let F ← containcs.elab
    let E ← allcs.elab
    return F.prodElim 0 |>.app E
  | allConcat concatcs all₀cs all₁cs => do
    let F ← concatcs.elab
    let E₀ ← all₀cs.elab
    let E₁ ← all₁cs.elab
    return F.prodElim 0 |>.app E₀ |>.app E₁
  | ind (ξτs := ξτs) => do
    let i₀ ← freshId
    let i₁ ← freshId
    return .lam i₀ <| .lam i₁ <| ← ξτs.length.foldM (init := .var i₁) fun i _ acc => do
      let Eₗ ← concatConcrete i 1
      let Eᵣ ← concatConcrete (i + 1) (ξτs.length - i - 1)
      return «λπι».Term.var i₀ |>.app Eₗ |>.app Eᵣ |>.app .unit |>.app acc
  | splitEmpty => concatConcrete 0 0
  | splitSingletonMatch => concatConcrete 1 0
  | splitSingletonRest => concatConcrete 0 1
  | splitPiecewise _ _ _ _ _ concatcs => concatcs.elab
  | splitConcat splitcs => splitcs.elab
where
  concatConcrete (m n : Nat) : ElabM «λπι».Term := do
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    let i₆ ← freshId
    let i₇ ← freshId
    let i₈ ← freshId
    return .prodIntro [
      .lam i₀ <| .lam i₁ <| .prodIntro <| m.map (.prodElim · (.var i₀)) ++
        n.map (.prodElim · (.var i₁)),
      .lam i₂ <| .lam i₃ <| .lam i₄ <| .sumElim (.var i₄) <|
        (← m.mapM (fun j => do
          let i ← freshId
          return .lam i <| .app (.var i₂) <| .sumIntro j (.var i))) ++
        (← n.mapM (fun j => do
          let i ← freshId
          return .lam i <| .app (.var i₃) <| .sumIntro j (.var i))),
      .prodIntro [
        .lam i₅ <| .prodIntro <| m.map (.prodElim · (.var i₅)),
        .lam i₆ <| .sumElim (.var i₆) <| ← m.mapM fun j => do
          let i ← freshId
          return .lam i <| .sumIntro j (.var i),
      ],
      .prodIntro [
        .lam i₇ <| .prodIntro <| n.map fun j => .prodElim (m + j) (.var i₇),
        .lam i₈ <| .sumElim (.var i₈) <| ← n.mapM fun j => do
          let i ← freshId
          return .lam i <| .sumIntro (m + j) (.var i),
      ],
    ]

def solve (cs : ConstraintSolution ψ) : ConstraintSolution (ψ.solve τ x) := by
  cases cs with
  | «local» i => exact .local i
  | containTrans contain₀₁cs contain₁₂cs =>
    replace contain₀₁cs := contain₀₁cs.solve (τ := τ) (x := x)
    replace contain₁₂cs := contain₁₂cs.solve (τ := τ) (x := x)
    rw [Monotype.solve] at contain₀₁cs contain₁₂cs ⊢
    exact containTrans contain₀₁cs contain₁₂cs
  | containConcat concat₂cs concat₅cs containₗcs containᵣcs =>
    replace concat₂cs := concat₂cs.solve (τ := τ) (x := x)
    replace concat₅cs := concat₅cs.solve (τ := τ) (x := x)
    replace containₗcs := containₗcs.solve (τ := τ) (x := x)
    replace containᵣcs := containᵣcs.solve (τ := τ) (x := x)
    rw [Monotype.solve] at concat₂cs concat₅cs
    rw [Monotype.solve] at containₗcs containᵣcs ⊢
    exact containConcat concat₂cs concat₅cs containₗcs containᵣcs
  | concatConcrete =>
    simp
    exact concatConcrete
  | concatEmptyL =>
    simp
    exact concatEmptyL
  | concatEmptyR =>
    simp
    exact concatEmptyR
  | concatAssocL concat₀₁cs concat₁₂cs concat₀₄cs =>
    replace concat₀₁cs := concat₀₁cs.solve (τ := τ) (x := x)
    replace concat₁₂cs := concat₁₂cs.solve (τ := τ) (x := x)
    replace concat₀₄cs := concat₀₄cs.solve (τ := τ) (x := x)
    rw [Monotype.solve] at concat₀₁cs concat₁₂cs concat₀₄cs ⊢
    exact concatAssocL concat₀₁cs concat₁₂cs concat₀₄cs
  | concatAssocR concat₀₁cs concat₁₂cs concat₃₂cs =>
    replace concat₀₁cs := concat₀₁cs.solve (τ := τ) (x := x)
    replace concat₁₂cs := concat₁₂cs.solve (τ := τ) (x := x)
    replace concat₃₂cs := concat₃₂cs.solve (τ := τ) (x := x)
    rw [Monotype.solve] at concat₀₁cs concat₁₂cs concat₃₂cs ⊢
    exact concatAssocR concat₀₁cs concat₁₂cs concat₃₂cs
  | concatSwap concatcs =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at concatcs ⊢
    exact concatSwap concatcs
  | concatContainL concatcs =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at concatcs ⊢
    exact concatContainL concatcs
  | concatContainR concatcs =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at concatcs ⊢
    exact concatContainR concatcs
  | containDecay containcs po =>
    replace containcs := containcs.solve (τ := τ) (x := x)
    replace po := po.solve (τ := τ) (x := x)
    simp at containcs po ⊢
    exact containDecay containcs po
  | concatDecay concatcs po =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    replace po := po.solve (τ := τ) (x := x)
    simp at concatcs po ⊢
    exact concatDecay concatcs po
  | liftContain containcs =>
    replace containcs := containcs.solve (τ := τ) (x := x)
    simp at containcs ⊢
    exact liftContain containcs
  | liftConcat concatcs =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at concatcs ⊢
    exact liftConcat concatcs
  | tcInst inst τ's ψscs =>
    let { tids, prereqs, mids, name, target, memberElab, superclassElab } := inst
    simp
    rw [Monotype.solve_multiSubst_distrib sorry]
    rw [List.zip_eq_zipWith, List.map_zipWith,
        ← List.zipWith_map_left (f := fun τ' => Monotype.solve τ' τ x)]
    apply tcInst {
      prereqs := prereqs.map (·.solve τ x)
      mids
      target := _
      memberElab
      superclassElab
      ..
    } _
    intro ψ mem
    rcases List.mem_of_mem_map mem with ⟨_, mem', rfl⟩
    let ψcs := ψscs _ mem' |>.solve (τ := τ) (x := x)
    rw [solve_multiSubst_distrib sorry] at ψcs
    simp at ψcs ⊢
    rw [List.zip_eq_zipWith, List.map_zipWith,
        ← List.zipWith_map_left (f := fun τ' => Monotype.solve τ' τ x),
        ← List.zip_eq_zipWith] at ψcs
    exact ψcs
  | tcSuper tcτcs n =>
    replace tcτcs := tcτcs.solve (τ := τ) (x := x)
    rw [Monotype.solve, Monotype.solve] at tcτcs ⊢
    exact tcSuper tcτcs n
  | allEmpty =>
    simp
    exact allEmpty
  | allSingletonIntro ϕτcs =>
    replace ϕτcs := ϕτcs.solve (τ := τ) (x := x)
    simp at ϕτcs ⊢
    exact allSingletonIntro ϕτcs
  | allSingletonElim allcs =>
    replace allcs := allcs.solve (τ := τ) (x := x)
    simp at allcs ⊢
    exact allSingletonElim allcs
  | allContain containcs allcs =>
    replace containcs := containcs.solve (τ := τ) (x := x)
    replace allcs := allcs.solve (τ := τ) (x := x)
    simp at containcs allcs ⊢
    exact allContain containcs allcs
  | allConcat concatcs all₀cs all₁cs =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    replace all₀cs := all₀cs.solve (τ := τ) (x := x)
    replace all₁cs := all₁cs.solve (τ := τ) (x := x)
    simp at concatcs all₀cs all₁cs ⊢
    exact allConcat concatcs all₀cs all₁cs
  | ind =>
    rw [Monotype.solve]
    exact ind
  | splitEmpty =>
    simp
    exact splitEmpty
  | splitSingletonMatch =>
    simp
    exact splitSingletonMatch
  | splitSingletonRest =>
    simp
    exact splitSingletonRest
  | splitPiecewise split₂cs split₅cs concat₆cs concat₇cs concat₈cs concatcs =>
    replace split₂cs := split₂cs.solve (τ := τ) (x := x)
    replace split₅cs := split₅cs.solve (τ := τ) (x := x)
    replace concat₆cs := concat₆cs.solve (τ := τ) (x := x)
    replace concat₇cs := concat₇cs.solve (τ := τ) (x := x)
    replace concat₈cs := concat₈cs.solve (τ := τ) (x := x)
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at split₂cs split₅cs concat₆cs concat₇cs concat₈cs concatcs ⊢
    exact splitPiecewise split₂cs split₅cs concat₆cs concat₇cs concat₈cs concatcs
  | splitConcat concatcs =>
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at concatcs ⊢
    exact splitConcat concatcs

end ConstraintSolution

end Monotype

open Monotype

namespace QualifiedType

def subst (γ : QualifiedType) (τ : Monotype) (i : TId) : QualifiedType := match γ with
  | .mono τ' => τ'.subst τ i
  | .qual ψ γ' => subst γ' τ i |>.qual <| ψ.subst τ i

@[simp]
def solve (γ : QualifiedType) (τ : Monotype) (x : UId) : QualifiedType := match γ with
  | .mono τ' => τ'.solve τ x
  | .qual ψ γ' => solve γ' τ x |>.qual <| ψ.solve τ x

theorem solve_subst_distrib (nmem : i ∉ τ')
  : solve (subst γ τ i) τ' x = subst (solve γ τ' x) (τ.solve τ' x) i := by
  induction γ
  all_goals aesop (add simp [subst, solve], apply safe Monotype.solve_subst_distrib)

end QualifiedType

open QualifiedType

namespace TypeScheme

def subst (σ : TypeScheme) (τ : Monotype) (i : TId) : TypeScheme := match σ with
  | .qual γ => γ.subst τ i
  | .quant i' κ σ' =>
    .quant i' κ <| if i == i' then σ' else subst σ' τ i

@[simp]
def solve (σ : TypeScheme) (τ : Monotype) (x : UId) : TypeScheme := match σ with
  | .qual γ => γ.solve τ x
  | .quant i κ σ' => .quant i κ <| solve σ' τ x

theorem solve_subst_distrib (nmem : i ∉ τ')
  : solve (subst σ τ i) τ' x = subst (solve σ τ' x) (τ.solve τ' x) i := by
  induction σ
  all_goals aesop (add simp [subst, solve], apply safe QualifiedType.solve_subst_distrib)

inductive Subtyping : TypeScheme → TypeScheme → Type where
  | refl : Subtyping σ σ
  | trans : Subtyping σ₀ σ₁ → Subtyping σ₁ σ₂ → Subtyping σ₀ σ₂
  | arr {τ₀ τ₁ τ₂ τ₃ : Monotype} : Subtyping τ₂ τ₀ → Subtyping τ₁ τ₃ →
    Subtyping (arr τ₀ τ₁) (arr τ₂ τ₃)
  | qual {ψ₀ ψ₁ : Monotype} {γ₀ γ₁ : QualifiedType} : Subtyping ψ₁ ψ₀ → Subtyping γ₀ γ₁ →
    Subtyping (γ₀.qual ψ₀) (γ₁.qual ψ₁)
  | schemeL : Subtyping (subst σ₀ τ i) σ₁ → Subtyping (quant i κ σ₀) σ₁
  | schemeR : Subtyping σ₀ σ₁ → Subtyping σ₀ (quant i κ σ₁)
  | prodOrSum {τ₀s τ₁s : List Monotype} :
    (∀ τ₀₁ ∈ List.zip τ₀s τ₁s, let (τ₀, τ₁) := τ₀₁; Subtyping τ₀ τ₁) →
    Subtyping ((prodOrSum Ξ μ).app (row (List.zip ξs τ₀s) κ?))
      ((prodOrSum Ξ μ).app (row (List.zip ξs τ₁s) κ?))
  | prodOrSumRow : RowEquivalence ρ₀ μ ρ₁ →
    Subtyping ((prodOrSum Ξ μ).app ρ₀) ((prodOrSum Ξ μ).app ρ₁)
  | decay : CommutativityPartialOrdering μ₀ μ₁ →
    Subtyping ((prodOrSum Ξ μ₀).app ρ) ((prodOrSum Ξ μ₁).app ρ)
  | never : Subtyping ((prodOrSum .sum (comm .comm)).app (.row .nil (some star))) σ
  | contain : RowEquivalence ρ₀ μ ρ₂ → RowEquivalence ρ₁ μ ρ₃ →
    Subtyping (contain ρ₀ μ ρ₁) (contain ρ₂ μ ρ₃)
  | concat : RowEquivalence ρ₀ μ ρ₃ → RowEquivalence ρ₁ μ ρ₄ → RowEquivalence ρ₂ μ ρ₅ →
    Subtyping (concat ρ₀ μ ρ₁ ρ₂) (concat ρ₃ μ ρ₄ ρ₅)
  | all : RowEquivalence ρ₀ (comm .comm) ρ₁ → Subtyping ((all ϕ).app ρ₀) ((all ϕ).app ρ₁)
  | split : Subtyping (concat ((lift ϕ).app ρ₀) (comm .comm) ρ₁ ρ₂)
      (concat ((lift ϕ).app ρ₃) (comm .comm) ρ₄ ρ₅) →
    Subtyping (split ϕ ρ₀ ρ₁ ρ₂) (split ϕ ρ₃ ρ₄ ρ₅)
  | list {τ₀ τ₁ : Monotype} : Subtyping τ₀ τ₁ →
    Subtyping (list.app τ₀) (list.app τ₁)

namespace Subtyping

def «elab» : Subtyping σ₀ σ₁ → ElabM «λπι».Term
  | refl | decay _ => return .id
  | trans σ₀₁'st σ₁'₂st => do
    let i ← freshId
    return .lam i <| (← σ₁'₂st.elab).app <| (← σ₀₁'st.elab).app <| .var i
  | arr st st'
  | qual st st' => do
    let i ← freshId
    let i' ← freshId
    return .lam i <| .lam i' <| (← st'.elab).app <| .app (.var i) <| (← st.elab).app <| .var i'
  | schemeL st' | schemeR st' => st'.elab
  | prodOrSum τ₀₁sst (Ξ := Ξ) (τ₀s := τ₀s) (τ₁s := τ₁s) => do
    let i ← freshId
    match Ξ with
    | .prod => return .lam i <| .prodIntro <| ← τ₀s.zip τ₁s |>.mapMemIdxM fun j _ mem =>
        return (← τ₀₁sst _ mem |>.elab).app <| .prodElim j <| .var i
    | .sum => return .lam i <| .sumElim (.var i) <| ← τ₀s.zip τ₁s |>.mapMemIdxM fun j _ mem => do
        let i' ← freshId
        return .lam i' <| .sumIntro j <| (← τ₀₁sst _ mem |>.elab).app <| .var i'
  | prodOrSumRow ρ₀₁re (Ξ := Ξ) => match Ξ with | .prod => ρ₀₁re.prodElab | .sum => ρ₀₁re.sumElab
  | never => do
    let i ← freshId
    return .lam i <| .sumElim (.var i) []
  | contain ρ₀₂re ρ₁₃re => do
    let i ← freshId
    return .lam i <| ← contain.elab ρ₀₂re ρ₁₃re i
  | concat ρ₀₃re ρ₁₄re ρ₂₅re => do
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    let i₆ ← freshId
    let i₇ ← freshId
    return .lam i₀ <| .prodIntro [
      .lam i₁ <| .lam i₂ <| (← ρ₂₅re.prodElab).app <| «λπι».Term.app (.var i₀)
        ((← ρ₀₃re.symm.prodElab).app (.var i₁)) |>.app ((← ρ₁₄re.symm.prodElab).app (.var i₂)),
      .lam i₃ <| .lam i₄ <| .lam i₅ <| («λπι».Term.var i₀) |>.app
        (.lam i₆ (.app (.var i₃) ((← ρ₀₃re.sumElab).app (.var i₆))))
        |>.app (.lam i₇ (.app (.var i₄) ((← ρ₁₄re.sumElab).app (.var i₇)))) |>.app <|
        (← ρ₂₅re.symm.sumElab).app (.var i₅),
      ← contain.elab ρ₀₃re ρ₂₅re i₀,
      ← contain.elab ρ₁₄re ρ₂₅re i₀
    ]
  | all ρ₀₁re => ρ₀₁re.prodElab
  | split concatst => concatst.elab
  | list τ₀₁st => do
    let E ← τ₀₁st.elab
    let i ← freshId
    let iₐ ← freshId
    let iₓ ← freshId
    return .lam i <|
      .app (.app (.app .fold (.lam iₐ (.lam iₓ (.cons (.var iₓ) (.var iₐ))))) .nil) <|
      .app (.app (.app .fold (.lam iₐ (.lam iₓ (.cons (E.app (.var iₓ)) (.var iₐ))))) .nil) <| .var i
where
  contain.elab {μ ρ₀ ρ₁ ρ₂ ρ₃} (ρ₀₂re : RowEquivalence ρ₀ μ ρ₂) (ρ₁₃re : RowEquivalence ρ₁ μ ρ₃)
    (i : «λπι».Id) : ElabM «λπι».Term := do
      let i' ← freshId
      let i'' ← freshId
      return «λπι».Term.prodIntro [
        .lam i' <| (← ρ₀₂re.prodElab).app <| .app (.var i) <|
          (← ρ₁₃re.symm.prodElab).app <| .var i',
        .lam i'' <| (← ρ₁₃re.sumElab).app <| .app (.var i) <| (← ρ₀₂re.symm.sumElab).app <| .var i''
      ]

def solve (st : Subtyping σ₀ σ₁) : Subtyping (σ₀.solve τ x) (σ₁.solve τ x) := by
  cases st with
  | refl => exact refl
  | trans σ₀₁'st σ₁'₂st => exact trans σ₀₁'st.solve σ₁'₂st.solve
  | arr st st' =>
    replace st := st.solve (τ := τ) (x := x)
    replace st' := st'.solve (τ := τ) (x := x)
    simp at st st' ⊢
    exact arr st st'
  | qual st st' =>
    replace st := st.solve (τ := τ) (x := x)
    replace st' := st'.solve (τ := τ) (x := x)
    simp at st st' ⊢
    exact qual st st'
  | schemeL st' =>
    rename Monotype => τ'
    simp
    replace st' := st'.solve (τ := τ) (x := x)
    apply schemeL (τ := τ'.solve τ x)
    rw [← solve_subst_distrib sorry]
    exact st'
  | schemeR st' =>
    simp
    exact schemeR <| st'.solve
  | prodOrSum τ₀₁sst =>
    simp
    rw [List.map_eq_map_iff (f := fun a => (Monotype.solve a.fst τ x, Monotype.solve a.snd τ x))
          (g := Prod.map (Monotype.solve · τ x) (Monotype.solve · τ x)).mpr (by simp),
        List.map_eq_map_iff (f := fun a => (Monotype.solve a.fst τ x, Monotype.solve a.snd τ x))
          (g := Prod.map (Monotype.solve · τ x) (Monotype.solve · τ x)).mpr (by simp),
        ← List.zip_map, ← List.zip_map]
    apply prodOrSum
    rintro ⟨_, _⟩ mem
    rw [List.zip_map] at mem
    rcases List.mem_of_mem_map mem with ⟨⟨_, _⟩, mem', eq⟩
    rw [Prod.map] at eq
    rcases eq with ⟨rfl, rfl⟩
    exact τ₀₁sst _ mem' |>.solve
  | prodOrSumRow ρ₀₁re =>
    simp
    apply prodOrSumRow ρ₀₁re.solve
  | decay po =>
    simp
    exact decay <| po.solve
  | never =>
    simp
    exact never
  | contain ρ₀₂re ρ₁₃re =>
    simp
    exact contain ρ₀₂re.solve ρ₁₃re.solve
  | concat ρ₀₃re ρ₁₄re ρ₂₅re =>
    simp
    exact concat ρ₀₃re.solve ρ₁₄re.solve ρ₂₅re.solve
  | all ρ₀₁re =>
    replace ρ₀₁re := ρ₀₁re.solve (τ := τ) (x := x)
    simp at ρ₀₁re ⊢
    exact all ρ₀₁re
  | split concatst =>
    replace concatst := concatst.solve (τ := τ) (x := x)
    simp at concatst ⊢
    exact split concatst
  | list τ₀₁st =>
    simp
    exact list τ₀₁st.solve
termination_by sizeOf st
decreasing_by
  all_goals simp_arith
  all_goals sorry

end Subtyping

end TypeScheme

open TypeScheme

def «λπι».Op.result : «λπι».Op → Monotype
  | .add | .sub | .mul | .div => .int
  | .eq | .lt | .le | .gt | .ge => .bool

@[simp]
theorem Monotype.solve_Op_result : solve («λπι».Op.result o) τ x = «λπι».Op.result o := by
  cases o <;> simp [«λπι».Op.result, bool, unit]

namespace Term

-- TODO: Check for shadowing?
@[simp]
def subst (M : Term) (τ : Monotype) (i : TId) : Term := match M with
  | var i' => var i'
  | member s => member s
  | lam i' M' => lam i' <| subst M' τ i
  | app M' N => app (subst M' τ i) (subst N τ i)
  | «let» i' σ? M' N => «let» i' (σ?.map (·.subst τ i)) (subst M' τ i) (subst N τ i)
  | annot M' σ => annot (subst M' τ i) (σ.subst τ i)
  | label s => label s
  | prod M'Ns => prod <| M'Ns.mapMem fun (M', N) _ => (subst M' τ i, subst N τ i)
  | sum M' N => sum (subst M' τ i) (subst N τ i)
  | unlabel M' N => unlabel (subst M' τ i) (subst N τ i)
  | prj M' => prj <| subst M' τ i
  | concat M' N => concat (subst M' τ i) (subst N τ i)
  | inj M' => inj <| subst M' τ i
  | elim M' N => elim (subst M' τ i) (subst N τ i)
  | ind ϕ ρ l t rn ri rp M' N =>
    ind (ϕ.subst τ i) (ρ.subst τ i) l t rn ri rp (subst M' τ i) (subst N τ i)
  | splitₚ ϕ M' => splitₚ (ϕ.subst τ i) (subst M' τ i)
  | splitₛ ϕ M' N => splitₛ (ϕ.subst τ i) (subst M' τ i) (subst N τ i)
  | nil => nil
  | cons M' N => cons (subst M' τ i) (subst N τ i)
  | fold i iₐ => fold i iₐ
  | int i => int i
  | op o M' N => op o (subst M' τ i) (subst N τ i)
  | range => range
  | str s => str s
  | throw => throw
  | «def» s => «def» s

@[simp]
def solve (M : Term) (τ : Monotype) (x : UId) : Term := match M with
  | var i => var i
  | member s => member s
  | lam i M' => lam i <| solve M' τ x
  | app M' N => app (solve M' τ x) (solve N τ x)
  | «let» i σ? M' N => «let» i (σ?.map (·.solve τ x)) (solve M' τ x) (solve N τ x)
  | annot M' σ => annot (solve M' τ x) (σ.solve τ x)
  | label s => label s
  | prod M'Ns => prod <| M'Ns.mapMem fun (M', N) _ => (solve M' τ x, solve N τ x)
  | sum M' N => sum (solve M' τ x) (solve N τ x)
  | unlabel M' N => unlabel (solve M' τ x) (solve N τ x)
  | prj M' => prj <| solve M' τ x
  | concat M' N => concat (solve M' τ x) (solve N τ x)
  | inj M' => inj <| solve M' τ x
  | elim M' N => elim (solve M' τ x) (solve N τ x)
  | ind ϕ ρ l t rn ri rp M' N =>
    ind (ϕ.solve τ x) (ρ.solve τ x) l t rn ri rp (solve M' τ x) (solve N τ x)
  | splitₚ ϕ M' => splitₚ (ϕ.solve τ x) (solve M' τ x)
  | splitₛ ϕ M' N => splitₛ (ϕ.solve τ x) (solve M' τ x) (solve N τ x)
  | nil => nil
  | cons M' N => cons (solve M' τ x) (solve N τ x)
  | fold i iₐ => fold i iₐ
  | int i => int i
  | op o M' N => op o (solve M' τ x) (solve N τ x)
  | range => range
  | str s => str s
  | throw => throw
  | «def» s => «def» s

theorem solve_subst_distrib (nmem : i ∉ τ')
  : solve (subst M τ i) τ' x = subst (solve M τ' x) (τ.solve τ' x) i := by
  sorry

-- Existence of this Typing term doesn't actually prove the Term has this type; this is only used to
-- guide elaboration, so it is up to the function producing this to ensure it is constructed
-- correctly, since mistakes will not necessarily be caught by the type checker.
inductive Typing : Term → TypeScheme → Type where
  | var : Typing (.var n) σ
  | lam {τ₁ : Monotype} : Typing M τ₁ → Typing (M.lam i) (arr τ₀ τ₁)
  | app {ϕ : Monotype} : Typing M (ϕ.arr τ) → Typing N ϕ → Typing (M.app N) τ
  | qualI {γ : QualifiedType} : (ConstraintSolution ψ → Typing M γ) → Typing M (γ.qual ψ)
  | qualE {γ : QualifiedType} : ConstraintSolution ψ → (Typing M (γ.qual ψ)) → Typing M γ
  | schemeI : Typing M σ → Typing M (quant i κ σ)
  | schemeE : Typing M (quant i κ σ) → Typing (subst M τ i) (σ.subst τ i)
  | let : Typing M σ₀ → Typing N σ₁ → Typing (M.let i (Option.someIf σ₀ b) N) σ₁
  | annot : Typing M σ → Typing (M.annot σ) σ
  | label : Typing (label s) (floor (.label s))
  | prod : (∀ MNξτ ∈ MNs.zip ξτs, let ((_, N), _, τ) := MNξτ; Typing N τ) →
    Typing (prod MNs) ((prodOrSum .prod (comm .non)).app (row ξτs (some .star)))
  | sum {τ : Monotype} : Typing N τ →
    Typing (sum M N) ((prodOrSum .sum (comm .non)).app (row [(ξ, τ)] none))
  | unlabel : Typing M ((prodOrSum Ξ μ).app (row [(ξ, τ)] κ?)) → Typing (unlabel M N) τ
  | prj : Typing M ((prodOrSum .prod μ).app ρ₀) → ConstraintSolution (contain ρ₁ μ ρ₀) →
    Typing (prj M) ((prodOrSum .prod μ).app ρ₁)
  | concat : Typing M ((prodOrSum .prod μ).app ρ₀) → Typing N ((prodOrSum .prod μ).app ρ₁) →
    ConstraintSolution (.concat ρ₀ μ ρ₁ ρ₂) → Typing (M.concat N) ((prodOrSum .prod μ).app ρ₂)
  | inj : Typing M ((prodOrSum .sum μ).app ρ₀) → ConstraintSolution (contain ρ₀ μ ρ₁) →
    Typing (inj M) ((prodOrSum .sum μ).app ρ₁)
  | elim : Typing M (((prodOrSum .sum μ).app ρ₀).arr τ) →
    Typing N (((prodOrSum .sum μ).app ρ₁).arr τ) → ConstraintSolution (.concat ρ₀ μ ρ₁ ρ₂) →
    Typing (M.elim N) (((prodOrSum .sum μ).app ρ₂).arr τ)
  | sub : Typing M σ₀ → Subtyping σ₀ σ₁ → Typing M σ₁
  | member : ConstraintSolution ((tc s).app τ) → Typing (member m) σ
  | ind : Typing M (quant iₗ .label (quant iₜ κ (quant iₚ κ.row (quant iᵢ κ.row (quant iₙ κ.row
      (qual (.concat (.var iₚ) (comm .non) (row [(.var iₗ, .var iₜ)] none) (.var iᵢ))
        (qual (.concat (.var iᵢ) (comm .non) (.var iₙ) ρ)
          ((floor (.var iₗ)).arr ((ϕ.app (.var iₚ)).arr (ϕ.app (.var iᵢ))))))))))) →
    Typing N (ϕ.app (.row .nil (some κ))) → ConstraintSolution (Monotype.ind ρ) →
    Typing (ind ϕ ρ iₗ iₜ iₚ iᵢ iₙ M N) (ϕ.app ρ)
  | splitₚ : Typing M ((prodOrSum .prod (comm .comm)).app ρ₂) →
    ConstraintSolution (split ϕ ρ₀ ρ₁ ρ₂) →
    Typing (M.splitₚ ϕ) ((prodOrSum .prod (comm .non)).app
      (row [
        (.label "match", (prodOrSum .prod (comm .comm)).app ((lift ϕ).app ρ₀)),
        (.label "rest", (prodOrSum .prod (comm .comm)).app ρ₁)
      ] none))
  | splitₛ : Typing M (((prodOrSum .sum (comm .comm)).app ((lift ϕ).app ρ₀)).arr τ) →
    Typing N (((prodOrSum .sum (comm .comm)).app ρ₁).arr τ) →
    ConstraintSolution (split ϕ ρ₀ ρ₁ ρ₂) →
    Typing (M.splitₛ ϕ N) (((prodOrSum .sum (comm .comm)).app ρ₂).arr τ)
  | nil : Typing nil (list.app τ)
  | cons {τ : Monotype} : Typing M τ → Typing N (list.app τ) → Typing (cons M N) (list.app τ)
  | fold : Typing (fold i iₐ) (quant i .star (quant iₐ .star (qual (mono (arr (arr
      (.var iₐ) (arr (.var i) (.var iₐ))) (arr (.var iₐ) ((list.app (.var i)).arr (.var iₐ))))))))
  | int : Typing (int i) Monotype.int
  | op : Typing M Monotype.int → Typing N Monotype.int →
    Typing (op o M N) o.result
  | range : Typing range (Monotype.int.arr (list.app .int))
  | str : Typing (str s) (Monotype.str)
  | throw : Typing throw (Monotype.str.arr σ)
  | def : Typing («def» s) σ

instance [Inhabited α] : Inhabited (Thunk α) where
  default := .mk fun _ => default

namespace Typing

def «elab» : Typing M σ → ReaderT (HashMap String «λπι».Term) ElabM «λπι».Term
  | var (n := n) => return .var n
  | lam (i := i) M'ty => M'ty.elab <&> .lam i
  | app M'ty Nty => return (← M'ty.elab).app <| ← Nty.elab
  | qualI Mty'_of_cs => do
    let i ← freshId
    «elab» (Mty'_of_cs <| .local i) <&> .lam i
  | qualE ψcs Mty' => return (← Mty'.elab).app <| ← ψcs.elab
  | schemeI Mty' => Mty'.elab
  | schemeE Mty' => Mty'.elab
  | .let (i := i) M'ty Nty => return (← Nty.elab).lam i |>.app <| ← M'ty.elab
  | annot M'ty => M'ty.elab
  | label => return .unit
  | prod Nsty (MNs := MNs) (ξτs := ξτs) =>
    return .prodIntro <| ← MNs.zip ξτs |>.mapMemM (Nsty · · |>.elab)
  | sum Nty => Nty.elab <&> .sumIntro 0
  | unlabel M'ty (Ξ := Ξ) => match Ξ with
    | .prod => M'ty.elab <&> .prodElim 0
    | .sum => return (← M'ty.elab).sumElim [.id]
  | prj M'ty containcs => return (← containcs.elab).prodElim 0 |>.app <| ← M'ty.elab
  | concat M'ty Nty concatcs =>
    return (← concatcs.elab).prodElim 0 |>.app (← M'ty.elab) |>.app <| ← Nty.elab
  | inj M'ty containcs => return (← containcs.elab).prodElim 1 |>.app <| ← M'ty.elab
  | elim M'ty Nty concatcs =>
    return (← concatcs.elab).prodElim 1 |>.app (← M'ty.elab) |>.app <| ← Nty.elab
  | sub Mty' .refl => Mty'.elab
  | sub Mty' σ₀st => return (← σ₀st.elab).app <| ← Mty'.elab
  | member TCτcs => return (← TCτcs.elab).prodElim 0
  | ind M'ty Nty indcs => return (← indcs.elab).app (← M'ty.elab) |>.app <| ← Nty.elab
  | splitₚ M'ty splitcs => do
    let E ← M'ty.elab
    let F ← splitcs.elab
    return .prodIntro [F.prodElim 2 |>.prodElim 0 |>.app E, F.prodElim 3 |>.prodElim 0 |>.app E]
  | splitₛ M'ty Nty splitcs =>
    return (← splitcs.elab).prodElim 1 |>.app (← M'ty.elab) |>.app <| ← Nty.elab
  | nil => return .nil
  | cons M'ty Nty => return .cons (← M'ty.elab) (← Nty.elab)
  | fold .. => return .fold
  | int (i := i) => return .int i
  | op M'ty Nty (o := o) => return .op o (← M'ty.elab) (← Nty.elab)
  | range => return .range
  | str (s := s) => return .str s
  | throw => return .throw
  | «def» (s := s) => return (← read)[s]!

def solve (ty : Typing M σ) : Typing (M.solve τ x) (σ.solve τ x) := by
  cases ty
  · case var =>
    simp
    exact var
  · case lam M'ty =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    simp at M'ty ⊢
    exact lam M'ty
  · case app M'ty Nty =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    simp at M'ty Nty ⊢
    exact app M'ty Nty
  · case qualI Mty'_of_cs => sorry
  · case qualE ψce Mty' =>
    replace Mty' := solve Mty' (τ := τ) (x := x)
    simp at Mty'
    exact qualE ψce.solve Mty'
  · case schemeI M'ty =>
    simp
    exact schemeI M'ty.solve
  · case schemeE M'ty =>
    rw [Term.solve_subst_distrib sorry, TypeScheme.solve_subst_distrib sorry]
    exact schemeE M'ty.solve
  · case «let» M'ty Nty =>
    simp [Option.map_someIf]
    exact «let» M'ty.solve Nty.solve
  · case annot M'ty =>
    simp
    exact annot M'ty.solve
  · case label =>
    simp
    exact label
  · case prod Nsty =>
    replace Nsty MNξτ mem := solve (Nsty MNξτ mem) (τ := τ) (x := x)
    simp at Nsty ⊢
    apply prod
    rintro ⟨⟨_, _⟩, _, _⟩ mem
    simp
    rw [List.zip_map] at mem
    rcases List.mem_of_mem_map mem with ⟨_, mem', eq⟩
    simp [Prod.map] at eq
    rcases eq with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
    exact Nsty _ mem'
  · case sum Nty =>
    simp
    exact sum Nty.solve
  · case unlabel M'ty =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    simp at M'ty ⊢
    exact unlabel M'ty
  · case prj M'ty containcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace containcs := containcs.solve (τ := τ) (x := x)
    simp at M'ty containcs ⊢
    exact prj M'ty containcs
  · case concat M'ty Nty concatcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at M'ty Nty concatcs ⊢
    exact concat M'ty Nty concatcs
  · case inj M'ty containcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace containcs := containcs.solve (τ := τ) (x := x)
    simp at M'ty containcs ⊢
    exact inj M'ty containcs
  · case elim M'ty Nty concatcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    replace concatcs := concatcs.solve (τ := τ) (x := x)
    simp at M'ty Nty concatcs ⊢
    exact elim M'ty Nty concatcs
  · case sub Mty' σ₀st =>
    replace Mty' := solve Mty' (τ := τ) (x := x)
    replace σ₀st := σ₀st.solve (τ := τ) (x := x)
    simp at Mty' σ₀st ⊢
    exact sub Mty' σ₀st
  · case member TCτcs =>
    replace TCτcs := TCτcs.solve (τ := τ) (x := x)
    simp at TCτcs ⊢
    exact member TCτcs
  · case ind M'ty Nty indcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    replace indcs := indcs.solve (τ := τ) (x := x)
    simp at M'ty Nty indcs ⊢
    exact ind M'ty Nty indcs
  · case splitₚ M'ty splitcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace splitcs := splitcs.solve (τ := τ) (x := x)
    simp at M'ty splitcs ⊢
    exact splitₚ M'ty splitcs
  · case splitₛ M'ty Nty splitcs =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    replace splitcs := splitcs.solve (τ := τ) (x := x)
    simp at M'ty Nty splitcs ⊢
    exact splitₛ M'ty Nty splitcs
  · case nil =>
    simp
    exact nil
  · case cons M'ty Nty =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    simp at M'ty Nty ⊢
    exact cons M'ty Nty
  · case fold =>
    simp
    exact fold
  · case int =>
    simp
    exact int
  · case op M'ty Nty =>
    replace M'ty := solve M'ty (τ := τ) (x := x)
    replace Nty := solve Nty (τ := τ) (x := x)
    simp at M'ty Nty ⊢
    exact op M'ty Nty
  · case range =>
    simp
    exact range
  · case str =>
    simp
    exact str
  · case throw =>
    simp
    exact throw
  · case «def» =>
    simp
    exact «def»
termination_by sizeOf ty
decreasing_by
  all_goals simp_arith
  all_goals sorry

end Typing

end Term

namespace «λπι»

def Value.delab (V : Value) (σ : Interpreter.TypeScheme) : Option Interpreter.Term := do
  let .qual (.mono τ) := σ | none
  let ⟨E, EIs⟩ := V
  match E with
  | .lam i E' =>
    if E'Is : Is E' then
      let .arr _ τ₁ := τ | none
      let M ← delab ⟨E', E'Is⟩ τ₁
      return M.lam i
    none
  | .app E' F => match E' with
    | .fold =>
      let .arr τₐ (.arr (.app .list τₑ) _) := τ | none
      let FIs := match EIs with | .fold₁ h => h
      let M ← delab ⟨F, FIs⟩ <| τₐ.arr <| τₑ.arr τₐ
      some <| .app (.fold { val := 0 } { val := 0 }) M
    | .app .fold _ => none -- Can't determine accumulator type.
  | .prodIntro Es =>
    let .app (.prodOrSum .prod _) (.row ξτ's _) := τ | none
    let EsIs := match EIs with | .prodIntro h => h
    let true := Es.length == ξτ's.length | none
    let V's : List { V' : Value // V'.val ∈ Es } := Es.mapMem fun E mem => ⟨⟨E, EsIs _ mem⟩, mem⟩
    let MNs ← V's.zip ξτ's |>.mapM fun
      | (⟨V', _⟩, .label s, τ') => do
        let N ← V'.delab τ'
        return (TabularTypeInterpreter.Interpreter.Term.label s, N)
      | _ => none
    return .prod MNs
  | .sumIntro n E' => do
    let .app (.prodOrSum .sum _) (.row ξτ's _) := τ | none
    let E'Is := match EIs with | .sumIntro h => h
    let (.label s, τ') ← ξτ's.get? n | none
    let N ← delab ⟨E', E'Is⟩ τ'
    return .sum (.label s) N
  | .nil => some .nil
  | .cons E' F => do
    let .app .list τ' := τ | none
    let ⟨E'Is, FIs⟩ : _ ∧ _ := match EIs with
      | .cons EIs FIs => ⟨EIs, FIs⟩
    let M ← delab ⟨E', E'Is⟩ τ'
    let N ← delab ⟨F, FIs⟩ <| .qual <| .mono <| .app .list τ'
    return M.cons N
  | .fold => some <| .fold { val := 0 } { val := 0 }
  | .int i => some <| .int i
  | .range => some .range
  | .str s => some <| .str s
  | .throw => some .throw
termination_by sizeOf V.val

end «λπι»

end Interpreter

end TabularTypeInterpreter
