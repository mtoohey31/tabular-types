import Aesop
import TabularTypeInterpreter.Semantics.Type

namespace TabularTypeInterpreter

open «F⊗⊕ω»

mutual

@[simp]
theorem TypeLambda.TypeVar_open_sizeOf («λτ» : TypeLambda)
  : sizeOf («λτ».TypeVar_open a n) = sizeOf «λτ» := open TypeLambda in by
  let .mk κ τ := «λτ»
  rw [TypeVar_open, mk.sizeOf_spec, mk.sizeOf_spec, τ.TypeVar_open_sizeOf]

@[simp]
theorem Monotype.TypeVar_open_sizeOf (τ : Monotype) : sizeOf (τ.TypeVar_open a n) = sizeOf τ :=
  open Monotype in by
  match τ with
  | .var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [var.sizeOf_spec, var.sizeOf_spec, ← h]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | .var (.free _) =>
    rw [TypeVar_open]
    split <;> rfl
  | .app φ τ =>
    rw [TypeVar_open, app.sizeOf_spec, app.sizeOf_spec, φ.TypeVar_open_sizeOf,
        τ.TypeVar_open_sizeOf]
  | .arr τ₀ τ₁ =>
    rw [TypeVar_open, arr.sizeOf_spec, arr.sizeOf_spec, τ₀.TypeVar_open_sizeOf,
        τ₁.TypeVar_open_sizeOf]
  | .label _ => rw [TypeVar_open]
  | .floor ξ => rw [TypeVar_open, floor.sizeOf_spec, floor.sizeOf_spec, ξ.TypeVar_open_sizeOf]
  | .comm _ => rw [TypeVar_open]
  | .row ξτs κ? =>
    rw [TypeVar_open, List.mapMem_eq_map]
    match ξτs with
    | [] => rw [List.map]
    | (ξ, τ) :: ξτs' =>
      rw [List.map, row.sizeOf_spec, row.sizeOf_spec, List.cons.sizeOf_spec, List.cons.sizeOf_spec,
          Prod.mk.sizeOf_spec, Prod.mk.sizeOf_spec, ξ.TypeVar_open_sizeOf, τ.TypeVar_open_sizeOf]
      have : sizeOf ((row ξτs' κ?).TypeVar_open a n) = sizeOf (row ξτs' κ?) :=
        (row ξτs' κ?).TypeVar_open_sizeOf
      simp_arith [TypeVar_open] at this
      simp_arith [this]
  | .prod μ ρ =>
    rw [TypeVar_open, prod.sizeOf_spec, prod.sizeOf_spec, μ.TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .sum μ ρ =>
    rw [TypeVar_open, sum.sizeOf_spec, sum.sizeOf_spec, μ.TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .lift «λτ» ρ =>
    rw [TypeVar_open, lift.sizeOf_spec, lift.sizeOf_spec, «λτ».TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .contain ρ₀ μ ρ₁ =>
    rw [TypeVar_open, contain.sizeOf_spec, contain.sizeOf_spec, ρ₀.TypeVar_open_sizeOf,
        μ.TypeVar_open_sizeOf, ρ₁.TypeVar_open_sizeOf]
  | .concat ρ₀ μ ρ₁ ρ₂ =>
    rw [TypeVar_open, concat.sizeOf_spec, concat.sizeOf_spec, ρ₀.TypeVar_open_sizeOf,
        μ.TypeVar_open_sizeOf, ρ₁.TypeVar_open_sizeOf, ρ₂.TypeVar_open_sizeOf]
  | .typeClass _ τ =>
    rw [TypeVar_open, typeClass.sizeOf_spec, typeClass.sizeOf_spec, τ.TypeVar_open_sizeOf]
  | .all «λτ» ρ =>
    rw [TypeVar_open, all.sizeOf_spec, all.sizeOf_spec, «λτ».TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .ind ρ => rw [TypeVar_open, ind.sizeOf_spec, ind.sizeOf_spec, ρ.TypeVar_open_sizeOf]
  | .split «λτ» ρ₀ ρ₁ ρ₂ =>
    rw [TypeVar_open, split.sizeOf_spec, split.sizeOf_spec, «λτ».TypeVar_open_sizeOf,
        ρ₀.TypeVar_open_sizeOf, ρ₁.TypeVar_open_sizeOf, ρ₂.TypeVar_open_sizeOf]

end

mutual

@[simp]
theorem TypeLambda.TypeVar_open_sizeOf' («λτ» : TypeLambda)
  : («λτ».TypeVar_open a n).sizeOf' = «λτ».sizeOf' := open TypeLambda in by
  let .mk κ τ := «λτ»
  rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']

@[simp]
theorem Monotype.TypeVar_open_sizeOf' (τ : Monotype) : (τ.TypeVar_open a n).sizeOf' = τ.sizeOf' :=
  open Monotype in by
  match τ with
  | .var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [sizeOf', sizeOf', ← h]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | .var (.free _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [sizeOf', sizeOf']
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse h => rfl
  | .app φ τ =>
    rw [TypeVar_open, sizeOf', sizeOf', φ.TypeVar_open_sizeOf', τ.TypeVar_open_sizeOf']
  | .arr τ₀ τ₁ =>
    rw [TypeVar_open, sizeOf', sizeOf', τ₀.TypeVar_open_sizeOf', τ₁.TypeVar_open_sizeOf']
  | .label _ => rw [TypeVar_open]
  | .floor ξ => rw [TypeVar_open, sizeOf', sizeOf', ξ.TypeVar_open_sizeOf']
  | .comm _ => rw [TypeVar_open]
  | .row ξτs κ? =>
    rw [TypeVar_open, List.mapMem_eq_map]
    match ξτs with
    | [] => rw [List.map]
    | (ξ, τ) :: ξτs' =>
      rw [List.map, sizeOf', sizeOf', List.mapMem_eq_map, List.map_cons, List.sum_cons,
          ξ.TypeVar_open_sizeOf', τ.TypeVar_open_sizeOf']
      have : ((row ξτs' κ?).TypeVar_open a n).sizeOf' = (row ξτs' κ?).sizeOf' :=
        (row ξτs' κ?).TypeVar_open_sizeOf'
      simp_arith [TypeVar_open] at this
      simp_arith [this]
  | .prod μ ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', μ.TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .sum μ ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', μ.TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .lift «λτ» ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', «λτ».TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .contain ρ₀ μ ρ₁ =>
    rw [TypeVar_open, sizeOf', sizeOf', ρ₀.TypeVar_open_sizeOf', μ.TypeVar_open_sizeOf',
        ρ₁.TypeVar_open_sizeOf']
  | .concat ρ₀ μ ρ₁ ρ₂ =>
    rw [TypeVar_open, sizeOf', sizeOf', ρ₀.TypeVar_open_sizeOf', μ.TypeVar_open_sizeOf',
        ρ₁.TypeVar_open_sizeOf', ρ₂.TypeVar_open_sizeOf']
  | .typeClass _ τ =>
    rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']
  | .all «λτ» ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', «λτ».TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .ind ρ => rw [TypeVar_open, sizeOf', sizeOf', ρ.TypeVar_open_sizeOf']
  | .split «λτ» ρ₀ ρ₁ ρ₂ =>
    rw [TypeVar_open, sizeOf', sizeOf', «λτ».TypeVar_open_sizeOf', ρ₀.TypeVar_open_sizeOf',
        ρ₁.TypeVar_open_sizeOf', ρ₂.TypeVar_open_sizeOf']

end

namespace Monotype

@[elab_as_elim]
def rec_uniform {motive : Monotype → Prop} (var : ∀ a, motive (.var a))
  (app : ∀ φ τ, motive φ → motive τ → motive (.app φ τ))
  (arr : ∀ τ₀ τ₁, motive τ₀ → motive τ₁ → motive (.arr τ₀ τ₁)) (label : ∀ ℓ, motive (.label ℓ))
  (floor : ∀ ξ, motive ξ → motive (.floor ξ)) (comm : ∀ u, motive (.comm u))
  (row : ∀ ξτs κ?, (∀ ξτ ∈ ξτs, motive ξτ.fst ∧ motive ξτ.snd) → motive (.row ξτs κ?))
  (prod : ∀ μ ρ, motive μ → motive ρ → motive (.prod μ ρ))
  (sum : ∀ μ ρ, motive μ → motive ρ → motive (.sum μ ρ))
  (lift : ∀ κ τ ρ, motive τ → motive ρ → motive (.lift (.mk κ τ) ρ))
  (contain : ∀ ρ₀ μ ρ₁, motive ρ₀ → motive μ → motive ρ₁ → motive (.contain ρ₀ μ ρ₁))
  (concat : ∀ ρ₀ μ ρ₁ ρ₂, motive ρ₀ → motive μ → motive ρ₁ → motive ρ₂ → motive (.concat ρ₀ μ ρ₁ ρ₂))
  (typeClass : ∀ TC τ, motive τ → motive (.typeClass TC τ))
  (all : ∀ κ ψ ρ, motive ψ → motive ρ → motive (.all (.mk κ ψ) ρ))
  (ind : ∀ ρ, motive ρ → motive (.ind ρ))
  (split : ∀ κ τ ρ₀ ρ₁ ρ₂, motive τ → motive ρ₀ → motive ρ₁ → motive ρ₂ → motive (.split (.mk κ τ) ρ₀ ρ₁ ρ₂))
  (τ : Monotype) : motive τ :=
  Monotype.rec (motive_1 := fun | .mk _ τ => motive τ) (motive_2 := motive)
    (motive_3 := fun τss => ∀ τs ∈ τss, motive τs.fst ∧ motive τs.snd)
    (motive_4 := fun τs => motive τs.fst ∧ motive τs.snd) (fun _ _ mτ => mτ) var app arr label
    floor comm row prod sum (fun | .mk κ τ, ρ, mτ, mρ => lift κ τ ρ mτ mρ) contain concat typeClass
    (fun | .mk κ τ, ρ, mτ, mρ => all κ τ ρ mτ mρ) ind
    (fun | .mk κ τ, ρ₀, ρ₁, ρ₂, mτ, mρ₀, mρ₁, mρ₂ => split κ τ ρ₀ ρ₁ ρ₂ mτ mρ₀ mρ₁ mρ₂)
    (fun _ => (nomatch ·))
    (fun _ _ mhead mtail _ mem => match mem with | .head _ => mhead | .tail _ mem' => mtail _ mem') (fun _ _ mτ₀ mτ₁ => ⟨mτ₀, mτ₁⟩) τ

@[simp]
theorem sizeOf_pos (τ : Monotype) : 0 < sizeOf τ := by cases τ <;> simp_arith

@[simp]
theorem sizeOf'_pos (τ : Monotype) : 0 < τ.sizeOf' := by cases τ <;> simp_arith [sizeOf']

theorem TypeVar_open_comm (τ : Monotype)
  : m ≠ n → (τ.TypeVar_open a m).TypeVar_open a' n = (τ.TypeVar_open a' n).TypeVar_open a m := by
  induction τ using rec_uniform generalizing m n
  all_goals aesop (add simp [TypeVar_open, TypeLambda.TypeVar_open])
  · case left => exact a_1 _ _ a_4 |>.left a_2
  · case right => exact a_1 _ _ a_4 |>.right a_2

namespace TypeVarLocallyClosed

theorem weakening (τlc : TypeVarLocallyClosed τ m) : TypeVarLocallyClosed τ (m + n) := by
  induction τlc using rec
    (motive_1 := fun | .mk κ τ, m, _ => τ.TypeVarLocallyClosed (m + n + 1)) <;> aesop
      (simp_config := { arith := true }) (add safe constructors TypeVarLocallyClosed,
        safe constructors TypeLambda.TypeVarLocallyClosed, 20% [of_eq, Nat.lt_add_right])
where
  of_eq {τ m n} (τlc : TypeVarLocallyClosed τ m) (eq : m = n) : τ.TypeVarLocallyClosed n := by
    rwa [eq] at τlc

theorem TypeVar_open_id : TypeVarLocallyClosed τ n → τ.TypeVar_open a n = τ := by
  induction τ using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, TypeLambda.TypeVar_open], 50% cases TypeVarLocallyClosed,
      safe cases TypeLambda.TypeVarLocallyClosed)

theorem TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed τ n → (τ.TypeVar_close a n).TypeVar_open a n = τ := by
  induction τ using rec_uniform generalizing n <;> aesop
    (add simp [TypeVar_open, TypeVar_close, TypeLambda.TypeVar_open, TypeLambda.TypeVar_close],
      50% cases TypeVarLocallyClosed, safe cases TypeLambda.TypeVarLocallyClosed)

end TypeVarLocallyClosed

theorem TypeVar_open_Monotype_open_comm (τ : Monotype) : TypeVarLocallyClosed τ' m → m ≠ n →
    (τ.TypeVar_open a m).Monotype_open τ' n = (τ.Monotype_open τ' n).TypeVar_open a m := by
  induction τ using rec_uniform generalizing m n <;> aesop
    (add simp [TypeVar_open, Monotype_open, TypeLambda.TypeVar_open, TypeLambda.Monotype_open],
      20% [TypeVarLocallyClosed.TypeVar_open_id, Eq.symm, TypeVarLocallyClosed.weakening])
  · case left => exact a_1 _ _ a_5 |>.left a_2 a_3
  · case right => exact a_1 _ _ a_5 |>.right a_2 a_3

end Monotype

namespace QualifiedType

@[simp]
theorem sizeOf_pos (γ : QualifiedType) : 0 < sizeOf γ := by cases γ <;> simp_arith

@[simp]
theorem TypeVar_open_sizeOf (γ : QualifiedType) : sizeOf (γ.TypeVar_open a n) = sizeOf γ := by
  match γ with
  | .mono τ => rw [TypeVar_open, mono.sizeOf_spec, mono.sizeOf_spec, τ.TypeVar_open_sizeOf]
  | .qual ψ γ =>
    rw [TypeVar_open, qual.sizeOf_spec, qual.sizeOf_spec, ψ.TypeVar_open_sizeOf,
        γ.TypeVar_open_sizeOf]

@[simp]
theorem sizeOf'_pos (γ : QualifiedType) : 0 < γ.sizeOf' := by cases γ <;> simp_arith [sizeOf']

@[simp]
theorem TypeVar_open_sizeOf' (γ : QualifiedType) : (γ.TypeVar_open a n).sizeOf' = γ.sizeOf' := by
  match γ with
  | .mono τ => rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']
  | .qual ψ γ => rw [TypeVar_open, sizeOf', sizeOf', ψ.TypeVar_open_sizeOf', γ.TypeVar_open_sizeOf']

theorem TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed γ n → (γ.TypeVar_close a n).TypeVar_open a n = γ := by
  induction γ <;> aesop
    (add simp [TypeVar_open, TypeVar_close], 50% cases TypeVarLocallyClosed,
      20% Monotype.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id)

theorem TypeVar_open_comm (γ : QualifiedType)
  : m ≠ n → (γ.TypeVar_open a m).TypeVar_open a' n = (γ.TypeVar_open a' n).TypeVar_open a m := by
  induction γ <;> aesop (add simp TypeVar_open, 20% Monotype.TypeVar_open_comm)

theorem TypeVar_open_Monotype_open_comm (γ : QualifiedType) {τ : Monotype}
  : τ.TypeVarLocallyClosed m → m ≠ n →
    (γ.TypeVar_open a m).Monotype_open τ n = (γ.Monotype_open τ n).TypeVar_open a m := by
  induction γ <;> aesop
    (add simp [TypeVar_open, Monotype_open], 20% Monotype.TypeVar_open_Monotype_open_comm)

end QualifiedType

namespace TypeScheme

@[simp]
theorem TypeVar_open_sizeOf (σ : TypeScheme) : sizeOf (σ.TypeVar_open a n) = sizeOf σ := by
  match σ with
  | .qual γ => rw [TypeVar_open, qual.sizeOf_spec, qual.sizeOf_spec, γ.TypeVar_open_sizeOf]
  | .quant _ σ => rw [TypeVar_open, quant.sizeOf_spec, quant.sizeOf_spec, σ.TypeVar_open_sizeOf]

@[simp]
theorem sizeOf'_pos (σ : TypeScheme) : 0 < σ.sizeOf' := by cases σ <;> simp_arith [sizeOf']

@[simp]
theorem TypeVar_open_sizeOf' (σ : TypeScheme) : (σ.TypeVar_open a n).sizeOf' = σ.sizeOf' := by
  match σ with
  | .qual γ => rw [TypeVar_open, sizeOf', sizeOf', γ.TypeVar_open_sizeOf']
  | .quant _ σ => rw [TypeVar_open, sizeOf', sizeOf', σ.TypeVar_open_sizeOf']

theorem TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed σ n → (σ.TypeVar_close a n).TypeVar_open a n = σ  := by
  induction σ generalizing n <;> aesop
    (add simp [TypeVar_open, TypeVar_close], 50% cases TypeVarLocallyClosed,
      20% [QualifiedType.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id])

theorem TypeVar_open_comm (σ : TypeScheme)
  : m ≠ n → (σ.TypeVar_open a m).TypeVar_open a' n = (σ.TypeVar_open a' n).TypeVar_open a m := by
  induction σ generalizing m n <;> aesop
    (add simp TypeVar_open, 20% [QualifiedType.TypeVar_open_comm, Monotype.TypeVar_open_comm])

theorem TypeVar_open_Monotype_open_comm (σ : TypeScheme) {τ : Monotype}
  : τ.TypeVarLocallyClosed m → m ≠ n →
    (σ.TypeVar_open a m).Monotype_open τ n = (σ.Monotype_open τ n).TypeVar_open a m := by
  induction σ generalizing m n <;> aesop
    (add simp [TypeVar_open, Monotype_open],
      20% [QualifiedType.TypeVar_open_Monotype_open_comm, Monotype.TypeVarLocallyClosed.weakening])

namespace KindingAndElaboration

theorem row_inversion
  (rowke : [[Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ' // b />⟩ : κ ⇝ A]])
  : (∃ B, ∀ i ∈ [:n], [[Γc; Γ ⊢ ξ@i : L ⇝ B@i]]) ∧ [[unique(</ ξ@i // i in [:n] />)]] ∧
    (∃ B κ'', A = [[{</ B@i // i in [:n] />}]] ∧ κ = [[R κ'']] ∧ (n ≠ 0 ∨ b) ∧ (b → κ' = κ'') ∧
      ∀ i ∈ [:n], [[Γc; Γ ⊢ τ@i : κ'' ⇝ B@i]]) := by
  generalize ξτseq : ([:n].map fun i => [(ξ i, τ i)]).flatten = ξτs at rowke
  generalize κ''eq : (some κ').filter (fun _ => b) = κ'' at rowke
  let .row ξke uni τke h := rowke
  rename Nat => n'
  rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξτseq
  let length_eq : List.length (List.map ..) = List.length _ := by rw [ξτseq]
  let neqn' : n = n' := by
    repeat rw [List.length_map, Std.Range.length_toList] at length_eq
    exact length_eq
  cases neqn'
  let ξτeqs := Std.Range.eq_of_mem_of_map_eq ξτseq
  rw [List.map_singleton_flatten,
      Std.Range.map_eq_of_eq_of_mem (by rw [← And.left <| Prod.mk.inj <| ξτeqs · ·]),
      ← List.map_singleton_flatten] at uni
  exact ⟨
    ⟨
      _,
      fun i imem => by
        rw [And.left <| Prod.mk.inj <| ξτeqs i imem]
        exact ξke i imem
    ⟩,
    uni,
    ⟨
      _,
      _,
      rfl,
      rfl,
      match h with
      | .inl h => .inl h
      | .inr h => by
        rw [BoolId, id] at h
        rw [h] at κ''eq
        exact .inr <| And.right <| Option.filter_eq_some.mp κ''eq,
      fun beq => by
        rw [beq, Option.filter, if_pos rfl] at κ''eq
        symm at κ''eq ⊢
        exact Option.mem_some.mp <| And.left <| Option.filter_eq_some.mp κ''eq
      ,
      fun i imem => by
        rw [And.right <| Prod.mk.inj <| ξτeqs i imem]
        exact τke i imem
    ⟩
  ⟩

end KindingAndElaboration

end TypeScheme

def Monotype.label.Uniqueness.Perm_preservation {ξ' : Nat → Monotype}
  (uni : [[unique(</ ξ@i // i in [:n] />)]]) (perm : List.Perm p [:n])
  (eq : ∀ i, ξ' i = ξ (p.get! i)) : [[unique(</ ξ'@i // i in [:n] />)]] := by
  generalize ξseq : ([:n].map fun i => [ξ i]).flatten = ξs at uni
  match uni with
  | concrete ne (ℓ := ℓ) =>
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξseq
    let lengths_eq : List.length (List.map ..) = List.length _ := by rw [ξseq]
    rw [List.length_map, List.length_map, Std.Range.length_toList,
        Std.Range.length_toList, Nat.sub_zero, Nat.sub_zero] at lengths_eq
    cases lengths_eq
    let lengths_eq := perm.length_eq
    rw [Std.Range.length_toList] at lengths_eq
    cases lengths_eq
    rw [List.map_singleton_flatten, Std.Range.map_eq_of_eq_of_mem (by
      intro i imem
      show ξ' i = label (ℓ (p.get! i))
      rw [← Std.Range.eq_of_mem_of_map_eq ξseq (p.get! i) <| Std.Range.mem_of_mem_toList <|
            perm.mem_iff.mp <| List.get!_mem imem.right]
      exact eq i
    ), ← List.map_singleton_flatten]
    apply concrete
    intro i imem
    simp only
    let pimem := Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.right
    intro j jmem
    let pjmem := Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem jmem.right
    match Nat.lt_trichotomy (p.get! i) (p.get! j) with
    | .inl piltpj =>
      exact ne _ ⟨Nat.zero_le _, pimem.right⟩ _ ⟨Nat.succ_le_of_lt piltpj, pjmem.right⟩
    | .inr (.inl pieqpj) =>
      let inej : i ≠ j := Nat.ne_of_lt <| Nat.lt_of_succ_le jmem.left
      let count_le_one : [:p.length].toList.count (p.get! i) ≤ 1 := Std.Range.count_toList_le_one
      rw [← perm.count_eq (p.get! i)] at count_le_one
      let two_le_count := List.two_le_count_of_get!_eq_of_ne imem.right jmem.right pieqpj inej
      nomatch Nat.not_lt_of_le count_le_one <| Nat.lt_of_succ_le two_le_count
    | .inr (.inr pjltpi) =>
      apply Ne.symm
      exact ne _ ⟨Nat.zero_le _, pjmem.right⟩ _ ⟨Nat.succ_le_of_lt pjltpi, pimem.right⟩
  | var =>
    let lengths_eq : List.length (List.flatten _) = List.length _ := by rw [ξseq]
    rw [List.map_singleton_flatten, List.length_map, Std.Range.length_toList,
        List.length_singleton, Nat.sub_zero] at lengths_eq
    cases lengths_eq
    rw [List.map_singleton_flatten, Std.Range.toList, if_neg (nomatch ·), if_pos Nat.one_pos,
        Std.Range.toList, if_neg (nomatch ·), Nat.zero_add,
        if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map_singleton]
    exact var

end TabularTypeInterpreter
