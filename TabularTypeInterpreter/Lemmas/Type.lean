import TabularTypeInterpreter.Semantics.Type

namespace TabularTypeInterpreter

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

@[simp]
theorem Monotype.sizeOf_pos (τ : Monotype) : 0 < sizeOf τ := by cases τ <;> simp_arith

@[simp]
theorem Monotype.sizeOf'_pos (τ : Monotype) : 0 < τ.sizeOf' := by cases τ <;> simp_arith [sizeOf']

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

end TypeScheme

end TabularTypeInterpreter
