import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

termonly
mutual

@[simp]
noncomputable
def TypeLambda.sizeOf' : TypeLambda → Nat | .mk κ τ => 1 + sizeOf κ + τ.sizeOf'

@[simp]
noncomputable
def Monotype.sizeOf' : Monotype → Nat
  | .var a => 1 + sizeOf a
  | .app ϕ τ => 1 + ϕ.sizeOf' + τ.sizeOf'
  | .arr τ₀ τ₁ => 1 + τ₀.sizeOf' + τ₁.sizeOf'
  | .label ℓ => 1 + sizeOf ℓ
  | .floor ξ => 1 + ξ.sizeOf'
  | .comm u => 1 + sizeOf u
  | .row ξτs κ? => 1 + (List.sum <| ξτs.mapMem fun (ξ, τ) _ => ξ.sizeOf' + τ.sizeOf') + sizeOf κ?
  | .prodOrSum _ μ ρ => 1 + μ.sizeOf' + ρ.sizeOf'
  | .lift «λτ» ρ => 1 + «λτ».sizeOf' + ρ.sizeOf'
  | .contain ρ₀ μ ρ₁ => 1 + ρ₀.sizeOf' + μ.sizeOf' + ρ₁.sizeOf'
  | .concat ρ₀ μ ρ₁ ρ₂ => 1 + ρ₀.sizeOf' + μ.sizeOf' + ρ₁.sizeOf' + ρ₂.sizeOf'
  | .typeClass _ τ => 1 + τ.sizeOf'
  | .all «λτ» ρ => 1 + «λτ».sizeOf' + ρ.sizeOf'
  | .ind ρ => 15 + ρ.sizeOf'
  | .split «λτ» ρ₀ ρ₁ ρ₂ => 5 + «λτ».sizeOf' + ρ₀.sizeOf' + ρ₁.sizeOf' + ρ₂.sizeOf'

end

termonly
@[simp]
noncomputable
def QualifiedType.sizeOf' : QualifiedType → Nat
  | mono τ => 1 + τ.sizeOf'
  | qual ψ γ => 1 + ψ.sizeOf' + γ.sizeOf'

termonly
@[simp]
noncomputable
def TypeScheme.sizeOf' : TypeScheme → Nat
  | qual γ => 1 + γ.sizeOf'
  | quant _ σ => 2 + σ.sizeOf'

termonly
def Monotype.TypeVar_multi_open (τ : Monotype) (a : Nat → TypeVarId) : Nat → Monotype
  | 0 => τ
  | n + 1 => τ.TypeVar_open (a n) n |>.TypeVar_multi_open a n

termonly
def Monotype.Monotype_multi_open (τ₀ : Monotype) (τ₁ : Nat → Monotype) : Nat → Monotype
  | 0 => τ₀
  | n + 1 => τ₀.Monotype_open (τ₁ n) n |>.Monotype_multi_open τ₁ n

end TabularTypeInterpreter
