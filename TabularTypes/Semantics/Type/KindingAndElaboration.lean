import Lott.Elab.JudgementComprehension
import TabularTypes.«F⊗⊕ω».Semantics.Type
import TabularTypes.Semantics.Kind
import TabularTypes.Semantics.TypeEnvironment.Basic
import TabularTypes.Semantics.ClassEnvironment.Basic

namespace TabularTypes

judgement_syntax ℓ " ≠ " ℓ' : Label.Ne

def Label.Ne := _root_.Ne (α := Label)

judgement_syntax "unique" "(" sepBy(ξ, ", ") ")" : Monotype.label.Uniqueness

judgement Monotype.label.Uniqueness where

</ </ ℓ@i ≠ ℓ@j // j in [i + 1:n] /> // i in [:n] />
──────────────────────────────────────────────────── concrete
unique(</ ℓ@i // i in [:n] />)

───────── singleton
unique(ξ)

open «F⊗⊕ω»

syntax (name := kinding) Lott.Symbol.TabularTypes.ClassEnvironment "; " Lott.Symbol.TabularTypes.TypeEnvironment " ⊢ " Lott.Symbol.TabularTypes.TypeScheme " : " Lott.Symbol.TabularTypes.Kind : Lott.Judgement

judgement_syntax Γc "; " Γ " ⊢ " σ " : " κ " ⇝ " A : TypeScheme.KindingAndElaboration (tex := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {σ} \\, \\kindingsym \\, {κ} \\, \\lottsym\{⇝} \\, {A}") (tex noelab := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {σ} \\, \\kindingsym \\, {κ}")

macro_rules
  | `([[$Γc:Lott.Symbol.TabularTypes.ClassEnvironment; $Γ:Lott.Symbol.TabularTypes.TypeEnvironment ⊢ $σ:Lott.Symbol.TabularTypes.TypeScheme : $κ:Lott.Symbol.TabularTypes.Kind]]) =>
    `($(Lean.mkIdent `KindingAndElaboration) [[$(.mk Γc):Lott.Symbol]] [[$(.mk Γ):Lott.Symbol]] [[$(.mk σ):Lott.Symbol]] [[$(.mk κ):Lott.Symbol]] _)

@[lott_tex_elab kinding]
private
def kindingTexElab : Lott.TexElab := fun profile ref stx => do
  let `(kinding| $Γc:Lott.Symbol.TabularTypes.ClassEnvironment; $Γ:Lott.Symbol.TabularTypes.TypeEnvironment ⊢ $σ:Lott.Symbol.TabularTypes.TypeScheme : $κ:Lott.Symbol.TabularTypes.Kind) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let Γc ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.ClassEnvironment profile ref Γc
  let Γ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.TypeEnvironment profile ref Γ
  let σ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.TypeScheme profile ref σ
  let κ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.Kind profile ref κ
  return s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {σ} \\, \\kindingsym \\, {κ}"

judgement TypeScheme.KindingAndElaboration where

a : κ ∈ Γ
───────────────── var
Γc; Γ ⊢ a : κ ⇝ a

Γc; Γ ⊢ ϕ : κ₀ ↦ κ₁ ⇝ A
Γc; Γ ⊢ τ : κ₀ ⇝ B
─────────────────────── app
Γc; Γ ⊢ ϕ τ : κ₁ ⇝ A B

Γc; Γ ⊢ τ₀ : * ⇝ A
Γc; Γ ⊢ τ₁ : * ⇝ B
─────────────────────────── arr
Γc; Γ ⊢ τ₀ → τ₁ : * ⇝ A → B

Γc; Γ ⊢ ψ : C ⇝ A
Γc; Γ ⊢ γ : * ⇝ B
───────────────────────── qual
Γc; Γ ⊢ ψ ⇒ γ : * ⇝ A → B

∀ a ∉ I, Γc; Γ, a : κ ⊢ σ^a : * ⇝ A^a
notex for noelab ⊢ κ ⇝ K
───────────────────────────────────── scheme (I : List TypeVarId)
Γc; Γ ⊢ ∀ a : κ. σ : * ⇝ ∀ a : K. A

───────────────────────── label
Γc; Γ ⊢ ℓ : L ⇝ ⊗ { : * }

Γc; Γ ⊢ ξ : L
─────────────────────────── floor
Γc; Γ ⊢ ⌊ξ⌋ : * ⇝ ⊗ { : * }

───────────────────────── comm
Γc; Γ ⊢ u : U ⇝ ⊗ { : * }

</ Γc; Γ ⊢ ξ@i : L // i in [:n] notex />
unique(</ ξ@i // i in [:n] notex />)
</ Γc; Γ ⊢ τ@i : κ ⇝ A@i // i in [:n] notex />
notex ⊢ κ ⇝ K
notex n ≠ 0 ∨ b
───────────────────────────────────────────────────────────────────────────────────────────────────────────────── row
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] notex /> </ : κ // b />⟩ : R κ ⇝ {</ A@i // i in [:n] notex /> </ : K // b />}

Γc; Γ ⊢ μ : U
Γc; Γ ⊢ ρ : R * ⇝ A
──────────────────────── prod
Γc; Γ ⊢ Π(μ) ρ : * ⇝ ⊗ A

Γc; Γ ⊢ μ : U
Γc; Γ ⊢ ρ : R * ⇝ A
──────────────────────── sum
Γc; Γ ⊢ Σ(μ) ρ : * ⇝ ⊕ A

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ τ^a : κ₁ ⇝ A^a
notex for noelab ⊢ κ₀ ⇝ K₀
Γc; Γ ⊢ ρ : R κ₀ ⇝ B
─────────────────────────────────────────────────────── lift (I : List TypeVarId)
Γc; Γ ⊢ Lift (λ a : κ₀. τ) ρ : R κ₁ ⇝ (λ a : K₀. A) ⟦B⟧

Γc; Γ ⊢ μ : U
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab ⊢ κ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────── contain
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ : C ⇝ ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)}

Γc; Γ ⊢ μ : U
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab ⊢ κ ⇝ K
notex for noelab Γc; Γ ⊢ ρ₀ ≲(μ) ρ₂ : C ⇝ Bₗ
notex for noelab Γc; Γ ⊢ ρ₁ ≲(μ) ρ₂ : C ⇝ Bᵣ
notex for noelab Bₙ := ∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧)
notex for noelab Bₑ := ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concat
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ : C ⇝ ⊗ {Bₙ, Bₑ, Bₗ, Bᵣ}

(</ TC'@i a ⇝ A'@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
Γc; Γ ⊢ τ : κ ⇝ B
───────────────────────────────────────────────────────────────────── tc {TC}
Γc; Γ ⊢ TC τ : C ⇝ ⊗ {A^^B/a, </ A'@i^^B/a // i in [:n] notex />}

∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
notex for noelab ⊢ κ ⇝ K
Γc; Γ ⊢ ρ : R κ ⇝ B
───────────────────────────────────────────────────── all (I : List TypeVarId)
Γc; Γ ⊢ All (λ a : κ. ψ) ρ : C ⇝ ⊗ ((λ a : K. A) ⟦B⟧)

Γc; Γ ⊢ ρ : R κ ⇝ A
notex for noelab ⊢ κ ⇝ K
notex for noelab ∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, Γc; Γ, aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ ⊢ aₚ ⊙(N) ⟨aₗ ▹ aₜ⟩ ~ aᵢ : C ⇝ Bₗ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1
notex for noelab ∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, Γc; Γ, aᵢ : R κ, aₙ : R κ ⊢ aᵢ ⊙(N) aₙ ~ ρ : C ⇝ Bᵣ^aᵢ#1^aₙ
notex for noelab Aₛ := ∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bₗ → Bᵣ → (⊗ { : * }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ind (I₀ I₁)
Γc; Γ ⊢ Ind ρ : C ⇝ ∀ aₘ : (L K) ↦ *. Aₛ → (aₘ$0 { : K }) → aₘ$0 A

Γc; Γ ⊢ (Lift (λ a : κ. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ : C ⇝ A
─────────────────────────────────────────────────── split
Γc; Γ ⊢ Split (λ a : κ. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ : C ⇝ A

end TabularTypes
