import Lott.Elab.JudgementComprehension
import Lott.Elab.OrJudgement
import Lott.Elab.UniversalJudgement
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.Semantics.Kind
import TabularTypeInterpreter.Semantics.TypeEnvironment.Basic
import TabularTypeInterpreter.Semantics.ClassEnvironment.Basic

namespace TabularTypeInterpreter

judgement_syntax ℓ " ≠ " ℓ' : Label.Ne

def Label.Ne := _root_.Ne (α := Label)

judgement_syntax "unique" "(" sepBy(ξ, ", ") ")" : Monotype.label.Uniqueness

judgement Monotype.label.Uniqueness where

</ </ ℓ@i ≠ ℓ@j // j in [i + 1:n] /> // i in [:n] />
──────────────────────────────────────────────────── concrete
unique(</ ℓ@i // i in [:n] />)

───────── var
unique(ξ)

open «F⊗⊕ω»

judgement_syntax Γc "; " Γ " ⊢ " σ " : " κ " ⇝ " A : TypeScheme.KindingAndElaboration

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
Γc; Γ ⊢ γ : κ ⇝ B
⊢ κ ⇝ *
───────────────────────── qual
Γc; Γ ⊢ ψ ⇒ γ : κ ⇝ A → B

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ σ^a : κ₁ ⇝ A^a
⊢ κ₀ ⇝ K₀
─────────────────────────────────────── scheme (I : List TypeVarId)
Γc; Γ ⊢ ∀ a : κ₀. σ : κ₁ ⇝ ∀ a : K₀. A

───────────────────── label
Γc; Γ ⊢ ℓ : L ⇝ ⊗ { }

Γc; Γ ⊢ ξ : L ⇝ A
─────────────────────── floor
Γc; Γ ⊢ ⌊ξ⌋ : * ⇝ ⊗ { }

───────────────────── comm
Γc; Γ ⊢ u : U ⇝ ⊗ { }

</ Γc; Γ ⊢ ξ@i : L ⇝ B@i // i in [:n] notex />
unique(</ ξ@i // i in [:n] notex />)
</ Γc; Γ ⊢ τ@i : κ ⇝ A@i // i in [:n] notex />
notex n ≠ 0 ∨ b
────────────────────────────────────────────────────────────────────────────────────────────────── row
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] notex /> </ : κ // b />⟩ : R κ ⇝ {</ A@i // i in [:n] notex />}

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ : R * ⇝ A
──────────────────────── prod
Γc; Γ ⊢ Π(μ) ρ : * ⇝ ⊗ A

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ : R * ⇝ A
──────────────────────── sum
Γc; Γ ⊢ Σ(μ) ρ : * ⇝ ⊕ A

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ τ^a : κ₁ ⇝ A^a
⊢ κ₀ ⇝ K₀
Γc; Γ ⊢ ρ : R κ₀ ⇝ B
─────────────────────────────────────────────────────── lift (I : List TypeVarId)
Γc; Γ ⊢ Lift (λ a : κ₀. τ) ρ : R κ₁ ⇝ (λ a : K₀. A) ⟦B⟧

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
⊢ κ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────── contain
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ : C ⇝ ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)}

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
⊢ κ ⇝ K
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₂ : C ⇝ Bₗ
Γc; Γ ⊢ ρ₁ ≲(μ) ρ₂ : C ⇝ Bᵣ
Bₙ := ∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧)
Bₑ := ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concat
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ : C ⇝ ⊗ {Bₙ, Bₑ, Bₗ, Bᵣ}

(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
Γc; Γ ⊢ τ : κ ⇝ B
───────────────────────────────────────────────────────────────────── tc {TC}
Γc; Γ ⊢ TC τ : C ⇝ ⊗ {A^^B/a, </ Aₛ@i^^B/a // i in [:n] notex />}

∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
⊢ κ ⇝ K
Γc; Γ ⊢ ρ : R κ ⇝ B
───────────────────────────────────────────────────── all (I : List TypeVarId)
Γc; Γ ⊢ All (λ a : κ. ψ) ρ : C ⇝ ⊗ ((λ a : K. A) ⟦B⟧)

Γc; Γ ⊢ ρ : R κ ⇝ A
⊢ κ ⇝ K
∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀, Γc; Γ, aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ, aₙ : R κ ⊢ ⟨aₗ ▹ aₜ⟩ ⊙(N) aₚ ~ aᵢ : C ⇝ Bᵣ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1^aₙ
∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, Γc; Γ, aᵢ : R κ, aₙ : R κ ⊢ aₙ ⊙(N) aᵢ ~ ρ : C ⇝ Bₗ^aᵢ#1^aₙ
Aₛ := ∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → (⊗ { }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── «ind» (I₀ I₁)
Γc; Γ ⊢ Ind ρ : C ⇝ ∀ aₘ : (L K) ↦ *. Aₛ → (aₘ$0 { }) → aₘ$0 A

Γc; Γ ⊢ (Lift (λ a : *. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ : C ⇝ A
─────────────────────────────────────────────────── split
Γc; Γ ⊢ Split (λ a : *. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ : C ⇝ A

judgement_syntax Γc "; " Γ " ⊢ " ρ₀ " ≡" "(" μ ") " ρ₁ " ⇝ " Fₚ ", " Fₛ : Monotype.RowEquivalenceAndElaboration (tex := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {ρ₀} \\, \\lottsym\{≡}_\{{μ}} \\, {ρ₁} \\, \\lottsym\{⇝} \\, {Fₚ} \\, \\lottsym\{,} \\, {Fₛ}")

judgement Monotype.RowEquivalenceAndElaboration where

Γc; Γ ⊢ ρ : R κ ⇝ A
⊢ κ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────── refl
Γc; Γ ⊢ ρ ≡(μ) ρ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0

/-
symm is not included directly as a rule because the elaboration functions are directional (they
convert from an elaborated prod or sum of the lhs to the same of the rhs), so a symm rule would have
to magically find the inverse function term based on the original direction. Instead, we include a
lemma proving symmetry in ../../Lemmas/Type.lean.
-/

Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
⊢ κ ⇝ K
Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ₀₁, Fₛ₀₁
Γc; Γ ⊢ ρ₁ ≡(μ) ρ₂ ⇝ Fₚ₁₂, Fₛ₁₂
Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₀⟧). Fₚ₁₂ [a$0] ⦅Fₚ₀₁ [a$0] x$0⦆
Fₛ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₀⟧). Fₛ₁₂ [a$0] ⦅Fₛ₀₁ [a$0] x$0⦆
────────────────────────────────────────────────────────────────── trans
Γc; Γ ⊢ ρ₀ ≡(μ) ρ₂ ⇝ Fₚ, Fₛ

p_ permutes [:n]
p_' permutes [:n]
p_ inverts p_' on [:n]
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b notex />⟩ : R κ ⇝ {</ A@i // i in [:n] />}
⊢ κ ⇝ K
Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦{</ A@i // i in [:n] />}⟧). (</ π i x$0 // (tex := "i \\in p") i in p_ />)
Fₛ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦{</ A@i // i in [:n] />}⟧). case x$0 {</ λ x' : a$0 A@i. ι j x'$0 // (tex := "i \\in [:n], j \\in p'") (i, j) in [:n].toList.zip p_' />}
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── comm
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b notex />⟩ ≡(C) ⟨</ ξ@i ▹ τ@i // i in p_ /> </ : κ // b notex />⟩ ⇝ Fₚ, Fₛ

Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ : R κ₁ ⇝ A
⊢ κ₁ ⇝ K
Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0
Fₛ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftL (μ)
Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ ≡(μ) ⟨</ ξ@i ▹ τ₁^^τ₀@i/a // i in [:n] notex /> </ : κ₁ // b notex />⟩ ⇝ Fₚ, Fₛ

Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ : R κ₁ ⇝ A
⊢ κ₁ ⇝ K
Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0
Fₛ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftR (μ)
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ₁^^τ₀@i/a // i in [:n] notex /> </ : κ₁ // b notex />⟩ ≡(μ) Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ ⇝ Fₚ, Fₛ

judgement_syntax Γc "; " Γ " ⊢ " σ₀ " <: " σ₁ " ⇝ " F : TypeScheme.SubtypingAndElaboration

judgement TypeScheme.SubtypingAndElaboration where

Γc; Γ ⊢ σ : κ ⇝ A
───────────────────────────── refl
Γc; Γ ⊢ σ <: σ ⇝ λ x : A. x$0

-- TODO: Add transitivity

-- TODO: Explain why we don't have an app rule here in the paper.

Γc; Γ ⊢ τ₂ <: τ₀ ⇝ E
Γc; Γ ⊢ τ₁ <: τ₃ ⇝ F
Γc; Γ ⊢ τ₀ → τ₁ : * ⇝ A
Γc; Γ ⊢ τ₂ : * ⇝ B
──────────────────────────────────────────────────────────────── arr
Γc; Γ ⊢ τ₀ → τ₁ <: τ₂ → τ₃ ⇝ λ x : A. λ xₐ : B. F ⦅x$1 ⦅E xₐ$0⦆⦆

Γc; Γ ⊢ ψ₁ <: ψ₀ ⇝ E
Γc; Γ ⊢ γ₀ <: γ₁ ⇝ F
Γc; Γ ⊢ ψ₀ ⇒ γ₀ : κ ⇝ A
Γc; Γ ⊢ ψ₁ : C ⇝ B
──────────────────────────────────────────────────────────────── qual
Γc; Γ ⊢ ψ₀ ⇒ γ₀ <: ψ₁ ⇒ γ₁ ⇝ λ x : A. λ xₐ : B. F ⦅x$1 ⦅E xₐ$0⦆⦆

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ σ₀^a <: σ₁^a ⇝ F^a
⊢ κ₀ ⇝ K₀
Γc; Γ ⊢ ∀ a : κ₀. σ₀ : κ₁ ⇝ A
─────────────────────────────────────────────────────────────────────── scheme (I : List TypeVarId)
Γc; Γ ⊢ ∀ a : κ₀. σ₀ <: ∀ a : κ₀. σ₁ ⇝ λ x : A. Λ a : K₀. F ⦅x$0 [a$0]⦆

</ Γc; Γ ⊢ τ₀@i <: τ₁@i ⇝ F@i // i in [:n] notex />
Γc; Γ ⊢ Π(μ) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : * // b notex />⟩ : * ⇝ A
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── prod
Γc; Γ ⊢ Π(μ) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : * // b notex />⟩ <: Π(μ) ⟨</ ξ@i ▹ τ₁@i // i in [:n] notex /> </ : * // b notex />⟩ ⇝ λ x : A. (</ F@i π i x$0 // i in [:n] notex />)

</ Γc; Γ ⊢ τ₀@i <: τ₁@i ⇝ F@i // i in [:n] notex />
Γc; Γ ⊢ Σ(μ) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : * // b notex />⟩ : * ⇝ A
</ Γc; Γ ⊢ τ₀@i : * ⇝ B@i // i in [:n] notex />
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sum
Γc; Γ ⊢ Σ(μ) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : * // b notex />⟩ <: Σ(μ) ⟨</ ξ@i ▹ τ₁@i // i in [:n] notex /> </ : * // b notex />⟩ ⇝ λ x : A. case x$0 {</ λ x' : B@i. ι i ⦅F@i x'$0⦆ // i in [:n] notex />}

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ
Γc; Γ ⊢ Π(μ) ρ₀ : * ⇝ A
────────────────────────────────────────────── prodRow
Γc; Γ ⊢ Π(μ) ρ₀ <: Π(μ) ρ₁ ⇝ Fₚ [λ a : *. a$0]

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ
Γc; Γ ⊢ Σ(μ) ρ₀ : * ⇝ A
────────────────────────────────────────────── sumRow
Γc; Γ ⊢ Σ(μ) ρ₀ <: Σ(μ) ρ₁ ⇝ Fₛ [λ a : *. a$0]

Γc; Γ ⊢ Ξ(N) ρ : * ⇝ A
Γc; Γ ⊢ μ : U ⇝ B
─────────────────────────────────────── decay
Γc; Γ ⊢ Ξ(N) ρ <: Ξ(μ) ρ ⇝ λ x : A. x$0

Γc; Γ ⊢ μ : U ⇝ A
Γc; Γ ⊢ σ : * ⇝ B
───────────────────────────────────────────────────── never
Γc; Γ ⊢ Σ(μ) ⟨ : * ⟩ <: σ ⇝ λ x : ⊕ { }. case x$0 { }

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₂ ⇝ F₀₂ₚ, F₀₂ₛ
Γc; Γ ⊢ ρ₁ ≡(μ) ρ₃ ⇝ F₁₃ₚ, F₁₃ₛ
Γc; Γ ⊢ ρ₂ ≡(μ) ρ₀ ⇝ F₂₀ₚ, F₂₀ₛ
Γc; Γ ⊢ ρ₃ ≡(μ) ρ₁ ⇝ F₃₁ₚ, F₃₁ₛ
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ : C ⇝ A
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
Γc; Γ ⊢ ρ₃ : R κ ⇝ A₃
⊢ κ ⇝ K
Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₃⟧). F₀₂ₚ [a$0] ⦅⦅π 0 xₑ$1⦆ [a$0] ⦅F₃₁ₚ [a$0] x$0⦆⦆
Fᵢ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₂⟧). F₁₃ₛ [a$0] ⦅⦅π 1 xₑ$1⦆ [a$0] ⦅F₂₀ₛ [a$0] x$0⦆⦆
───────────────────────────────────────────────────────────────────────────────────── contain
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ <: ρ₂ ≲(μ) ρ₃ ⇝ λ xₑ : A. (Fₚ, Fᵢ)

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₃ ⇝ F₀₃ₚ, F₀₃ₛ
Γc; Γ ⊢ ρ₁ ≡(μ) ρ₄ ⇝ F₁₄ₚ, F₁₄ₛ
Γc; Γ ⊢ ρ₂ ≡(μ) ρ₅ ⇝ F₂₅ₚ, F₂₅ₛ
Γc; Γ ⊢ ρ₃ ≡(μ) ρ₀ ⇝ F₃₀ₚ, F₃₀ₛ
Γc; Γ ⊢ ρ₄ ≡(μ) ρ₁ ⇝ F₄₁ₚ, F₄₁ₛ
Γc; Γ ⊢ ρ₅ ≡(μ) ρ₂ ⇝ F₅₂ₚ, F₅₂ₛ
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ : C ⇝ A
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
Γc; Γ ⊢ ρ₃ : R κ ⇝ A₃
Γc; Γ ⊢ ρ₄ : R κ ⇝ A₄
Γc; Γ ⊢ ρ₅ : R κ ⇝ A₅
⊢ κ ⇝ K
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₂ <: ρ₃ ≲(μ) ρ₅ ⇝ F₀₂₃₅
Γc; Γ ⊢ ρ₁ ≲(μ) ρ₂ <: ρ₄ ≲(μ) ρ₅ ⇝ F₁₂₄₅
Fₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A₃⟧). λ xᵣ : ⊗ (a$0 ⟦A₄⟧). F₂₅ₚ [a$0] ⦅⦅⦅π 0 xₑ$2⦆ [a$0] ⦅F₃₀ₚ [a$0] xₗ$1⦆⦆ ⦅F₄₁ₚ [a$0] xᵣ$0⦆⦆
Fₑᵢ := ⦅⦅⦅π 1 xₑ$3⦆ [a$1] [aₜ$0] ⦅λ xₗ' : ⊕ (a$1 ⟦A₀⟧). xₗ$3 ⦅F₀₃ₛ [a$1] xₗ'$0⦆⦆⦆ ⦅λ xᵣ' : ⊕ (a$1 ⟦A₁⟧). xᵣ$2 ⦅F₁₄ₛ [a$1] xᵣ'$0⦆⦆⦆ ⦅F₅₂ₛ [a$1] x$0⦆
Fₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A₃⟧)) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A₄⟧)) → aₜ$0 . λ x : ⊕ (a$1 ⟦A₅⟧). Fₑᵢ
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concat
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ <: ρ₃ ⊙(μ) ρ₄ ~ ρ₅ ⇝ λ xₑ : A. (Fₙ, Fₑ, F₀₂₃₅ ⦅π 2 xₑ$0⦆, F₁₂₄₅ ⦅π 3 xₑ$0⦆)

/-
NOTE: The evidence of this first hypothesis isn't actually used, it's just present to prevent
unexpected behaviour.
-/
Γc; Γ ⊢ τ₀ <: τ₁ ⇝ E
Γc; Γ ⊢ σ^^τ₀/a <: σ^^τ₁/a ⇝ F
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ B ∈ Γc
</ Γc; Γ ⊢ TCₛ@i τ₀ <: TCₛ@i τ₁ ⇝ Fₛ@i // i in [:n] notex />
Γc; Γ ⊢ TC τ₀ : C ⇝ A
────────────────────────────────────────────────────────────────────────────────────────── tc {TC}
Γc; Γ ⊢ TC τ₀ <: TC τ₁ ⇝ λ x : A. (F π 0 x$0, </ Fₛ@i π (i + 1) x$0 // i in [:n] notex />)

/-
NOTE: The evidence of this first hypothesis isn't actually used, it's just present to prevent
unexpected behaviour. We allow C commutativity since the second hypothesis will still block things
if the method uses them non-commutatively.
-/
Γc; Γ ⊢ ρ₀ ≡(C) ρ₁ ⇝ Eₚ, Eₛ
Γc; Γ ⊢ σ^^ρ₀/a <: σ^^ρ₁/a ⇝ F
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ B ∈ Γc
</ Γc; Γ ⊢ TCₛ@i ρ₀ <: TCₛ@i ρ₁ ⇝ Fₛ@i // i in [:n] notex />
Γc; Γ ⊢ TC ρ₀ : C ⇝ A
────────────────────────────────────────────────────────────────────────────────────────── tcRow {TC}
Γc; Γ ⊢ TC ρ₀ <: TC ρ₁ ⇝ λ x : A. (F π 0 x$0, </ Fₛ@i π (i + 1) x$0 // i in [:n] notex />)

Γc; Γ ⊢ ρ₀ ≡(C) ρ₁ ⇝ Fₚ, Fₛ
Γc; Γ ⊢ All (λ a : κ. ψ) ρ₀ : C ⇝ A
∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ B^a
⊢ κ ⇝ K
──────────────────────────────────────────────────────────────────── allRow (I : List TypeVarId)
Γc; Γ ⊢ All (λ a : κ. ψ) ρ₀ <: All (λ a : κ. ψ) ρ₁ ⇝ Fₚ [λ a : K. B]

Γc; Γ ⊢ (Lift (λ a : *. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ <: (Lift (λ a : *. τ) ρ₃) ⊙(C) ρ₄ ~ ρ₅ ⇝ F
────────────────────────────────────────────────────────────────────────────────────── split
Γc; Γ ⊢ Split (λ a : *. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ <: Split (λ a : *. τ) ρ₃ ⊙' ρ₄ ~ ρ₅ ⇝ F

end TabularTypeInterpreter
