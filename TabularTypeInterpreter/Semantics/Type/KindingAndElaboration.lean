import Lott.DSL.Elab.JudgementComprehension
import Lott.DSL.Elab.OrJudgement
import Lott.DSL.Elab.UniversalJudgement
import TabularTypeInterpreter.Data.Range
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.Semantics.Kind
import TabularTypeInterpreter.Semantics.TypeEnvironment
import TabularTypeInterpreter.Semantics.ClassEnvironment

namespace TabularTypeInterpreter

judgement_syntax ℓ " ≠ " ℓ' : Label.Ne

def Label.Ne := _root_.Ne (α := Label)

judgement_syntax "unique" "(" sepBy(ξ, ", ") ")" : Monotype.label.Uniqueness

judgement Monotype.label.Uniqueness :=

</ </ ℓ@i ≠ ℓ@j // j in [i + 1:n] /> // i in [:n] />
──────────────────────────────────────────────────── concrete
unique(</ ℓ@i // i in [:n] />)

───────── var
unique(ξ)

open «F⊗⊕ω»

judgement_syntax Γc "; " Γ " ⊢ " σ " : " κ " ⇝ " A : TypeScheme.KindingAndElaboration

judgement_syntax Γc " ⊢ " Γ " ⇝ " Δ : TypeEnvironment.WellFormednessAndElaboration

judgement_syntax "⊢c " Γc : ClassEnvironment.WellFormedness

mutual

judgement TypeScheme.KindingAndElaboration :=

a : κ ∈ Γ
───────────────── var
Γc; Γ ⊢ a : κ ⇝ a

Γc; Γ ⊢ φ : κ₀ ↦ κ₁ ⇝ A
Γc; Γ ⊢ τ : κ₀ ⇝ B
─────────────────────── app
Γc; Γ ⊢ φ τ : κ₁ ⇝ A B

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

</ Γc; Γ ⊢ ξ@i : L ⇝ B@i // i in [:n] />
unique(</ ξ@i // i in [:n] />)
</ Γc; Γ ⊢ τ@i : κ ⇝ A@i // i in [:n] />
n ≠ 0 ∨ b
────────────────────────────────────────────────────────────────────────────────────── row
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b />⟩ : R κ ⇝ {</ A@i // i in [:n] />}

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
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concat
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ : C ⇝ ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0, Bₗ, Bᵣ}

⊢c Γc
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
Γc; Γ ⊢ τ : κ ⇝ B
─────────────────────────────────────────────────────────────── tc {TC}
Γc; Γ ⊢ TC τ : C ⇝ ⊗ {A^^B, </ Aₛ@i^^B // i in [:n] />}

∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
⊢ κ ⇝ K
Γc; Γ ⊢ ρ : R κ ⇝ B
───────────────────────────────────────────────────── all (I : List TypeVarId)
Γc; Γ ⊢ All (λ a : κ. ψ) ρ : C ⇝ ⊗ ((λ a : K. A) ⟦B⟧)

Γc; Γ ⊢ ρ : R κ ⇝ A
⊢ κ ⇝ K
∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀, Γc; Γ, aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ, aₙ : R κ ⊢ ⟨aₗ ▹ aₜ⟩ ⊙(N) aₚ ~ aᵢ : C ⇝ Bᵣ^aₙ^aᵢ^aₚ^aₜ^aₗ
∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, Γc; Γ, aᵢ : R κ, aₙ : R κ ⊢ aᵢ ⊙(N) aₙ ~ ρ : C ⇝ Bₗ^aₙ^aᵢ
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ind (I₀ I₁)
Γc; Γ ⊢ Ind ρ : C ⇝ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → aₗ$4 → aₘ$5 aₚ$2 → aₘ$5 aₙ$0) → aₘ$5 { } → aₘ$5 A

Γc; Γ ⊢ (Lift (λ a : *. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ : C ⇝ A
─────────────────────────────────────────────────── split
Γc; Γ ⊢ Split (λ a : *. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ : C ⇝ A

judgement TypeEnvironment.WellFormednessAndElaboration :=

────────── empty
Γc ⊢ ε ⇝ ε

Γc ⊢ Γ ⇝ Δ
a ∉ dom(Γ)
⊢ κ ⇝ K
──────────────────────── typeExt
Γc ⊢ Γ, a : κ ⇝ Δ, a : K

Γc ⊢ Γ ⇝ Δ
x ∉ dom'(Γ)
Γc; Γ ⊢ σ : * ⇝ A
──────────────────────── termExt
Γc ⊢ Γ, x : σ ⇝ Δ, x : A

Γc ⊢ Γ ⇝ Δ
x ∉ dom'(Γ)
Γc; Γ ⊢ ψ : C ⇝ A
──────────────────────── constrExt
Γc ⊢ Γ, ψ ⇝ x ⇝ Δ, x : A

judgement ClassEnvironment.WellFormedness :=

──── empty
⊢c ε

⊢c Γc
⊢ κ ⇝ K
∀ a, Γc; ε, a : κ ⊢ σ : * ⇝ A^a
∀ a, ε, a : K ⊢ A^a : *
</ ∀ a, Γc; ε, a : κ ⊢ TCₛ@i a : * ⇝ Aₛ@i^a // i in [:n] />
</ ∀ a, ε, a : K ⊢ Aₛ@i^a : * // i in [:n] />
───────────────────────────────────────────────────────────────── ext {TC}
⊢c Γc, (</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A

end

judgement_syntax Γc "; " Γ " ⊢ " ρ₀ " ≡" "(" μ ") " ρ₁ " ⇝ " Fₚ ", " Fₛ : Monotype.RowEquivalenceAndElaboration

judgement Monotype.RowEquivalenceAndElaboration :=

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
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── trans
Γc; Γ ⊢ ρ₀ ≡(μ) ρ₂ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₀⟧). Fₚ₁₂ [a$0] ⦅Fₚ₀₁ [a$0] x$0⦆, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₀⟧). Fₛ₁₂ [a$0] ⦅Fₛ₀₁ [a$0] x$0⦆

-- TODO: Add comment to latex output to explain relationship between [:n], p, and p'.
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b />⟩ : R κ ⇝ {</ A@i // i in [:n] />}
⊢ κ ⇝ K
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── comm {p p' : List Nat} (perm : List.Perm p [:n]) (perm' : List.Perm p' [:n]) (inv : Std.Range.get!InverseOn p p' n)
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b />⟩ ≡(C) ⟨</ ξ@i ▹ τ@i // i in p /> </ : κ // b />⟩ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦{</ A@i // i in [:n] />}⟧). (</ π n' x$0 // n' in p />), Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦{</ A@i // i in [:n] />}⟧). case x$0 {</ λ x' : a$0 A@i. ι n' x'$0 // (i, n') in [:n].toList.zip p' />}

Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] /> </ : κ₀ // b />⟩ : R κ₁ ⇝ A
⊢ κ₁ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftL (μ)
Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] /> </ : κ₀ // b />⟩ ≡(μ) ⟨</ ξ@i ▹ τ₁^^τ₀@i // i in [:n] /> </ : κ₁ // b />⟩ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0

Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] /> </ : κ₀ // b />⟩ : R κ₁ ⇝ A
⊢ κ₁ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftR (μ)
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ₁^^τ₀@i // i in [:n] /> </ : κ₁ // b />⟩ ≡(μ) Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] /> </ : κ₀ // b />⟩ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0

end TabularTypeInterpreter
