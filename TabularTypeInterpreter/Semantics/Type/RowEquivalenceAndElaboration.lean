import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax Γc "; " Γ " ⊢ " ρ₀ " ≡" "(" μ ") " ρ₁ " ⇝ " Fₚ ", " Fₛ : Monotype.RowEquivalenceAndElaboration (tex := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {ρ₀} \\, \\lottsym\{≡}_\{{μ}} \\, {ρ₁} \\, \\lottsym\{⇝} \\, {Fₚ} \\, \\lottsym\{,} \\, {Fₛ}")

judgement Monotype.RowEquivalenceAndElaboration where

Γc; Γ ⊢ ρ : R κ ⇝ A
⊢ κ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────── refl
Γc; Γ ⊢ ρ ≡(μ) ρ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0

/-
symm is not included directly as a rule because the elaboration functions are directional (they
convert from an elaborated prod or sum of the lhs to the same of the rhs), so a symm rule would have
to magically find the inverse function term based on the original direction.
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

end TabularTypeInterpreter
