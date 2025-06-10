import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax Γc "; " Γ " ⊢ " ρ₀ " ≡" "(" μ ") " ρ₁ " ⇝ " Fₚ ", " Fₛ : Monotype.RowEquivalenceAndElaboration (tex := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {ρ₀} \\, \\rowequivsym_\{{μ}} \\, {ρ₁} \\, \\lottsym\{⇝} \\, {Fₚ} \\, \\lottsym\{,} \\, {Fₛ}") (tex noelab := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {ρ₀} \\, \\rowequivsym_\{{μ}} \\, {ρ₁}")

judgement Monotype.RowEquivalenceAndElaboration where

Γc; Γ ⊢ ρ : R κ ⇝ A
notex for noelab ⊢ κ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────── refl
Γc; Γ ⊢ ρ ≡(μ) ρ ⇝ Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0

/-
symm is not included directly as a rule because the elaboration functions are directional (they
convert from an elaborated prod or sum of the lhs to the same of the rhs), so a symm rule would have
to magically find the inverse function term based on the original direction.
-/

Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab ⊢ κ ⇝ K
Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ₀₁, Fₛ₀₁
Γc; Γ ⊢ ρ₁ ≡(μ) ρ₂ ⇝ Fₚ₁₂, Fₛ₁₂
notex for noelab Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₀⟧). Fₚ₁₂ [a$0] ⦅Fₚ₀₁ [a$0] x$0⦆
notex for noelab Fₛ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₀⟧). Fₛ₁₂ [a$0] ⦅Fₛ₀₁ [a$0] x$0⦆
─────────────────────────────────────────────────────────────────────────────────── trans
Γc; Γ ⊢ ρ₀ ≡(μ) ρ₂ ⇝ Fₚ, Fₛ

p_ permutes [:n]
notex for noelab p_' permutes [:n]
notex for noelab p_ inverts p_' on [:n]
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b notex />⟩ : R κ ⇝ {</ A@i // i in [:n] />}
notex for noelab ⊢ κ ⇝ K
notex for noelab Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦{</ A@i // i in [:n] />}⟧). (</ π i x$0 // (tex := "i \\in p") i in p_ />)
notex for noelab Fₛ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦{</ A@i // i in [:n] />}⟧). case x$0 {</ λ x' : a$0 A@i. ι j x'$0 // (tex := "i \\in [:n], j \\in p'") (i, j) in [:n].toList.zip p_' />}
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── comm
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ // b notex />⟩ ≡(C) ⟨</ ξ@i ▹ τ@i // (tex := "i \\in p") i in p_ /> </ : κ // b notex />⟩ ⇝ Fₚ, Fₛ

Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ : R κ₁ ⇝ A
notex for noelab ⊢ κ₁ ⇝ K
notex for noelab Fₚ := Λ a' : K ↦ *. λ x : ⊗ (a'$0 ⟦A⟧). x$0
notex for noelab Fₛ := Λ a' : K ↦ *. λ x : ⊕ (a'$0 ⟦A⟧). x$0
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftL (μ)
Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ ≡(μ) ⟨</ ξ@i ▹ τ₁^^τ₀@i/a // i in [:n] notex /> </ : κ₁ // b notex />⟩ ⇝ Fₚ, Fₛ

Γc; Γ ⊢ Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ : R κ₁ ⇝ A
notex for noelab ⊢ κ₁ ⇝ K
notex for noelab Fₚ := Λ a' : K ↦ *. λ x : ⊗ (a'$0 ⟦A⟧). x$0
notex for noelab Fₛ := Λ a' : K ↦ *. λ x : ⊕ (a'$0 ⟦A⟧). x$0
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftR (μ)
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ₁^^τ₀@i/a // i in [:n] notex /> </ : κ₁ // b notex />⟩ ≡(μ) Lift (λ a : κ₀. τ₁) ⟨</ ξ@i ▹ τ₀@i // i in [:n] notex /> </ : κ₀ // b notex />⟩ ⇝ Fₚ, Fₛ

syntax (name := rowEquivalence) Lott.Symbol.TabularTypeInterpreter.ClassEnvironment "; " Lott.Symbol.TabularTypeInterpreter.TypeEnvironment " ⊢ " Lott.Symbol.TabularTypeInterpreter.Monotype " ≡" "(" Lott.Symbol.TabularTypeInterpreter.Monotype ") " Lott.Symbol.TabularTypeInterpreter.Monotype : Lott.Judgement

macro_rules
  | `([[$Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment; $Γ:Lott.Symbol.TabularTypeInterpreter.TypeEnvironment ⊢ $ρ₀:Lott.Symbol.TabularTypeInterpreter.Monotype ≡($μ:Lott.Symbol.TabularTypeInterpreter.Monotype) $ρ₁:Lott.Symbol.TabularTypeInterpreter.Monotype]]) =>
    `(Monotype.RowEquivalenceAndElaboration [[$(.mk Γc):Lott.Symbol]] [[$(.mk Γ):Lott.Symbol]] [[$(.mk ρ₀):Lott.Symbol]] [[$(.mk μ):Lott.Symbol]] [[$(.mk ρ₁):Lott.Symbol]] _ _)

@[lott_tex_elab rowEquivalence]
private
def rowEquivalenceTexElab : Lott.TexElab := fun profile ref stx => do
  let `(rowEquivalence| $Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment; $Γ:Lott.Symbol.TabularTypeInterpreter.TypeEnvironment ⊢ $ρ₀:Lott.Symbol.TabularTypeInterpreter.Monotype ≡($μ:Lott.Symbol.TabularTypeInterpreter.Monotype) $ρ₁:Lott.Symbol.TabularTypeInterpreter.Monotype) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let Γc ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.ClassEnvironment profile ref Γc
  let Γ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeEnvironment profile ref Γ
  let ρ₀ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.Monotype profile ref ρ₀
  let μ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.Monotype profile ref μ
  let ρ₁ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeScheme profile ref ρ₁
  return s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {ρ₀} \\, \\rowequivsym_\{{μ}} \\, {ρ₁}"

end TabularTypeInterpreter
