import TabularTypeInterpreter.Semantics.Type.RowEquivalenceAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax μ₀ " ≤ " μ₁ : Monotype.CommutativityPartialOrdering (tex := s!"{μ₀} \\, \\partialordsym \\, {μ₁}")

judgement Monotype.CommutativityPartialOrdering where

───── refl
μ ≤ μ

───── «N»
N ≤ μ

───── «C»
μ ≤ C

syntax (name := subtyping) Lott.Symbol.TabularTypeInterpreter.ClassEnvironment "; " Lott.Symbol.TabularTypeInterpreter.TypeEnvironment " ⊢ " Lott.Symbol.TabularTypeInterpreter.TypeScheme " <: " Lott.Symbol.TabularTypeInterpreter.TypeScheme : Lott.Judgement

judgement_syntax Γc "; " Γ " ⊢ " σ₀ " <: " σ₁ " ⇝ " F : TypeScheme.SubtypingAndElaboration (tex := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {σ₀} \\, \\subtypingsym \\, {σ₁} \\, \\lottsym\{⇝} \\, {F}") (tex noelab := s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {σ₀} \\, \\subtypingsym \\, {σ₁}")

macro_rules
  | `([[$Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment; $Γ:Lott.Symbol.TabularTypeInterpreter.TypeEnvironment ⊢ $σ₀:Lott.Symbol.TabularTypeInterpreter.TypeScheme <: $σ₁:Lott.Symbol.TabularTypeInterpreter.TypeScheme]]) =>
    `($(Lean.mkIdent `SubtypingAndElaboration) [[$(.mk Γc):Lott.Symbol]] [[$(.mk Γ):Lott.Symbol]] [[$(.mk σ₀):Lott.Symbol]] [[$(.mk σ₁):Lott.Symbol]] _)

@[lott_tex_elab subtyping]
private
def subtypingTexElab : Lott.TexElab := fun profile ref stx => do
  let `(subtyping| $Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment; $Γ:Lott.Symbol.TabularTypeInterpreter.TypeEnvironment ⊢ $σ₀:Lott.Symbol.TabularTypeInterpreter.TypeScheme <: $σ₁:Lott.Symbol.TabularTypeInterpreter.TypeScheme) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let Γc ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.ClassEnvironment profile ref Γc
  let Γ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeEnvironment profile ref Γ
  let σ₀ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeScheme profile ref σ₀
  let σ₁ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeScheme profile ref σ₁
  return s!"{Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {σ₀} \\, \\subtypingsym \\, {σ₁}"

judgement TypeScheme.SubtypingAndElaboration where

Γc; Γ ⊢ σ : κ ⇝ A
────────────────────────────────── refl
Γc; Γ ⊢ σ <: σ ⇝ λ x : A. x$0

Γc; Γ ⊢ σ₀ : κ ⇝ A
Γc; Γ ⊢ σ₀ <: σ₁ ⇝ E
Γc; Γ ⊢ σ₁ <: σ₂ ⇝ F
───────────────────────────────────── trans
Γc; Γ ⊢ σ₀ <: σ₂ ⇝ λ x : A. F ⦅E x$0⦆

Γc; Γ ⊢ τ₂ <: τ₀ ⇝ E
Γc; Γ ⊢ τ₁ <: τ₃ ⇝ F
Γc; Γ ⊢ τ₀ → τ₁ : * ⇝ A
notex for noelab Γc; Γ ⊢ τ₂ : * ⇝ B
──────────────────────────────────────────────────────────────── arr
Γc; Γ ⊢ τ₀ → τ₁ <: τ₂ → τ₃ ⇝ λ x : A. λ xₐ : B. F ⦅x$1 ⦅E xₐ$0⦆⦆

Γc; Γ ⊢ ψ₁ <: ψ₀ ⇝ E
Γc; Γ ⊢ γ₀ <: γ₁ ⇝ F
Γc; Γ ⊢ ψ₀ ⇒ γ₀ : κ ⇝ A
notex for noelab Γc; Γ ⊢ ψ₁ : C ⇝ B
──────────────────────────────────────────────────────────────── qual
Γc; Γ ⊢ ψ₀ ⇒ γ₀ <: ψ₁ ⇒ γ₁ ⇝ λ x : A. λ xₐ : B. F ⦅x$1 ⦅E xₐ$0⦆⦆

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ σ₀^a <: σ₁^a ⇝ F^a
notex for noelab ⊢ κ₀ ⇝ K₀
Γc; Γ ⊢ ∀ a : κ₀. σ₀ : κ₁ ⇝ A
─────────────────────────────────────────────────────────────────────── scheme (I : List TypeVarId)
Γc; Γ ⊢ ∀ a : κ₀. σ₀ <: ∀ a : κ₀. σ₁ ⇝ λ x : A. Λ a : K₀. F ⦅x$0 [a$0]⦆

</ Γc; Γ ⊢ τ@i <: τ'@i ⇝ F@i // i in [:n] notex />
Γc; Γ ⊢ Π(μ) ⟨</ ξ@i ▹ τ@i // i in [:n] notex /> </ : * // b notex />⟩ : * ⇝ A
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── prod
Γc; Γ ⊢ Π(μ) ⟨</ ξ@i ▹ τ@i // i in [:n] notex /> </ : * // b notex />⟩ <: Π(μ) ⟨</ ξ@i ▹ τ'@i // i in [:n] notex /> </ : * // b notex />⟩ ⇝ λ x : A. (</ F@i π i x$0 // i in [:n] notex />)

</ Γc; Γ ⊢ τ@i <: τ'@i ⇝ F@i // i in [:n] notex />
Γc; Γ ⊢ Σ(μ) ⟨</ ξ@i ▹ τ@i // i in [:n] notex /> </ : * // b notex />⟩ : * ⇝ A
notex for noelab </ Γc; Γ ⊢ τ@i : * ⇝ B@i // i in [:n] notex />
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sum
Γc; Γ ⊢ Σ(μ) ⟨</ ξ@i ▹ τ@i // i in [:n] notex /> </ : * // b notex />⟩ <: Σ(μ) ⟨</ ξ@i ▹ τ'@i // i in [:n] notex /> </ : * // b notex />⟩ ⇝ λ x : A. case x$0 {</ λ x' : B@i. ι i ⦅F@i x'$0⦆ // i in [:n] notex />}

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ
Γc; Γ ⊢ Π(μ) ρ₀ : *
────────────────────────────────────────────── prodRow
Γc; Γ ⊢ Π(μ) ρ₀ <: Π(μ) ρ₁ ⇝ Fₚ [λ a : *. a$0]

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ
Γc; Γ ⊢ Σ(μ) ρ₀ : *
────────────────────────────────────────────── sumRow
Γc; Γ ⊢ Σ(μ) ρ₀ <: Σ(μ) ρ₁ ⇝ Fₛ [λ a : *. a$0]

Γc; Γ ⊢ Ξ(μ₀) ρ : * ⇝ A
Γc; Γ ⊢ μ₁ : U
μ₀ ≤ μ₁
─────────────────────────────────────── decay
Γc; Γ ⊢ Ξ(μ₀) ρ <: Ξ(μ₁) ρ ⇝ λ x : A. x$0

Γc; Γ ⊢ σ : *
───────────────────────────────────────────────────────── never
Γc; Γ ⊢ Σ(C) ⟨ : * ⟩ <: σ ⇝ λ x : ⊕ { : * }. case x$0 { }

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₂ ⇝ F₀₂ₚ, F₀₂ₛ
Γc; Γ ⊢ ρ₁ ≡(μ) ρ₃ ⇝ F₁₃ₚ, F₁₃ₛ
notex for noelab Γc; Γ ⊢ ρ₂ ≡(μ) ρ₀ ⇝ F₂₀ₚ, F₂₀ₛ
notex for noelab Γc; Γ ⊢ ρ₃ ≡(μ) ρ₁ ⇝ F₃₁ₚ, F₃₁ₛ
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ : C ⇝ A
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab Γc; Γ ⊢ ρ₃ : R κ ⇝ A₃
notex for noelab ⊢ κ ⇝ K
notex for noelab Fₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₃⟧). F₀₂ₚ [a$0] ⦅⦅π 0 xₑ$1⦆ [a$0] ⦅F₃₁ₚ [a$0] x$0⦆⦆
notex for noelab Fᵢ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₂⟧). F₁₃ₛ [a$0] ⦅⦅π 1 xₑ$1⦆ [a$0] ⦅F₂₀ₛ [a$0] x$0⦆⦆
────────────────────────────────────────────────────────────────────────────────────────────────────── contain
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ <: ρ₂ ≲(μ) ρ₃ ⇝ λ xₑ : A. (Fₚ, Fᵢ)

Γc; Γ ⊢ ρ₀ ≡(μ) ρ₃ ⇝ F₀₃ₚ, F₀₃ₛ
Γc; Γ ⊢ ρ₁ ≡(μ) ρ₄ ⇝ F₁₄ₚ, F₁₄ₛ
Γc; Γ ⊢ ρ₂ ≡(μ) ρ₅ ⇝ F₂₅ₚ, F₂₅ₛ
notex for noelab Γc; Γ ⊢ ρ₃ ≡(μ) ρ₀ ⇝ F₃₀ₚ, F₃₀ₛ
notex for noelab Γc; Γ ⊢ ρ₄ ≡(μ) ρ₁ ⇝ F₄₁ₚ, F₄₁ₛ
notex for noelab Γc; Γ ⊢ ρ₅ ≡(μ) ρ₂ ⇝ F₅₂ₚ, F₅₂ₛ
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ : C ⇝ A
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab Γc; Γ ⊢ ρ₃ : R κ ⇝ A₃
notex for noelab Γc; Γ ⊢ ρ₄ : R κ ⇝ A₄
notex for noelab Γc; Γ ⊢ ρ₅ : R κ ⇝ A₅
notex for noelab ⊢ κ ⇝ K
notex for noelab Γc; Γ ⊢ ρ₀ ≲(μ) ρ₂ <: ρ₃ ≲(μ) ρ₅ ⇝ F₀₂₃₅
notex for noelab Γc; Γ ⊢ ρ₁ ≲(μ) ρ₂ <: ρ₄ ≲(μ) ρ₅ ⇝ F₁₂₄₅
notex for noelab Fₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A₃⟧). λ xᵣ : ⊗ (a$0 ⟦A₄⟧). F₂₅ₚ [a$0] ⦅⦅⦅π 0 xₑ$2⦆ [a$0] ⦅F₃₀ₚ [a$0] xₗ$1⦆⦆ ⦅F₄₁ₚ [a$0] xᵣ$0⦆⦆
notex for noelab Fₑᵢ := ⦅⦅⦅π 1 xₑ$3⦆ [a$1] [aₜ$0] ⦅λ xₗ' : ⊕ (a$1 ⟦A₀⟧). xₗ$3 ⦅F₀₃ₛ [a$1] xₗ'$0⦆⦆⦆ ⦅λ xᵣ' : ⊕ (a$1 ⟦A₁⟧). xᵣ$2 ⦅F₁₄ₛ [a$1] xᵣ'$0⦆⦆⦆ ⦅F₅₂ₛ [a$1] x$0⦆
notex for noelab Fₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A₃⟧)) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A₄⟧)) → aₜ$0 . λ x : ⊕ (a$1 ⟦A₅⟧). Fₑᵢ
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concat
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ <: ρ₃ ⊙(μ) ρ₄ ~ ρ₅ ⇝ λ xₑ : A. (Fₙ, Fₑ, F₀₂₃₅ ⦅π 2 xₑ$0⦆, F₁₂₄₅ ⦅π 3 xₑ$0⦆)

Γc; Γ ⊢ ρ₀ ≡(C) ρ₁ ⇝ Fₚ, Fₛ
Γc; Γ ⊢ All (λ a : κ. ψ) ρ₀ : C
notex for noelab ∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ B^a
notex for noelab ⊢ κ ⇝ K
──────────────────────────────────────────────────────────────────── all (I : List TypeVarId)
Γc; Γ ⊢ All (λ a : κ. ψ) ρ₀ <: All (λ a : κ. ψ) ρ₁ ⇝ Fₚ [λ a : K. B]

Γc; Γ ⊢ (Lift (λ a : κ. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ <: (Lift (λ a : κ. τ) ρ₃) ⊙(C) ρ₄ ~ ρ₅ ⇝ F
────────────────────────────────────────────────────────────────────────────────────── split
Γc; Γ ⊢ Split (λ a : κ. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ <: Split (λ a : κ. τ) ρ₃ ⊙' ρ₄ ~ ρ₅ ⇝ F

end TabularTypeInterpreter
