import TabularTypes.Semantics.Type
import TabularTypes.Syntax.Term

namespace TabularTypes

termonly
def Term.TypeVar_multi_open (M : Term) (a : Nat → TypeVarId) : Nat → Term
  | 0 => M
  | n + 1 => M.TypeVar_open (a n) n |>.TypeVar_multi_open a n

termonly
def Term.TermVar_multi_open (M : Term) (x : Nat → TermVarId) : Nat → Term
  | 0 => M
  | n + 1 => M.TermVar_open (x n) n |>.TermVar_multi_open x n

open «F⊗⊕ω»

abbrev ℓₘ := 0

abbrev ℓᵣ := 1

syntax (name := typing) Lott.Symbol.TabularTypes.InstanceEnvironment "; " Lott.Symbol.TabularTypes.ClassEnvironment "; " Lott.Symbol.TabularTypes.TypeEnvironment " ⊢ " Lott.Symbol.TabularTypes.Term " : " Lott.Symbol.TabularTypes.TypeScheme : Lott.Judgement

judgement_syntax Γᵢ "; " Γc "; " Γ " ⊢ " M " : " σ " ⇝ " E : Term.TypingAndElaboration (tex := s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {M} \\, \\typingsym \\, {σ} \\, \\lottsym\{⇝} \\, {E}") (tex noelab := s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {M} \\, \\typingsym \\, {σ}")

macro_rules
  | `([[$Γᵢ:Lott.Symbol.TabularTypes.InstanceEnvironment; $Γc:Lott.Symbol.TabularTypes.ClassEnvironment; $Γ:Lott.Symbol.TabularTypes.TypeEnvironment ⊢ $M:Lott.Symbol.TabularTypes.Term : $σ:Lott.Symbol.TabularTypes.TypeScheme]]) =>
    `($(Lean.mkIdent `TypingAndElaboration) [[$(.mk Γᵢ):Lott.Symbol]] [[$(.mk Γc):Lott.Symbol]] [[$(.mk Γ):Lott.Symbol]] [[$(.mk M):Lott.Symbol]] [[$(.mk σ):Lott.Symbol]] _)

@[lott_tex_elab typing]
private
def typingTexElab : Lott.TexElab := fun profile ref stx => do
  let `(typing| $Γᵢ:Lott.Symbol.TabularTypes.InstanceEnvironment; $Γc:Lott.Symbol.TabularTypes.ClassEnvironment; $Γ:Lott.Symbol.TabularTypes.TypeEnvironment ⊢ $M:Lott.Symbol.TabularTypes.Term : $σ:Lott.Symbol.TabularTypes.TypeScheme) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let Γᵢ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.InstanceEnvironment profile ref Γᵢ
  let Γc ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.ClassEnvironment profile ref Γc
  let Γ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.TypeEnvironment profile ref Γ
  let M ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.Term profile ref M
  let σ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypes.TypeScheme profile ref σ
  return s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\lottsym\{;} \\, {Γ} \\, \\lottsym\{⊢} \\, {M} \\, \\typingsym \\, {σ}"

open TypeScheme

judgement Term.TypingAndElaboration where

x : σ ∈ Γ
───────────────────── var
Γᵢ; Γc; Γ ⊢ x : σ ⇝ x

∀ x ∉ I, Γᵢ; Γc; Γ, x : τ₀ ⊢ M^x : τ₁ ⇝ E^x
Γc; Γ ⊢ τ₀ : * ⇝ A
─────────────────────────────────────────── lam (I : List TermVarId)
Γᵢ; Γc; Γ ⊢ λ x. M : τ₀ → τ₁ ⇝ λ x : A. E

Γᵢ; Γc; Γ ⊢ M : τ₀ → τ₁ ⇝ F
Γᵢ; Γc; Γ ⊢ «N» : τ₀ ⇝ E
──────────────────────────── app
Γᵢ; Γc; Γ ⊢ M «N» : τ₁ ⇝ F E

Γc; Γ ⊢ ψ : C ⇝ A
∀ x ∉ I, Γᵢ; Γc; Γ, ψ ⇝ x ⊢ M^x : γ ⇝ E^x
───────────────────────────────────────── qualI (I : List TermVarId)
Γᵢ; Γc; Γ ⊢ M : ψ ⇒ γ ⇝ λ x : A. E

Γᵢ; Γc; Γ ⊨ ψ ⇝ E
Γᵢ; Γc; Γ ⊢ M : ψ ⇒ γ ⇝ F
───────────────────────── qualE
Γᵢ; Γc; Γ ⊢ M : γ ⇝ F E

∀ a ∉ I, Γᵢ; Γc; Γ, a : κ ⊢ M^a : σ^a ⇝ E^a
elab_related ⊢ κ ⇝ K
─────────────────────────────────────────── schemeI (I : List TypeVarId)
Γᵢ; Γc; Γ ⊢ M : ∀ a : κ. σ ⇝ Λ a : K. E

Γᵢ; Γc; Γ ⊢ M : ∀ a : κ. σ ⇝ E
Γc; Γ ⊢ τ : κ ⇝ A
────────────────────────────── schemeE
Γᵢ; Γc; Γ ⊢ M : σ^^τ/a ⇝ E [A]

Γᵢ; Γc; Γ ⊢ M : σ₀ ⇝ E
Γc; Γ ⊢ σ₀ : * ⇝ A
∀ x ∉ I, Γᵢ; Γc; Γ, x : σ₀ ⊢ «N»^x : σ₁ ⇝ F^x
─────────────────────────────────────────────────────── «let» (I : List TermVarId)
Γᵢ; Γc; Γ ⊢ let x : σ₀ = M in «N» : σ₁ ⇝ ⦅λ x : A. F⦆ E

Γᵢ; Γc; Γ ⊢ M : σ ⇝ E
────────────────────────── annot
Γᵢ; Γc; Γ ⊢ M :' σ : σ ⇝ E

──────────────────────── label
Γᵢ; Γc; Γ ⊢ ℓ : ⌊ℓ⌋ ⇝ ()

Γᵢ; Γc; Γ ⊢ M : ⌊ξ⌋
Γᵢ; Γc; Γ ⊢ «N» : τ ⇝ E
────────────────────────────────────────── prod
Γᵢ; Γc; Γ ⊢ {M ▹ «N»} : Π(N) ⟨ξ ▹ τ⟩ ⇝ (E)

Γᵢ; Γc; Γ ⊢ M : ⌊ξ⌋
Γᵢ; Γc; Γ ⊢ «N» : τ ⇝ E
──────────────────────────────────────────── sum
Γᵢ; Γc; Γ ⊢ [M ▹ «N»] : Σ(N) ⟨ξ ▹ τ⟩ ⇝ ι 0 E

Γᵢ; Γc; Γ ⊢ M : Π(C) ⟨ξ ▹ τ⟩ ⇝ E
Γᵢ; Γc; Γ ⊢ «N» : ⌊ξ⌋
──────────────────────────────── unlabelProd
Γᵢ; Γc; Γ ⊢ M/«N» : τ ⇝ π 0 E

Γᵢ; Γc; Γ ⊢ M : Σ(C) ⟨ξ ▹ τ⟩ ⇝ E
Γᵢ; Γc; Γ ⊢ «N» : ⌊ξ⌋
elab_related Γc; Γ ⊢ τ : * ⇝ A
───────────────────────────────────────────── unlabelSum
Γᵢ; Γc; Γ ⊢ M/«N» : τ ⇝ case E {λ x : A. x$0}

Γᵢ; Γc; Γ ⊢ M : Π(μ) ρ₀ ⇝ E
Γᵢ; Γc; Γ ⊨ ρ₁ ≲(μ) ρ₀ ⇝ F
────────────────────────────────────────────────────── «prj»
Γᵢ; Γc; Γ ⊢ prj M : Π(μ) ρ₁ ⇝ ⦅π 0 F⦆ [λ a : *. a$0] E

Γᵢ; Γc; Γ ⊢ M : Π(μ) ρ₀ ⇝ E₀
Γᵢ; Γc; Γ ⊢ «N» : Π(μ) ρ₁ ⇝ E₁
Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ ⇝ F
─────────────────────────────────────────────────────────────── concat
Γᵢ; Γc; Γ ⊢ M ++ «N» : Π(μ) ρ₂ ⇝ ⦅⦅π 0 F⦆ [λ a : *. a$0] E₀⦆ E₁

Γᵢ; Γc; Γ ⊢ M : Σ(μ) ρ₀ ⇝ E
Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ) ρ₁ ⇝ F
────────────────────────────────────────────────────── «inj»
Γᵢ; Γc; Γ ⊢ inj M : Σ(μ) ρ₁ ⇝ ⦅π 1 F⦆ [λ a : *. a$0] E

Γᵢ; Γc; Γ ⊢ M : (Σ(μ) ρ₀) → τ ⇝ E₀
Γᵢ; Γc; Γ ⊢ «N» : (Σ(μ) ρ₁) → τ ⇝ E₁
Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ ⇝ F
Γc; Γ ⊢ τ : * ⇝ A
──────────────────────────────────────────────────────────────────────── elim
Γᵢ; Γc; Γ ⊢ M ▿ «N» : (Σ(μ) ρ₂) → τ ⇝ ⦅⦅π 1 F⦆ [λ a : *. a$0] [A] E₀⦆ E₁

Γᵢ; Γc; Γ ⊢ M : σ₀ ⇝ E
Γc; Γ ⊢ σ₀ <: σ₁ ⇝ F
──────────────────────── sub
Γᵢ; Γc; Γ ⊢ M : σ₁ ⇝ F E

(</ TC'@i a ⇝ A'@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
Γᵢ; Γc; Γ ⊨ TC τ ⇝ E
───────────────────────────────────────────────────────────────────── method {TC}
Γᵢ; Γc; Γ ⊢ m : σ^^τ/a ⇝ π 0 E

Γc; Γ ⊢ ρ : R κ
∀ a ∉ Iₘ, Γc; Γ, a : R κ ⊢ τ^a : * ⇝ A^a
∀ aₗ ∉ Iₛ, ∀ aₜ ∉ aₗ :: Iₛ, ∀ aₚ ∉ aₜ :: aₗ :: Iₛ, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: Iₛ, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: Iₛ, Γᵢ; Γc; Γ, aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ, aₙ : R κ ⊢ M : aₚ ⊙(N) ⟨aₗ ▹ aₜ⟩ ~ aᵢ ⇒ aᵢ ⊙(N) aₙ ~ ρ ⇒ ⌊aₗ⌋ → τ^aₚ/a → τ^aᵢ/a ⇝ E₀^aₗ#4^aₜ#3^aₚ#2^aᵢ#1^aₙ
Γᵢ; Γc; Γ ⊢ «N» : τ^^⟨ : κ ⟩/a ⇝ E₁
elab_related ⊢ κ ⇝ K
elab_related Γᵢ; Γc; Γ ⊨ Ind ρ ⇝ F
E := ⦅F [λ a : L K. A] ⦅Λ aₗ : *. Λ aₜ : K. Λ aₚ : L K. Λ aᵢ : L K. Λ aₙ : L K. E₀⦆⦆ E₁
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── «ind» (Iₘ Iₛ : List TypeVarId)
Γᵢ; Γc; Γ ⊢ ind (λ a : R κ. τ) ρ; M; «N» : τ^^ρ/a ⇝ E

end TabularTypes
