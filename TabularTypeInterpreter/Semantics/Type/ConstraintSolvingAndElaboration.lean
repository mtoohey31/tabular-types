import Lott.Elab.NotExistentialJudgement
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Semantics.InstanceEnvironment
import TabularTypeInterpreter.Semantics.Type.SubtypingAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»

-- TODO: Maybe try to simplify last remaining judgements which explicitly name irrelevant
-- elaborations (the remaining few in constraint solving and program typing are currently necessary
-- because we don't want the unnamed term to depend on the cofinitely quantified variables).

syntax (name := constraintSolving) Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment "; " Lott.Symbol.TabularTypeInterpreter.ClassEnvironment "; " Lott.Symbol.TabularTypeInterpreter.TypeEnvironment " ⊨ " Lott.Symbol.TabularTypeInterpreter.Monotype : Lott.Judgement

judgement_syntax Γᵢ "; " Γc "; " Γ " ⊨ " ψ " ⇝ " E : Monotype.ConstraintSolvingAndElaboration (tex := s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\lottsym\{;} \\, {Γ} \\, \\solvingsym \\, {ψ} \\, \\lottsym\{⇝} \\, {E}") (tex noelab := s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\lottsym\{;} \\, {Γ} \\, \\solvingsym \\, {ψ}")

macro_rules
  | `([[$Γᵢ:Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment; $Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment; $Γ:Lott.Symbol.TabularTypeInterpreter.TypeEnvironment ⊨ $ψ:Lott.Symbol.TabularTypeInterpreter.Monotype]]) =>
    `($(Lean.mkIdent `ConstraintSolvingAndElaboration) [[$(.mk Γᵢ):Lott.Symbol]] [[$(.mk Γc):Lott.Symbol]] [[$(.mk Γ):Lott.Symbol]] [[$(.mk ψ):Lott.Symbol]] _)

@[lott_tex_elab constraintSolving]
private
def constraintSolvingTexElab : Lott.TexElab := fun profile ref stx => do
  let `(constraintSolving| $Γᵢ:Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment; $Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment; $Γ:Lott.Symbol.TabularTypeInterpreter.TypeEnvironment ⊨ $ψ:Lott.Symbol.TabularTypeInterpreter.Monotype) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let Γᵢ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment profile ref Γᵢ
  let Γc ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.ClassEnvironment profile ref Γc
  let Γ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeEnvironment profile ref Γ
  let ψ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.Monotype profile ref ψ
  return s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\lottsym\{;} \\, {Γ} \\, \\solvingsym \\, {ψ}"

open TypeScheme

set_option maxHeartbeats 2000000 in
judgement Monotype.ConstraintSolvingAndElaboration where

ψ ⇝ x ∈ Γ
───────────────── «local»
Γᵢ; Γc; Γ ⊨ ψ ⇝ x

Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ) ρ₁ ⇝ E
Γᵢ; Γc; Γ ⊨ ρ₁ ≲(μ) ρ₂ ⇝ F
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₂⟧). ⦅π 0 E⦆ [a$0] ⦅π 0 F⦆ [a$0] x$0
notex for noelab Eᵢ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₀⟧). ⦅π 1 F⦆ [a$0] ⦅π 1 E⦆ [a$0] x$0
─────────────────────────────────────────────────────────────────────────────────────── containTrans
Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ) ρ₂ ⇝ (Eₚ, Eᵢ)

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ ⇝ E₂
Γᵢ; Γc; Γ ⊨ ρ₃ ⊙(μ) ρ₄ ~ ρ₅ ⇝ E₅
Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ) ρ₃ ⇝ Fₗ
Γᵢ; Γc; Γ ⊨ ρ₁ ≲(μ) ρ₄ ⇝ Fᵣ
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab Γc; Γ ⊢ ρ₅ : R κ ⇝ A₅
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₅⟧). ⦅⦅π 0 E₂⦆ [a$0] ⦅⦅π 0 Fₗ⦆ [a$0] ⦅⦅π 0 π 2 E₅⦆ [a$0] x$0⦆⦆⦆ ⦅⦅π 0 Fᵣ⦆ [a$0] ⦅⦅π 0 π 3 E₅⦆ [a$0] x$0⦆⦆
notex for noelab Eᵢ := Λ a : K ↦ *. ⦅⦅π 1 E₂⦆ [a$0] [⊕ (a$0 ⟦A₅⟧)] ⦅λ x : ⊕ (a$0 ⟦A₀⟧). ⦅π 1 π 2 E₅⦆ [a$0] ⦅⦅π 1 Fₗ⦆ [a$0] x$0⦆⦆⦆ ⦅λ x : ⊕ (a$0 ⟦A₁⟧). ⦅π 1 π 3 E₅⦆ [a$0] ⦅⦅π 1 Fᵣ⦆ [a$0] x$0⦆⦆
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── containConcat
Γᵢ; Γc; Γ ⊨ ρ₂ ≲(μ) ρ₅ ⇝ (Eₚ, Eᵢ)

notex for noelab Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:m] /> </ : κ // b₀ />⟩ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ⟨</ ξ'@j ▹ τ'@j // j in [:n] /> </ : κ // b₁ />⟩ : R κ ⇝ A₁
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:m] />, </ ξ'@j ▹ τ'@j // j in [:n] /> </ : κ // b₀ && b₁ />⟩ : R κ ⇝ A₂
notex for noelab ⊢ κ ⇝ K
notex for noelab </ Γc; Γ ⊢ τ@i : κ ⇝ B@i // i in [:m] />
notex for noelab </ Γc; Γ ⊢ τ'@j : κ ⇝ B'@j // j in [:n] />
notex for noelab Eₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A₀⟧). λ xᵣ : ⊗ (a$0 ⟦A₁⟧). (</ π i xₗ$1 // i in [:m] />, </ π j xᵣ$0 // j in [:n] />)
notex for noelab Eₑ' := case x$0 {</ λ x : a$1 B@i. xₗ$3 ⦅ι i x$0⦆ // i in [:m] />, </ λ x : a$1 B'@j. xᵣ$2 ⦅ι j x$0⦆ // j in [:n] />}
notex for noelab Eₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A₀⟧)) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A₁⟧)) → aₜ$0 . λ x : ⊕ (a$1 ⟦A₂⟧). Eₑ'
notex for noelab Eₚₗ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₂⟧). (</ π i x$0 // i in [:m] />)
notex for noelab Eᵢₗ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₀⟧). case x$0 {</ λ x : a$0 B@i. ι i x$0 // i in [:m] />}
notex for noelab Eₗ := (Eₚₗ, Eᵢₗ)
notex for noelab Eₚᵣ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₂⟧). (</ π (m + j) x$0 // j in [:n] />)
notex for noelab Eᵢᵣ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₁⟧). case x$0 {</ λ x : a$0 B'@j. ι (m + j) x$0 // j in [:n] />}
notex for noelab Eᵣ := (Eₚᵣ, Eᵢᵣ)
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concatConcrete
Γᵢ; Γc; Γ ⊨ ⟨</ ξ@i ▹ τ@i // i in [:m] /> </ : κ // b₀ />⟩ ⊙(N) ⟨</ ξ'@j ▹ τ'@j // j in [:n] /> </ : κ // b₁ />⟩ ~ ⟨</ ξ@i ▹ τ@i // i in [:m] />, </ ξ'@j ▹ τ'@j // j in [:n] /> </ : κ // b₀ && b₁ />⟩ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

Γc; Γ ⊢ ρ : R κ ⇝ A
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₙ := Λ a : K ↦ *. λ xₗ : ⊗ { }. λ xᵣ : ⊗ (a$0 ⟦A⟧). xᵣ$0
notex for noelab Eₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ { }) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A⟧)) → aₜ$0 . xᵣ$0
notex for noelab Eₗ := (Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). (), Λ a : K ↦ *. λ x : ⊕ { }. case x$0 { })
notex for noelab Eᵣ := (Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0)
──────────────────────────────────────────────────────────────────────────────────────────────────────── concatEmptyL
Γᵢ; Γc; Γ ⊨ ⟨ : κ ⟩ ⊙(N) ρ ~ ρ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

Γc; Γ ⊢ ρ : R κ ⇝ A
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A⟧). λ xᵣ : ⊗ { }. xₗ$1
notex for noelab Eₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A⟧)) → aₜ$0 . λ xᵣ : (⊕ { }) → aₜ$0 . xₗ$1
notex for noelab Eₗ := (Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). x$0, Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A⟧). x$0)
notex for noelab Eᵣ := (Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A⟧). (), Λ a : K ↦ *. λ x : ⊕ { }. case x$0 { })
──────────────────────────────────────────────────────────────────────────────────────────────────────── concatEmptyR
Γᵢ; Γc; Γ ⊨ ρ ⊙(N) ⟨ : κ ⟩ ~ ρ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₃ ⇝ E₀₁
Γᵢ; Γc; Γ ⊨ ρ₁ ⊙(μ) ρ₂ ~ ρ₄ ⇝ E₁₂
Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₄ ~ ρ₅ ⇝ E₀₄
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab Γc; Γ ⊢ ρ₃ : R κ ⇝ A₃
notex for noelab Γc; Γ ⊢ ρ₅ : R κ ⇝ A₅
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₙᵣ := ⦅⦅π 0 E₁₂⦆ [a$0] ⦅⦅π 0 π 3 E₀₁⦆ [a$0] xₗ$1⦆⦆ xᵣ$0
notex for noelab Eₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A₃⟧). λ xᵣ : ⊗ (a$0 ⟦A₂⟧). ⦅⦅π 0 E₀₄⦆ [a$0] ⦅⦅π 0 π 2 E₀₁⦆ [a$0] xₗ$1⦆⦆ Eₙᵣ
notex for noelab Eₑᵣ' := ⦅⦅π 1 E₁₂⦆ [a$1] [aₜ$0] ⦅λ x : ⊕ (a$1 ⟦A₁⟧). xₗ$2 ⦅⦅π 1 π 3 E₀₁⦆ [a$1] x$0⦆⦆⦆ xᵣ$0
notex for noelab Eₑ' := ⦅⦅π 1 E₀₄⦆ [a$1] [aₜ$0] ⦅λ x : ⊕ (a$1 ⟦A₀⟧). xₗ$2 ⦅⦅π 1 π 2 E₀₁⦆ [a$1] x$0⦆⦆⦆ Eₑᵣ'
notex for noelab Eₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A₃⟧)) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A₂⟧)) → aₜ$0 . Eₑ'
notex for noelab Eₚₗ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₅⟧). ⦅⦅π 0 E₀₁⦆ [a$0] ⦅⦅π 0 π 2 E₀₄⦆ [a$0] x$0⦆⦆ ⦅⦅π 0 π 2 E₁₂⦆ [a$0] ⦅π 0 π 3 E₀₄⦆ [a$0] x$0⦆
notex for noelab Eᵢₗᵣ := λ x' : ⊕ (a$0 ⟦A₁⟧). ⦅π 1 π 3 E₀₄⦆ [a$0] ⦅⦅π 1 π 2 E₁₂⦆ [a$0] x'$0⦆
notex for noelab Eᵢₗ := Λ a : K ↦ *. ⦅⦅π 1 E₀₁⦆ [a$0] [⊕ (a$0 ⟦A₅⟧)] ⦅⦅π 1 π 2 E₀₄⦆ [a$0]⦆⦆ Eᵢₗᵣ
notex for noelab Eₗ := (Eₚₗ, Eᵢₗ)
notex for noelab Eₚᵣ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₅⟧). ⦅π 0 π 3 E₁₂⦆ [a$0] ⦅π 0 π 3 E₀₄⦆ [a$0] x$0
notex for noelab Eᵢᵣ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₂⟧). ⦅π 1 π 3 E₀₄⦆ [a$0] ⦅π 1 π 3 E₁₂⦆ [a$0] x$0
notex for noelab Eᵣ := (Eₚᵣ, Eᵢᵣ)
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concatAssocL
Γᵢ; Γc; Γ ⊨ ρ₃ ⊙(μ) ρ₂ ~ ρ₅ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₃ ⇝ E₀₁
Γᵢ; Γc; Γ ⊨ ρ₁ ⊙(μ) ρ₂ ~ ρ₄ ⇝ E₁₂
Γᵢ; Γc; Γ ⊨ ρ₃ ⊙(μ) ρ₂ ~ ρ₅ ⇝ E₃₂
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
notex for noelab Γc; Γ ⊢ ρ₄ : R κ ⇝ A₄
notex for noelab Γc; Γ ⊢ ρ₅ : R κ ⇝ A₅
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₙₗ := ⦅⦅π 0 E₀₁⦆ [a$0] xₗ$1⦆ ⦅⦅π 0 π 2 E₁₂⦆ [a$0] xᵣ$0⦆
notex for noelab Eₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A₀⟧). λ xᵣ : ⊗ (a$0 ⟦A₄⟧). ⦅⦅π 0 E₃₂⦆ [a$0] Eₙₗ⦆ ⦅⦅π 0 π 3 E₁₂⦆ [a$0] xᵣ$0⦆
notex for noelab Eₑₗ' := ⦅⦅π 1 E₀₁⦆ [a$1] [aₜ$0] xₗ$1⦆ ⦅λ x : ⊕ (a$1 ⟦A₁⟧). xᵣ$1 ⦅⦅π 1 π 2 E₁₂⦆ [a$1] x$0⦆⦆
notex for noelab Eₑ' := ⦅⦅π 1 E₃₂⦆ [a$1] [aₜ$0] Eₑₗ'⦆ ⦅λ x : ⊕ (a$1 ⟦A₂⟧). xᵣ$1 ⦅⦅π 1 π 3 E₁₂⦆ [a$1] x$0⦆⦆
notex for noelab Eₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A₀⟧)) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A₄⟧)) → aₜ$0 . Eₑ'
notex for noelab Eₗₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₅⟧). ⦅π 0 π 2 E₀₁⦆ [a$0] ⦅π 0 π 2 E₃₂⦆ [a$0] x$0
notex for noelab Eₗᵢ := Λ a : K ↦ *. λ x : ⊕ (a$0 ⟦A₀⟧). ⦅π 1 π 2 E₃₂⦆ [a$0] ⦅π 1 π 2 E₀₁⦆ [a$0] x$0
notex for noelab Eₗ := (Eₗₚ, Eₗᵢ)
notex for noelab Eᵣₚ := Λ a : K ↦ *. λ x : ⊗ (a$0 ⟦A₅⟧). ⦅⦅π 0 E₁₂⦆ [a$0] ⦅⦅π 0 π 3 E₀₁⦆ [a$0] ⦅π 0 π 2 E₃₂⦆ [a$0] x$0⦆⦆ ⦅⦅π 0 π 3 E₃₂⦆ [a$0] x$0⦆
notex for noelab Eᵣᵢₗ := λ x' : ⊕ (a$0 ⟦A₁⟧). ⦅π 1 π 2 E₃₂⦆ [a$0] ⦅⦅π 1 π 3 E₀₁⦆ [a$0] x'$0⦆
notex for noelab Eᵣᵢ := Λ a : K ↦ *. ⦅⦅⦅π 1 E₁₂⦆ [a$0] [⊕ (a$0 ⟦A₅⟧)] Eᵣᵢₗ⦆ ⦅⦅π 1 π 3 E₃₂⦆ [a$0]⦆⦆
notex for noelab Eᵣ := (Eᵣₚ, Eᵣᵢ)
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concatAssocR
Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₄ ~ ρ₅ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(C) ρ₁ ~ ρ₂ ⇝ E
notex for noelab Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
notex for noelab Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
notex for noelab ⊢ κ ⇝ K
notex for noelab Eₙ := Λ a : K ↦ *. λ xₗ : ⊗ (a$0 ⟦A₁⟧). λ xᵣ : ⊗ (a$0 ⟦A₀⟧). ⦅⦅π 0 E⦆ [a$0] xᵣ$0⦆ xₗ$1
notex for noelab Eₑ := Λ a : K ↦ *. Λ aₜ : *. λ xₗ : (⊕ (a$1 ⟦A₁⟧)) → aₜ$0 . λ xᵣ : (⊕ (a$1 ⟦A₀⟧)) → aₜ$0 . ⦅⦅π 1 E⦆ [a$1] [aₜ$0] xᵣ$0⦆ xₗ$1
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concatSwap
Γᵢ; Γc; Γ ⊨ ρ₁ ⊙(C) ρ₀ ~ ρ₂ ⇝ (Eₙ, Eₑ, π 3 E, π 2 E)

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ ⇝ E
─────────────────────────────── concatContainL
Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ) ρ₂ ⇝ π 2 E

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ ⇝ E
─────────────────────────────── concatContainR
Γᵢ; Γc; Γ ⊨ ρ₁ ≲(μ) ρ₂ ⇝ π 3 E

Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ₀) ρ₁ ⇝ E
μ₀ ≤ μ₁
Γc; Γ ⊢ μ₁ : U
─────────────────────────── containDecay
Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ₁) ρ₁ ⇝ E

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ₀) ρ₁ ~ ρ₂ ⇝ E
μ₀ ≤ μ₁
Γc; Γ ⊢ μ₁ : U
──────────────────────────────── concatDecay
Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ₁) ρ₁ ~ ρ₂ ⇝ E

Γᵢ; Γc; Γ ⊨ ρ₀ ≲(μ) ρ₁ ⇝ E
Γc; Γ ⊢ ρ₀ : R κ₀
∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ τ^a : κ₁ ⇝ A^a
notex for noelab ⊢ κ₀ ⇝ K₀
notex for noelab ⊢ κ₁ ⇝ K₁
notex for noelab Eₚ := Λ a' : K₁ ↦ *. ⦅π 0 E⦆ [λ a : K₀. a'$1 A]
notex for noelab Eᵢ := Λ a' : K₁ ↦ *. ⦅π 1 E⦆ [λ a : K₀. a'$1 A]
─────────────────────────────────────────────────────────────────────────── liftContain (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ (Lift (λ a : κ₀. τ) ρ₀) ≲(μ) (Lift (λ a : κ₀. τ) ρ₁) ⇝ (Eₚ, Eᵢ)

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ ⇝ E
Γc; Γ ⊢ ρ₀ : R κ₀
∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ τ^a : κ₁ ⇝ A^a
notex for noelab ⊢ κ₀ ⇝ K₀
notex for noelab ⊢ κ₁ ⇝ K₁
notex for noelab Eₙ := Λ a' : K₁ ↦ *. ⦅π 0 E⦆ [λ a : K₀. a'$1 A]
notex for noelab Eₑ := Λ a' : K₁ ↦ *. ⦅π 1 E⦆ [λ a : K₀. a'$1 A]
notex for noelab Eₗ := (Λ a' : K₁ ↦ *. ⦅π 0 π 2 E⦆ [λ a : K₀. a'$1 A], Λ a' : K₁ ↦ *. ⦅π 1 π 2 E⦆ [λ a : K₀. a'$1 A])
notex for noelab Eᵣ := (Λ a' : K₁ ↦ *. ⦅π 0 π 3 E⦆ [λ a : K₀. a'$1 A], Λ a' : K₁ ↦ *. ⦅π 1 π 3 E⦆ [λ a : K₀. a'$1 A])
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────── liftConcat (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ (Lift (λ a : κ₀. τ) ρ₀) ⊙(μ) (Lift (λ a : κ₀. τ) ρ₁) ~ (Lift (λ a : κ₀. τ) ρ₂) ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

(∀ </ a@k : κ@k // k in [:o] notex />. </ ψ@j ⇝ x@j // j in [:l] notex /> ⇒ TC τ) ⇝ E; </ E'@i // i in [:n] notex /> ∈ Γᵢ
</ Γc; Γ ⊢ τ'@k : κ@k ⇝ B@k // k in [:o] notex />
</ Γᵢ; Γc; Γ ⊨ ψ@j^^^^τ'@@k#o/a ⇝ F@j // j in [:l] notex />
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── TCInst {TC}
Γᵢ; Γc; Γ ⊨ TC τ^^^^τ'@@k#o/a ⇝ (E^^^^B@@k#o/a^^^^F@@j#l/x, </ E'@i^^^^B@@k#o/a^^^^F@@j#l/x // i in [:n] notex />)

(</ TC'@j a ⇝ A'@j // j in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
Γᵢ; Γc; Γ ⊨ TC τ ⇝ E
i ∈ [:n]
─────────────────────────────────────────────────────────────── TCSuper {TC}
Γᵢ; Γc; Γ ⊨ TC'@i τ ⇝ π (1 + i) E

∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
───────────────────────────────────────── allEmpty (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ⟨ : κ ⟩ ⇝ ()

Γᵢ; Γc; Γ ⊨ ψ^^τ/a ⇝ E
∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
Γc; Γ ⊢ ξ : L
Γc; Γ ⊢ τ : κ
────────────────────────────────────────── allSingletonIntro (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ⟨ξ ▹ τ⟩ ⇝ (E)

Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ⟨ξ ▹ τ⟩ ⇝ E
──────────────────────────────────────── allSingletonElim
Γᵢ; Γc; Γ ⊨ ψ^^τ/a ⇝ π 0 E

Γᵢ; Γc; Γ ⊨ ρ₀ ≲(C) ρ₁ ⇝ F
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ρ₁ ⇝ E
notex for noelab ∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
notex for noelab ⊢ κ ⇝ K
──────────────────────────────────────────────────────── allContain (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ρ₀ ⇝ ⦅π 0 F⦆ [λ a : K. A] E

Γᵢ; Γc; Γ ⊨ ρ₀ ⊙(C) ρ₁ ~ ρ₂ ⇝ F
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ρ₀ ⇝ E₀
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ρ₁ ⇝ E₁
notex for noelab ∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
notex for noelab ⊢ κ ⇝ K
────────────────────────────────────────────────────────────── allConcat (I  : List TypeVarId)
Γᵢ; Γc; Γ ⊨ All (λ a : κ. ψ) ρ₂ ⇝ ⦅⦅π 0 F⦆ [λ a : K. A] E₀⦆ E₁

-- TODO: Mention that indConcat and such were omitted since it would require total type list concat
-- in the target and should become obsolete after future work figures out how to deal with
-- constraint totality properly.

</ Γc; Γ ⊢ τ@i : κ ⇝ A@i // i in [:n] />
notex for noelab ⊢ κ ⇝ K
notex for noelab ∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, Γc; Γ, aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ ⊢ aₚ ⊙(N) ⟨aₗ ▹ aₜ⟩ ~ aᵢ : C ⇝ Bₗ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1
notex for noelab ∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, Γc; Γ, aᵢ : R κ, aₙ : R κ ⊢ aᵢ ⊙(N) aₙ ~ ⟨</ ℓ@i ▹ τ@i // i in [:n] /> </ : κ // b />⟩ : C ⇝ Bᵣ^aᵢ#1^aₙ
notex for noelab Aₛ := ∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bₗ → Bᵣ → (⊗ { }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1
</ Γᵢ; Γc; Γ ⊨ ⟨</ ℓ@j ▹ τ@j // j in [:i] /> : κ⟩ ⊙(N) ⟨ℓ@i ▹ τ@i⟩ ~ ⟨</ ℓ@k ▹ τ@k // k in [:i+1] />⟩ ⇝ E@i // i in [:n] />
</ Γᵢ; Γc; Γ ⊨ ⟨</ ℓ@j ▹ τ@j // j in [:i+1] />⟩ ⊙(N) ⟨</ ℓ@k ▹ τ@k // k in [i+1:n] /> : κ⟩ ~ ⟨</ ℓ@l ▹ τ@l // l in [:n] /> </ : κ // b />⟩ ⇝ E'@i // i in [:n] />
notex for noelab E' := ! </ ⦅⦅xₛ$1 [⊗ { }] [A@i] [{</ A@j // j in [:i] />}] [{</ A@k // k in [:i+1] />}] [{</ A@l // l in [i+1:n] />}] E@i⦆ E'@i⦆ () // i in [:n] /> xᵢ$0
notex for noelab E := Λ aₘ : (L K) ↦ *. λ xₛ : Aₛ. λ xᵢ : aₘ$0 { }. E'
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ind (comment := "where the comprehension in $\\targetpre E' \\targetpost$ is repeated application") (comment noelab) (I₀ I₁ : List TypeVarId)
Γᵢ; Γc; Γ ⊨ Ind ⟨</ ℓ@i ▹ τ@i // i in [:n] /> </ : κ // b />⟩ ⇝ E

∀ a ∉ I, Γc; Γ, a : κ ⊢ τ^a : * ⇝ A^a
notex for noelab Eₙ := Λ a' : * ↦ *. λ xₗ : ⊗ { }. λ xᵣ : ⊗ { }. ()
notex for noelab Eₑ := Λ a' : * ↦ *. Λ aₜ : *. λ xₗ : (⊕ { }) → aₜ$0 . λ xᵣ : (⊕ { }) → aₜ$0 . xᵣ$0
notex for noelab Eₗᵣ := (Λ a' : * ↦ *. λ x : ⊗ { }. (), Λ a' : * ↦ *. λ x : ⊕ { }. x$0)
─────────────────────────────────────────────────────────────────────────────────────────────────── splitEmpty (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ) ⟨ : κ ⟩ ⊙' ⟨ : * ⟩ ~ ⟨ : * ⟩ ⇝ (Eₙ, Eₑ, Eₗᵣ, Eₗᵣ)

-- TODO: Talk about subtyping considerations in the paper.

∀ a ∉ I, Γc; Γ, a : κ ⊢ τ₀^a : * ⇝ A^a
Γc; Γ ⊢ τ₁ : κ ⇝ B
Γc; Γ ⊢ ξ : L
notex for noelab Eₙ := Λ a' : * ↦ *. λ xₗ : ⊗ {a'$0 A^^B/a}. λ xᵣ : ⊗ { }. xₗ$1
notex for noelab Eₑ := Λ a' : * ↦ *. Λ aₜ : *. λ xₗ : (⊕ {a'$1 A^^B/a}) → aₜ$0 . λ xᵣ : (⊕ { }) → aₜ$0 . xₗ$1
notex for noelab Eₗ := (Λ a' : * ↦ *. λ x : ⊗ {a'$0 A^^B/a}. x$0, Λ a' : * ↦ *. λ x : ⊕ {a'$0 A^^B/a}. x$0)
notex for noelab Eᵣ := (Λ a' : * ↦ *. λ x : ⊗ {a'$0 A^^B/a}. (), Λ a' : * ↦ *. λ x : ⊕ { }. case x$0 { })
───────────────────────────────────────────────────────────────────────────────────────────────────────────── splitSingletonMatch (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ₀) ⟨ξ ▹ τ₁⟩ ⊙' ⟨ : * ⟩ ~ ⟨ξ ▹ τ₀^^τ₁/a⟩ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

∄ τ₂ F, Γc; Γ ⊢ τ₁ <: τ₀^^τ₂/a ⇝ F
∀ a ∉ I, Γc; Γ, a : κ ⊢ τ₀^a : * ⇝ A^a
Γc; Γ ⊢ τ₁ : * ⇝ B
Γc; Γ ⊢ ξ : L
notex for noelab Eₙ := Λ a' : * ↦ *. λ xₗ : ⊗ { }. λ xᵣ : ⊗ {a'$0 B}. xᵣ$0
notex for noelab Eₑ := Λ a' : * ↦ *. Λ aₜ : *. λ xₗ : (⊕ { }) → aₜ$0 . λ xᵣ : (⊕ {a'$1 B}) → aₜ$0 . xᵣ$0
notex for noelab Eₗ := (Λ a' : * ↦ *. λ x : ⊗ {a'$0 B}. (), Λ a' : * ↦ *. λ x : ⊕ { }. case x$0 { })
notex for noelab Eᵣ := (Λ a' : * ↦ *. λ x : ⊗ {a'$0 B}. x$0, Λ a' : * ↦ *. λ x : ⊕ {a'$0 B}. x$0)
──────────────────────────────────────────────────────────────────────────────────────────────────────── splitSingletonRest (I : List TypeVarId)
Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ₀) ⟨ : κ ⟩ ⊙' ⟨ξ ▹ τ₁⟩ ~ ⟨ξ ▹ τ₁⟩ ⇝ (Eₙ, Eₑ, Eₗ, Eᵣ)

Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ) ρ₀ ⊙' ρ₁ ~ ρ₂
Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ) ρ₃ ⊙' ρ₄ ~ ρ₅
Γᵢ; Γc; Γ ⊨ (Lift (λ a : κ. τ) ρ₀) ⊙(C) (Lift (λ a : κ. τ) ρ₃) ~ (Lift (λ a : κ. τ) ρ₆)
Γᵢ; Γc; Γ ⊨ ρ₁ ⊙(C) ρ₄ ~ ρ₇
Γᵢ; Γc; Γ ⊨ ρ₂ ⊙(C) ρ₅ ~ ρ₈
notex for noelab Γᵢ; Γc; Γ ⊨ (Lift (λ a : κ. τ) ρ₆) ⊙(C) ρ₇ ~ ρ₈ ⇝ E
──────────────────────────────────────────────────────────────────────────────────────────── splitPiecewise
Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ) ρ₆ ⊙' ρ₇ ~ ρ₈ ⇝ E

Γᵢ; Γc; Γ ⊨ Split (λ a : κ. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ ⇝ E
─────────────────────────────────────────────────── splitConcat
Γᵢ; Γc; Γ ⊨ (Lift (λ a : κ. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ ⇝ E

end TabularTypeInterpreter
