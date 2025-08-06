import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Syntax.Program

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax Γᵢ "; " Γc " ⊢ " pgm " : " σ " ⇝ " E : Program.TypingAndElaboration (tex := s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\, \\lottsym\{⊢} \\, {pgm} \\, \\pgmtypingsym \\, {σ} \\, \\lottsym\{⇝} \\, {E}") (tex noelab := s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\, \\lottsym\{⊢} \\, {pgm} \\, \\pgmtypingsym \\, {σ}")

judgement Program.TypingAndElaboration where

</ TC'@i : κ ⇝ A'@i ∈ Γc // i in [:n] notex />
TC ∉ dom(Γc)
m ∉ dom(Γc)
∀ a, Γc; ε, a : κ ⊢ σ₀^a : * ⇝ A^a
Γᵢ; Γc, (</ TC'@i a ⇝ A'@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ₀ ⇝ A ⊢ pgm : σ₁ ⇝ E
──────────────────────────────────────────────────────────────────────────────────────── cls {TC}
Γᵢ; Γc ⊢ class </ TC'@i a // i in [:n] notex /> ⇒ TC a : κ where {m : σ₀}; pgm : σ₁ ⇝ E

(</ TC'@i a' ⇝ A'@i // i in [:n] notex /> ⇒ TC a' : κ) ↦ m : σ₀ ⇝ A ∈ Γc
</ ∀ a : { a : Nat → TypeVarId // a.Injective' }, Γc; ε,, </ a@k : κ'@k // k in [:o] notex /> ⊢ ψ@j^^^a#o : C ⇝ B@j^^^a#o // j in [:l] notex />
</ ∀ a : { a : Nat → TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, Γᵢ; Γc; ε,, </ a@k : κ'@k // k in [:o] notex />,,, </ ψ@j^^^a#o ⇝ x@j // j in [:l] notex /> ⊨ TC'@i τ^^^a#o ⇝ E'@i^^^x#l^^^a#o // i in [:n] notex />
∀ a : { a : Nat → TypeVarId // a.Injective' }, Γc; ε,, </ a@k : κ'@k // k in [:o] notex /> ⊢ τ^^^a#o : κ ⇝ B'^^^a#o
∀ a : { a : Nat → TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, Γᵢ; Γc; ε,, </ a@k : κ'@k // k in [:o] notex />,,, </ ψ@j^^^a#o ⇝ x@j // j in [:l] notex /> ⊢ M^^^x#l^^^a#o : σ₀^^⦅τ^^^a#o⦆/a' ⇝ E^^^x#l^^^a#o
Γᵢ, (∀ </ a@k : κ'@k // k in [:o] notex />. </ ψ@j ⇝ x@j // j in [:l] notex /> ⇒ TC τ) ⇝ E; </ E'@i // i in [:n] notex />; Γc ⊢ pgm : σ₁ ⇝ F
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── inst {TC}
Γᵢ; Γc ⊢ instance </ ψ@j // j in [:l] notex /> ⇒ TC τ where {m = M}; pgm : σ₁ ⇝ F

Γᵢ; Γc; ε ⊢ M : σ ⇝ E
───────────────────── term
Γᵢ; Γc ⊢ M : σ ⇝ E

syntax (name := pgmTyping) Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment "; " Lott.Symbol.TabularTypeInterpreter.ClassEnvironment " ⊢ " Lott.Symbol.TabularTypeInterpreter.Program " : " Lott.Symbol.TabularTypeInterpreter.TypeScheme : Lott.Judgement

macro_rules
  | `([[$Γᵢ:Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment; $Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment ⊢ $pgm:Lott.Symbol.TabularTypeInterpreter.Program : $σ:Lott.Symbol.TabularTypeInterpreter.TypeScheme]]) =>
    `(Program.TypingAndElaboration [[$(.mk Γᵢ):Lott.Symbol]] [[$(.mk Γc):Lott.Symbol]] [[$(.mk pgm):Lott.Symbol]] [[$(.mk σ):Lott.Symbol]] _)

@[lott_tex_elab pgmTyping]
private
def pgmTypingTexElab : Lott.TexElab := fun profile ref stx => do
  let `(pgmTyping| $Γᵢ:Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment; $Γc:Lott.Symbol.TabularTypeInterpreter.ClassEnvironment ⊢ $pgm:Lott.Symbol.TabularTypeInterpreter.Program : $σ:Lott.Symbol.TabularTypeInterpreter.TypeScheme) := stx
    | Lean.Elab.throwUnsupportedSyntax
  let Γᵢ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.InstanceEnvironment profile ref Γᵢ
  let Γc ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.ClassEnvironment profile ref Γc
  let pgm ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.Program profile ref pgm
  let σ ← Lott.texElabSymbolOrJudgement `Lott.Symbol.TabularTypeInterpreter.TypeScheme profile ref σ
  return s!"{Γᵢ} \\lottsym\{;} \\, {Γc} \\, \\lottsym\{⊢} \\, {pgm} \\, \\pgmtypingsym \\, {σ}"

end TabularTypeInterpreter
