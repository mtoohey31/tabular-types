import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Syntax.Program

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax Γᵢ "; " Γc " ⊢ " pgm " : " σ " ⇝ " E : Program.TypingAndElaboration

judgement Program.TypingAndElaboration where

</ TCₛ@i : κ ⇝ Aₛ@i ∈ Γc // i in [:n] notex />
TC ∉ dom(Γc)
m ∉ dom(Γc)
∀ a, Γc; ε, a : κ ⊢ σ₀^a : * ⇝ A^a
Γᵢ; Γc, (</ TCₛ@i a ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ₀ ⇝ A ⊢ pgm : σ₁ ⇝ E
──────────────────────────────────────────────────────────────────────────────────────── cls {TC}
Γᵢ; Γc ⊢ class </ TCₛ@i a // i in [:n] notex /> ⇒ TC a : κ where {m : σ₀}; pgm : σ₁ ⇝ E

(</ TCₛ@i a' ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a' : κ₀) ↦ m : σ₀ ⇝ A ∈ Γc
</ ∀ a : { a : Nat → TypeVarId // a.Injective' }, Γc; ε,, </ a@k : κ₁@k // k in [:o] notex /> ⊢ ψ@j^^^a#o : C ⇝ B@j^^^a#o // j in [:l] notex />
</ ∀ a : { a : Nat → TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, Γᵢ; Γc; ε,, </ a@k : κ₁@k // k in [:o] notex />,,, </ ψ@j^^^a#o ⇝ x@j // j in [:l] notex /> ⊨ TCₛ@i τ^^^a#o ⇝ Eₛ@i^^^x#l^^^a#o // i in [:n] notex />
∀ a : { a : Nat → TypeVarId // a.Injective' }, Γc; ε,, </ a@k : κ₁@k // k in [:o] notex /> ⊢ τ^^^a#o : κ₀ ⇝ B'^^^a#o
∀ a : { a : Nat → TypeVarId // a.Injective' }, ∀ x : { x : Nat → «F⊗⊕ω».TermVarId // x.Injective' }, Γᵢ; Γc; ε,, </ a@k : κ₁@k // k in [:o] notex />,,, </ ψ@j^^^a#o ⇝ x@j // j in [:l] notex /> ⊢ M^^^x#l^^^a#o : σ₀^^⦅τ^^^a#o⦆/a' ⇝ E^^^x#l^^^a#o
Γᵢ, (∀ </ a@k : κ₁@k // k in [:o] notex />. </ ψ@j ⇝ x@j // j in [:l] notex /> ⇒ TC τ) ↦ E; </ Eₛ@i // i in [:n] notex />; Γc ⊢ pgm : σ₁ ⇝ F
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── inst {TC}
Γᵢ; Γc ⊢ instance </ ψ@j // j in [:l] notex /> ⇒ TC τ where {m = M}; pgm : σ₁ ⇝ F

Γᵢ; Γc; ε ⊢ M : σ ⇝ E
───────────────────── term
Γᵢ; Γc ⊢ M : σ ⇝ E

end TabularTypeInterpreter
