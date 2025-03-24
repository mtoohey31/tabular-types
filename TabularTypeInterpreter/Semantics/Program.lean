import TabularTypeInterpreter.Data.Function
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

-- TODO: inst

Γᵢ; Γc; ε ⊢ M : σ ⇝ E
───────────────────── term
Γᵢ; Γc ⊢ M : σ ⇝ E

end TabularTypeInterpreter
