import TabularTypeInterpreter.Semantics.Program
import TabularTypeInterpreter.Theorems.Term

namespace TabularTypeInterpreter

theorem Program.TypingingAndElaboration.soundness (pte : [[Γᵢ; Γc ⊢ pgm : σ ⇝ E]])
  (Γcw : [[⊢c Γc]] := by exact .empty) (Γᵢw : [[Γc ⊢ Γᵢ]] := by exact .empty)
  (σke : [[Γc; ε ⊢ σ : * ⇝ A]]) : [[ε ⊢ E : A]] := match pte with
  | .cls .. => sorry
  -- | .inst .. => sorry
  | .term Mte => Mte.soundness σke Γcw Γᵢw .empty

end TabularTypeInterpreter
