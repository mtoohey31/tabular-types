import TabularTypeInterpreter.Lemmas.Type.Basic
import TabularTypeInterpreter.Semantics.Term

namespace TabularTypeInterpreter

namespace Term

namespace TermVarLocallyClosed

theorem weakening : TermVarLocallyClosed M m → TermVarLocallyClosed M (m + n) := sorry

theorem TermVar_open_id : TermVarLocallyClosed M n → TermVar_open M x n = M := sorry

end TermVarLocallyClosed

namespace TypingAndElaboration

theorem TermVarLocallyClosed_of (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) : M.TermVarLocallyClosed := sorry

theorem weakening (Mte : [[Γᵢ; Γc; Γ, Γ'' ⊢ M : σ ⇝ E]]) (Γwe : [[Γc ⊢ Γ, Γ', Γ'' ⇝ Δ]])
  : [[Γᵢ; Γc; Γ, Γ', Γ'' ⊢ M : σ ⇝ E]] := by
  sorry
  -- generalize Γ'''eq : [[Γ, Γ'']] = Γ''' at Mte
  -- induction Mte generalizing Δ Γ'' <;> try cases Γ'''eq
  -- · case var xσinΓ =>
  --   sorry
  -- · case lam I _ τ₀ke ih =>
  --   let τ₀ke' := τ₀ke.weakening Γwe
  --   apply lam (I ++ [[Γ, Γ', Γ'']].termVarDom) _ τ₀ke'
  --   intro x xnin
  --   let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
  --   let Γxwe := Γwe.termExt xninΓ τ₀ke'
  --   rw [← TypeEnvironment.append, ← TypeEnvironment.append] at Γxwe ⊢
  --   exact ih x xninI Γxwe rfl
  -- · case app _ _ M'ih Nih => exact app (M'ih Γwe rfl) (Nih Γwe rfl)
  -- · case qualI I ψke _ ih =>
  --   let ψke' := ψke.weakening Γwe
  --   apply qualI (I ++ [[Γ, Γ', Γ'']].termVarDom) ψke'
  --   intro x xnin
  --   let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
  --   let Γxwe := Γwe.constrExt xninΓ ψke'
  --   rw [← TypeEnvironment.append, ← TypeEnvironment.append] at Γxwe ⊢
  --   exact ih x xninI Γxwe rfl
  -- · case qualE ψce _ ih =>
  --   apply qualE <| ψce.weakening

end TypingAndElaboration

end Term

end TabularTypeInterpreter
