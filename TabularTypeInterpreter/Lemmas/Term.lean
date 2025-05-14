import TabularTypeInterpreter.Lemmas.Type.Basic
import TabularTypeInterpreter.Semantics.Term

namespace TabularTypeInterpreter

open Std

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

theorem singleton_prod (Mte : [[Γᵢ; Γc; Γ ⊢ M : ⌊ξ⌋ ⇝ F]]) (Nte : [[Γᵢ; Γc; Γ ⊢ «N» : τ ⇝ E]])
  (ξke : [[Γc; Γ ⊢ ξ : L ⇝ A₀]]) (τke : [[Γc; Γ ⊢ τ : * ⇝ A₁]]) (μke : [[Γc; Γ ⊢ μ : U ⇝ B]])
  : [[Γᵢ; Γc; Γ ⊢ {M ▹ «N»} : Π(μ) ⟨ξ ▹ τ⟩ ⇝ ⦅λ x : ⊗ {A₁}. x$0⦆ (E)]] := by
  let prodte := prod (by
    intro _ mem
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    exact Mte
  ) (by rw [Range.map_eq_cons_of_lt Nat.zero_lt_one, Range.map_same_eq_nil]; exact .var) (by
    intro _ mem
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    exact Nte
  ) (.inl nofun) (b := false) (n := 1) (Γᵢ := Γᵢ) (Γc := Γc) (Γ := Γ)
    (M := fun _ => M) («N» := fun _ => «N») (ξ := fun _ => ξ)
    (τ := fun _ => τ) (E := fun _ => E) (F := fun _ => F)
  rw [Range.map_eq_cons_of_lt Nat.zero_lt_one, Range.map_eq_cons_of_lt Nat.zero_lt_one,
      Range.map_eq_cons_of_lt Nat.zero_lt_one, Range.map_same_eq_nil, Range.map_same_eq_nil,
      Range.map_same_eq_nil, Option.someIf, if_neg nofun] at prodte
  simp only at prodte
  let prodte' := prodte.sub <| .decay (.prod .comm <| .singleton_row ξke τke) μke .N
  exact prodte'

instance : Inhabited Term where
  default := .prod []
in
instance __ : Inhabited Monotype where
  default := .row [] none
in
instance : Inhabited «F⊗⊕ω».Term where
  default := .prodIntro []
in
theorem unit (μke : [[Γc; Γ ⊢ μ : U ⇝ B]])
  : [[Γᵢ; Γc; Γ ⊢ {} : Π(μ) ⟨ : * ⟩ ⇝ ⦅λ x : ⊗ { }. x$0⦆ ()]] := by
  let prodte := prod nofun (.concrete nofun) nofun (.inr rfl) (n := 0) (Γᵢ := Γᵢ) (Γc := Γc) (Γ := Γ)
    (M := fun _ => default) («N» := fun _ => default) (ξ := fun _ => .label .zero)
    (τ := fun _ => default) (E := fun _ => default) (F := fun _ => default)
  rw [Range.map_same_eq_nil, Range.map_same_eq_nil, Range.map_same_eq_nil, Option.someIf,
      if_pos rfl] at prodte
  let prodte' := prodte.sub <| .decay (.prod .comm .empty_row) μke .N
  exact prodte'

end TypingAndElaboration

end Term

end TabularTypeInterpreter
