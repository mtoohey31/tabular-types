import TabularTypeInterpreter.Lemmas.Type.Basic
import TabularTypeInterpreter.Lemmas.Type.MonotypeOpenPreservation
import TabularTypeInterpreter.Semantics.Type.SubtypingAndElaboration
import TabularTypeInterpreter.Theorems.Type.KindingAndElaboration

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

theorem Monotype.RowEquivalenceAndElaboration.to_Kinding (ρee : [[Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ]])
  (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ κ A B, [[Γc; Γ ⊢ ρ₀ : R κ ⇝ A]] ∧ [[Γc; Γ ⊢ ρ₁ : R κ ⇝ B]] := by
  match ρee with
  | refl ρek .. => exact ⟨_, _, _, ρek, ρek⟩
  | comm perm _ _ ξτke κe (p_ := p) =>
    let ⟨⟨_, ξke⟩, uni, ⟨_, _, eq, eqκ, h, _, τke⟩⟩ := ξτke.row_inversion
    cases eqκ
    rw [← Std.Range.map_get!_eq (as := p), List.map_map]
    let length_eq := perm.length_eq
    rw [Std.Range.length_toList] at length_eq
    cases length_eq
    let ξke' := fun i (imem : i ∈ [:p.length]) =>
      ξke (p.get! i) <| Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.upper
    let τke' := fun i (imem : i ∈ [:p.length]) =>
      τke (p.get! i) <| Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.upper
    exact ⟨_, _, _, ξτke, .row ξke' (uni.Perm_preservation perm (fun _ => rfl)) τke' h⟩
  | trans ρ₀ke κe ρ₀₁ee ρ₁₂ee =>
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γcw Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    let ⟨_, _, _, ρ₁ke', ρ₂ke⟩ := ρ₁₂ee.to_Kinding Γcw Γwe
    cases ρ₁ke.deterministic ρ₁ke' |>.left
    exact ⟨_, _, _, ρ₀ke, ρ₂ke⟩
  | liftL _ liftke@(.lift I τ₁ke κ₀e ξτ₀ke) _ (τ₁ := τ₁) =>
    let ⟨⟨_, ξke⟩, uni, ⟨_, _, eq, κeq, h, _, τ₀ke⟩⟩ := ξτ₀ke.row_inversion
    cases eq
    cases κeq
    exact ⟨
      _,
      _,
      _,
      liftke,
      .row ξke uni (fun i imem => by
        rename «Type» => A
        let ⟨a, anin⟩ := τ₁.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom ++ I |>.exists_fresh
        let ⟨aninτ₁AΓ, aninI⟩ := List.not_mem_append'.mp anin
        let ⟨aninτ₁A, aninΓ⟩ := List.not_mem_append'.mp aninτ₁AΓ
        let ⟨aninτ₁, aninA⟩ := List.not_mem_append'.mp aninτ₁A
        have := τ₁ke a aninI
        rw [← QualifiedType.Monotype_open, ← TypeScheme.Monotype_open]
        rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at this
        exact this.Monotype_open_preservation Γcw (Γwe.typeExt aninΓ κ₀e) nofun aninτ₁ aninA
          (τ₀ke i imem) (Γ' := .empty)) h
    ⟩
  | liftR _ liftke@(.lift I τ₁ke κ₀e ξτ₀ke) _ (τ₁ := τ₁) =>
    let ⟨⟨_, ξke⟩, uni, ⟨_, _, eq, κeq, h, _, τ₀ke⟩⟩ := ξτ₀ke.row_inversion
    cases eq
    cases κeq
    exact ⟨
      _,
      _,
      _,
      .row ξke uni (fun i imem => by
        rename «Type» => A
        let ⟨a, anin⟩ := τ₁.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom ++ I |>.exists_fresh
        let ⟨aninτ₁AΓ, aninI⟩ := List.not_mem_append'.mp anin
        let ⟨aninτ₁A, aninΓ⟩ := List.not_mem_append'.mp aninτ₁AΓ
        let ⟨aninτ₁, aninA⟩ := List.not_mem_append'.mp aninτ₁A
        have := τ₁ke a aninI
        rw [← QualifiedType.Monotype_open, ← TypeScheme.Monotype_open]
        rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at this
        exact this.Monotype_open_preservation Γcw (Γwe.typeExt aninΓ κ₀e) nofun aninτ₁ aninA
          (τ₀ke i imem) (Γ' := .empty)) h,
      liftke
    ⟩

local instance : Inhabited Monotype where
  default := .row [] none
in
local instance : Inhabited «Type» where
  default := .list []
in
theorem TypeScheme.SubtypingAndElaboration.to_Kinding (σse : [[Γc; Γ ⊢ σ₀ <: σ₁ ⇝ F]])
  (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ κ A B, [[Γc; Γ ⊢ σ₀ : κ ⇝ A]] ∧ [[Γc; Γ ⊢ σ₁ : κ ⇝ B]] := by
  induction σse generalizing Δ with
  | refl σke => exact ⟨_, _, _, σke, σke⟩
  | trans σ₀ke σ₀₁se σ₁₂se σ₀₁ih σ₁₂ih =>
    let ⟨_, _, _, σ₀ke', σ₁ke⟩ := σ₀₁ih Γcw Γwe
    rcases σ₀ke.deterministic σ₀ke' with ⟨rfl, rfl⟩
    let ⟨_, _, _, σ₁ke', σ₂ke⟩ := σ₁₂ih Γcw Γwe
    rcases σ₁ke.deterministic σ₁ke' with ⟨rfl, rfl⟩
    exact ⟨_, _, _, σ₀ke, σ₂ke⟩
  | arr _ _ τ₀τ₁ke τ₂ke _ τ₁₃ih =>
    let .arr _ τ₁ke := τ₀τ₁ke
    let ⟨_, _, _, τ₁ke', τ₃ke⟩ := τ₁₃ih Γcw Γwe
    cases τ₁ke.deterministic τ₁ke' |>.left
    exact ⟨_, _, _, τ₀τ₁ke, τ₂ke.arr τ₃ke⟩
  | qual ψ₁₀se _ ψ₀γ₀ke ψ₁ke _ γ₀₁ih =>
    let .qual _ γ₀ke κe := ψ₀γ₀ke
    let ⟨_, _, _, γ₀ke', γ₁ke⟩ := γ₀₁ih Γcw Γwe
    cases γ₀ke.deterministic γ₀ke' |>.left
    exact ⟨_, _, _, ψ₀γ₀ke, ψ₁ke.qual γ₁ke κe⟩
  | scheme I _ κ₀e σ₀ke σ'ih =>
    rename Kind => κ₁
    rename TypeScheme => σ₁'
    rename TypeEnvironment => Γ
    let .scheme I' σ₀'ke _ := σ₀ke
    let ⟨a, anin⟩ := I ++ I' ++ Γ.typeVarDom ++ σ₁'.freeTypeVars |>.exists_fresh
    let ⟨aninII'Γ, aninσ₁'⟩ := List.not_mem_append'.mp anin
    let ⟨aninII', aninΓ⟩ := List.not_mem_append'.mp aninII'Γ
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let Γawe := Γwe.typeExt aninΓ κ₀e
    let ⟨_, _, B, σ₀'ke', σ₁'ke⟩ := σ'ih a aninI Γcw Γawe
    cases σ₀'ke a aninI' |>.deterministic σ₀'ke' |>.left
    exact ⟨_, _, _, σ₀ke, .scheme (a :: Γ.typeVarDom) (A := B.TypeVar_close a) (by
      intro a' a'nin
      let ⟨a'nea, a'ninΓ⟩ := List.not_mem_cons.mp a'nin
      let ⟨_, κ₁e⟩ := κ₁.Elaboration_total
      rw [← σ₁'ke.soundness Γcw Γawe κ₁e |>.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_close_id
            (a := a)] at σ₁'ke
      let Γa'awe :=
        Γwe.typeExt a'ninΓ κ₀e |>.typeExt (List.not_mem_cons.mpr ⟨a'nea.symm, aninΓ⟩) κ₀e
      have := σ₁'ke.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
        |>.Monotype_open_preservation Γcw Γa'awe nofun aninσ₁'
          Type.not_mem_freeTypeVars_TypeVar_close (.var .head) (Γ' := .empty)
      rw [TypeEnvironment.TypeVar_subst, ← Type.TypeVar_open_eq_Type_open_var,
          ← TypeVar_open_eq_Monotype_open_var] at this
      exact this
    ) κ₀e⟩
  | prod _ prodke τ₀₁ih =>
    rename_i n Γc Γ τ₀ τ₁ _ _ ξ b _ _
    let .prod μke ξτ₀ke := prodke
    generalize ξτ₀s'eq : ([:n].map fun i => (ξ i, τ₀ i)) = ξτ₀s' at *
    generalize κ?eq : Option.someIf Kind.star b = κ? at *
    let .row ξ'ke uni τ₀'ke h (ξ := ξ') := ξτ₀ke
    let neqn' : List.length (Range.map ..) = List.length _ := by rw [ξτ₀s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at neqn'
    cases neqn'
    let ξke i mem := by
      have := ξ'ke i mem
      simp only at this
      rw [← And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at this
      exact this
    rw [Range.map_eq_of_eq_of_mem''
          (Eq.symm <| And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq · ·)] at uni
    let τ₀ke i mem := by
      have := τ₀'ke i mem
      simp only at this
      rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at this
      exact this
    let ⟨_, τ₁ke⟩ := Range.skolem (n := n)
      (p := fun i A => KindingAndElaboration Γc Γ (.qual (.mono (τ₁ i))) .star A) <| by
      intro i mem
      let ⟨_, _, A, τ₀ke', τ₁ke⟩ := τ₀₁ih i mem Γcw Γwe
      cases τ₀ke i mem |>.deterministic τ₀ke' |>.left
      exact ⟨A, τ₁ke⟩
    exact ⟨_, _, _, prodke, .prod μke <| .row ξke uni τ₁ke h⟩
  | sum _ sumke τ₀ke τ₀₁ih =>
    rename_i n Γc Γ τ₀ τ₁ _ _ ξ b _ _ _
    let .sum μke ξτ₀ke := sumke
    generalize ξτ₀s'eq : ([:n].map fun i => (ξ i, τ₀ i)) = ξτ₀s' at *
    generalize κ?eq : Option.someIf Kind.star b = κ? at *
    let .row ξ'ke uni τ₀'ke h (ξ := ξ') := ξτ₀ke
    let neqn' : List.length (Range.map ..) = List.length _ := by rw [ξτ₀s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at neqn'
    cases neqn'
    let ξke i mem := by
      have := ξ'ke i mem
      simp only at this
      rw [← And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at this
      exact this
    rw [Range.map_eq_of_eq_of_mem''
          (Eq.symm <| And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq · ·)] at uni
    let ⟨_, τ₁ke⟩ := Range.skolem (n := n)
      (p := fun i A => KindingAndElaboration Γc Γ (.qual (.mono (τ₁ i))) .star A) <| by
      intro i mem
      let ⟨_, _, A, τ₀ke', τ₁ke⟩ := τ₀₁ih i mem Γcw Γwe
      cases τ₀ke i mem |>.deterministic τ₀ke' |>.left
      exact ⟨A, τ₁ke⟩
    exact ⟨_, _, _, sumke, .sum μke <| .row ξke uni τ₁ke h⟩
  | prodRow ρ₀₁se prodke =>
    let .prod μke ρ₀ke := prodke
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁se.to_Kinding Γcw Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, prodke, .prod μke ρ₁ke⟩
  | sumRow ρ₀₁se sumke =>
    let .sum μke ρ₀ke := sumke
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁se.to_Kinding Γcw Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, sumke, .sum μke ρ₁ke⟩
  | decay prodOrSumke μ₁ke _ =>
    rename ProdOrSum => Ξ
    match Ξ with
    | .prod =>
      let .prod _ ρke := prodOrSumke
      exact ⟨_, _, _, prodOrSumke, .prod μ₁ke ρke⟩
    | .sum =>
      let .sum _ ρke := prodOrSumke
      exact ⟨_, _, _, prodOrSumke, .sum μ₁ke ρke⟩
  | never σke => exact ⟨_, .sum (.list []), _, .sum .comm .empty_row, σke⟩
  | contain _ _ _ _ containke _ _ ρ₂ke ρ₃ke κe =>
    let .contain μke .. := containke
    exact ⟨_, _, _, containke, .contain μke ρ₂ke ρ₃ke κe⟩
  | concat _ _ _ _ _ _ concatke _ _ _ ρ₃ke ρ₄ke ρ₅ke κe contain₀₂₃₅se contain₁₂₄₅se =>
    let .concat μke .. := concatke
    exact ⟨
      _,
      _,
      _,
      concatke,
      .concat μke ρ₃ke ρ₄ke ρ₅ke κe (.contain μke ρ₃ke ρ₅ke κe) (.contain μke ρ₄ke ρ₅ke κe)
    ⟩
  | tc _ σop₀₁se _ TCₛse TCτ₀ke τ₀₁ih =>
    let ⟨_, _, _, τ₀ke, τ₁ke⟩ := τ₀₁ih Γcw Γwe
    let .tc γcin τ₀ke' := TCτ₀ke
    cases τ₀ke.deterministic τ₀ke' |>.left
    exact ⟨_, _, _, TCτ₀ke, .tc γcin τ₁ke⟩
  | tcRow ρ₀₁ee σop₀₁se _ TCₛse TCτ₀ke =>
    let ⟨_, _, _, ρ₀ke, ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γcw Γwe
    let .tc γcin ρ₀ke' := TCτ₀ke
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, TCτ₀ke, .tc γcin ρ₁ke⟩
  | allRow I ρ₀₁ee allke ψke κe =>
    let ⟨_, _, _, ρ₀ke, ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γcw Γwe
    let .all _ _ _ ρ₀ke' := allke
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, allke, .all I ψke κe ρ₁ke⟩
  | split _ concatih =>
    let ⟨_, _, _, concatke@(.concat ..), concatke'@(.concat ..)⟩ := concatih Γcw Γwe
    exact ⟨_, _, _, concatke.split, concatke'.split⟩

end TabularTypeInterpreter
