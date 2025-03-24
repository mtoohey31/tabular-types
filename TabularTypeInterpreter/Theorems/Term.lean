import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Lemmas.TypeEnvironment
import TabularTypeInterpreter.Semantics.InstanceEnvironment
import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Theorems.Type

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

theorem Monotype.ConstraintSolvingAndElaboration.to_Kinding (ψce : [[Γᵢ; Γc; Γ ⊨ ψ ⇝ E]])
  (Γcw : [[⊢c Γc]]) (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : ∃ A, [[Γc; Γ ⊢ ψ : C ⇝ A]] := sorry

namespace Term.TypingAndElaboration

instance : Inhabited Monotype where
  default := .row [] none
in
instance : Inhabited «Type» where
  default := .list []
in
theorem to_Kinding (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) (Γcw : [[⊢c Γc]]) (Γᵢw : [[Γc ⊢ Γᵢ]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : ∃ A, [[Γc; Γ ⊢ σ : * ⇝ A]] := by
  induction Mte using rec (motive_2 := fun Γᵢ Γc Γ ψ E ψce =>
      ∀ {Δ}, [[⊢c Γc]] → [[Γc ⊢ Γᵢ]] → [[Γc ⊢ Γ ⇝ Δ]] → ∃ A, [[Γc; Γ ⊢ ψ : C ⇝ A]])
    generalizing Δ with
  | var xinΓ => exact Γwe.KindingAndElaboration_of_TermVarIn xinΓ
  | lam I _ τ₀ke ih =>
    rename TypeEnvironment => Γ
    let ⟨x, xnin⟩ := I ++ Γ.termVarDom |>.exists_fresh
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let ⟨_, τ₁ke⟩ := ih x xninI Γcw Γᵢw <| Γwe.termExt xninΓ τ₀ke
    exact ⟨_, τ₀ke.arr <| τ₁ke.TermVar_drop (Γ' := .empty)⟩
  | app _ _ ϕih τih =>
    let ⟨_, .arr _ τ₁ke⟩ := ϕih Γcw Γᵢw Γwe
    exact ⟨_, τ₁ke⟩
  | qualI I ψke _ ih =>
    rename TypeEnvironment => Γ
    let ⟨x, xnin⟩ := I ++ Γ.termVarDom |>.exists_fresh
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let ⟨_, γke⟩ := ih x xninI Γcw Γᵢw <| Γwe.constrExt xninΓ ψke
    exact ⟨_, ψke.qual (γke.Constr_drop (Γ' := .empty)) .star⟩
  | qualE ψce _ _ γih =>
    let ⟨_, .qual _ γke _⟩ := γih Γcw Γᵢw Γwe
    exact ⟨_, γke⟩
  | schemeI I _ κe ih =>
    rename TypeScheme => σ'
    rename TypeEnvironment => Γ
    let ⟨a, anin⟩ := I ++ Γ.typeVarDom ++ σ'.freeTypeVars |>.exists_fresh
    let ⟨aninIΓ, aninσ'⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp aninIΓ
    let Γawe := Γwe.typeExt aninΓ κe
    let ⟨_, σ'ke⟩ := ih a aninI Γcw Γᵢw Γawe
    let Alc := σ'ke.soundness Γcw Γawe .star |>.TypeVarLocallyClosed_of
    rw [← Alc.TypeVar_open_TypeVar_close_id (a := a)] at σ'ke
    exact ⟨_, .scheme (I ++ ↑a :: Γ.typeVarDom) (by
      intro a' a'nin
      let ⟨a'ninI, a'ninΓa⟩ := List.not_mem_append'.mp a'nin
      let ⟨a'nea, a'ninΓ⟩ := List.not_mem_cons.mp a'ninΓa
      let Γa'awe := Γwe.typeExt a'ninΓ κe |>.typeExt (List.not_mem_cons.mpr ⟨a'nea.symm, aninΓ⟩) κe
      let σ'ke' := σ'ke.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
      have := σ'ke'.Monotype_open_preservation Γcw Γa'awe nofun aninσ'
        Type.not_mem_freeTypeVars_TypeVar_close (.var .head) (Γ' := .empty)
      rw [← TypeScheme.TypeVar_open_eq_Monotype_open_var,
          ← Type.TypeVar_open_eq_Type_open_var] at this
      exact this) κe⟩
  | schemeE _ τke σih =>
    rename TypeEnvironment => Γ
    rename TypeScheme => σ'
    let ⟨_, σke⟩ := σih Γcw Γᵢw Γwe
    let .scheme I σ'opke κ₀e (A := A) := σke
    let ⟨a, anin⟩ := Γ.typeVarDom ++ σ'.freeTypeVars ++ ↑A.freeTypeVars ++ I |>.exists_fresh
    let ⟨aninΓσ'A, aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓσ', aninA⟩ := List.not_mem_append'.mp aninΓσ'A
    let ⟨aninΓ, aninσ'⟩ := List.not_mem_append'.mp aninΓσ'
    let σ'opke' := σ'opke a aninI
    let Γawe := Γwe.typeExt aninΓ κ₀e
    exact ⟨_, σ'opke'.Monotype_open_preservation Γcw Γawe nofun aninσ' aninA τke (Γ' := .empty)⟩
  | «let» I _ σ₀ke _ _ σ₁ih =>
    rename TypeEnvironment => Γ
    let ⟨x, xnin⟩ := Γ.termVarDom ++ I |>.exists_fresh
    let ⟨xninΓ, xninI⟩ := List.not_mem_append'.mp xnin
    let ⟨_, σ₁ke⟩ := σ₁ih _ xninI Γcw Γᵢw <| Γwe.termExt xninΓ σ₀ke
    exact ⟨_, σ₁ke.TermVar_drop (Γ' := .empty)⟩
  | annot _ ih => exact ih Γcw Γᵢw Γwe
  | label => exact ⟨_, .floor .label⟩
  | prod _ uni _ μke h ξih τih =>
    rename Nat => n
    rename ClassEnvironment => Γc
    rename TypeEnvironment => Γ
    rename_i ξ _ _ _ _ _ _ _ _ _
    let ⟨_, ξke⟩ := Range.skolem (n := n) (p := fun i B => [[Γc; Γ ⊢ ξ@i : L ⇝ B]]) <| by
      intro i mem
      let ⟨_, .floor ξke⟩ := ξih i mem Γcw Γᵢw Γwe
      exact ⟨_, ξke⟩
    let ⟨_, τke⟩ := Range.skolem (τih · · Γcw Γᵢw Γwe)
    exact ⟨_, .prod μke (.row ξke uni τke h)⟩
  | sum _ _ μke ξih τih =>
    let ⟨_, .floor ξke⟩ := ξih Γcw Γᵢw Γwe
    let ⟨_, τke⟩ := τih Γcw Γᵢw Γwe
    exact ⟨_, .sum μke <| .singleton_row ξke τke⟩
  | unlabelProd _ _ prodih _ =>
    let ⟨_, .prod μke rowke⟩ := prodih Γcw Γᵢw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    exact ⟨_, τke⟩
  | unlabelSum _ _ _ sumih _ =>
    let ⟨_, .sum μke rowke⟩ := sumih Γcw Γᵢw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    exact ⟨_, τke⟩
  | «prj» _ _ prodke containih =>
    let ⟨_, .prod μke ρ₀ke⟩ := prodke Γcw Γᵢw Γwe
    let ⟨_, .contain _ ρ₁ke ρ₀ke' _⟩ := containih Γcw Γᵢw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .prod μke ρ₁ke⟩
  | concat _ _ _ prod₀ih _ concatih =>
    let ⟨_, .prod μke ρ₀ke⟩ := prod₀ih Γcw Γᵢw Γwe
    let ⟨_, .concat _ ρ₀ke' _ ρ₂ke _ _ _⟩ := concatih Γcw Γᵢw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .prod μke ρ₂ke⟩
  | «inj» _ _ sumih containih =>
    let ⟨_, .sum μke ρ₀ke⟩ := sumih Γcw Γᵢw Γwe
    let ⟨_, .contain _ ρ₀ke' ρ₁ke _⟩ := containih Γcw Γᵢw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .sum μke ρ₁ke⟩
  | elim _ _ _ τke sum₀ih _ concatih =>
    let ⟨_, .arr (.sum μke ρ₀ke) _⟩ := sum₀ih Γcw Γᵢw Γwe
    let ⟨_, .concat _ ρ₀ke' _ ρ₂ke _ _ _⟩ := concatih Γcw Γᵢw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .arr (.sum μke ρ₂ke) τke⟩
  | sub _ τ₀₁ee ih =>
    let ⟨_, τ₀ke⟩ := ih Γcw Γᵢw Γwe
    let ⟨_, _, _, τ₀ke', τ₁ke⟩ := τ₀₁ee.to_Kinding Γcw Γwe
    rcases τ₀ke.deterministic τ₀ke' with ⟨rfl, _⟩
    exact ⟨_, τ₁ke⟩
  | member γcin _ ih =>
    rename TypeEnvironment => Γ
    rename Kind => κ
    rename TypeScheme => σ'
    rename «Type» => A
    let ⟨_, .tc γcin' τke⟩ := ih Γcw Γᵢw Γwe
    rcases ClassEnvironmentEntry.mk.inj <| γcin.deterministic γcin' rfl with ⟨_, _, rfl, _⟩
    let ⟨_, κe, σ'ke, _⟩ := Γcw.of_ClassEnvironment_in γcin
    let ⟨a, anin⟩ := Γ.typeVarDom ++ σ'.freeTypeVars ++ ↑A.freeTypeVars |>.exists_fresh
    let ⟨aninΓσ', aninA⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓ, aninσ'⟩ := List.not_mem_append'.mp aninΓσ'
    let Γawe := Γwe.typeExt aninΓ κe
    rw [← Γ.empty_append] at Γawe
    let σ'ke' := σ'ke a |>.weakening Γawe (Γ' := Γ) (Γ'' := .typeExt .empty ..)
    rw [TypeEnvironment.empty_append] at Γawe σ'ke'
    exact ⟨_, σ'ke'.Monotype_open_preservation Γcw Γawe nofun aninσ' aninA τke (Γ' := .empty)⟩
  | «order» _ ih =>
    rename ProdOrSum => Ξ
    match Ξ with
    | .prod =>
      let ⟨_, .prod _ ρke⟩ := ih Γcw Γᵢw Γwe
      exact ⟨_, .prod .comm ρke⟩
    | .sum =>
      let ⟨_, .sum _ ρke⟩ := ih Γcw Γᵢw Γwe
      exact ⟨_, .sum .comm ρke⟩
  | «ind» Iₘ Iₛ ρke τke κe =>
    rename TypeEnvironment => Γ
    rename Monotype => τ
    rename «Type» => B
    let ⟨a, anin⟩ := Γ.typeVarDom ++ τ.freeTypeVars ++ ↑B.freeTypeVars ++ Iₘ |>.exists_fresh
    let ⟨aninΓτB, aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓτ, aninB⟩ := List.not_mem_append'.mp aninΓτB
    let ⟨aninΓ, aninτ⟩ := List.not_mem_append'.mp aninΓτ
    let Γawe := Γwe.typeExt aninΓ κe.row
    let τke' := τke a aninI
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at τke'
    exact ⟨_, τke'.Monotype_open_preservation Γcw Γawe nofun aninτ aninB ρke (Γ' := .empty)⟩
  | splitP _ _ prodih splitih =>
    let ⟨_, .prod μke ρ₂ke⟩ := prodih Γcw Γᵢw Γwe
    let ⟨_, .split concatke⟩ := splitih Γcw Γᵢw Γwe
    let .concat _ ρ₀ke ρ₁ke ρ₂ke' _ _ _ (A₀ := A₀) (A₁ := A₁) := concatke
    let ⟨κeq, _⟩ := ρ₂ke.deterministic ρ₂ke'
    cases Kind.row.inj κeq
    apply Exists.intro _
    apply TypeScheme.KindingAndElaboration.prod .comm
    have : none = Option.someIf Kind.star false := by rw [Option.someIf, if_neg nofun]
    rw [← Range.map_get!_eq (as := [_, _]), this]
    apply TypeScheme.KindingAndElaboration.row
      (A := fun | 0 => A₀.prod | 1 => A₁.prod | _ => default) (B := fun _ => [[⊗ { }]]) _ _ _ <|
      .inl <| by
        rw [List.length_cons, List.length_singleton]
        exact Nat.succ_ne_zero _
    · intro i mem
      match i with
      | 0 => exact .label
      | 1 => exact .label
    · rw [Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = Monotype.label i
        match i with
        | 0 => rw [List.get!_cons_zero]
        | 1 => rw [List.get!_cons_succ, List.get!_cons_zero]
      ), List.length_cons, List.length_singleton]
      apply Monotype.label.Uniqueness.concrete
      intro i mem
      match i with
      | 0 =>
        intro j mem
        match j with
        | 0 => nomatch Nat.not_lt_of_le mem.lower
        | _ + 1 => exact Nat.zero_ne_add_one _
      | _ + 1 =>
        rintro j ⟨lej, jlt, _⟩
        rw [Nat.add_assoc] at lej
        nomatch Nat.not_lt_of_le (Nat.le_trans (Nat.le_add_left ..) lej) jlt
    · intro i mem
      match i with
      | 0 =>
        rw [List.get!_cons_zero]
        exact .prod μke ρ₀ke
      | 1 =>
        rw [List.get!_cons_succ, List.get!_cons_zero]
        exact .prod μke ρ₁ke
  | splitS _ _ _ _ _ arrρ₁ih splitih =>
    let ⟨_, .arr (.sum μke ρ₁ke) τ₁ke⟩ := arrρ₁ih Γcw Γᵢw Γwe
    let ⟨_, .split concatke⟩ := splitih Γcw Γᵢw Γwe
    let .concat _ _ ρ₁ke' ρ₂ke .. := concatke
    let ⟨κeq, _⟩ := ρ₁ke.deterministic ρ₁ke'
    cases Kind.row.inj κeq
    exact ⟨_, .arr (.sum μke ρ₂ke) τ₁ke⟩

theorem _root_.TabularTypeInterpreter.«F⊗⊕ω».Type.eq_forall_of_TypeVar_open_eq_forall
  (eq : Type.TypeVar_open A a n = .forall K B)
  : ∃ A', Type.TypeVar_open A' a (n + 1) = B ∧ A = .forall K A' := by
  cases A <;> rw [Type.TypeVar_open] at eq
  case «forall» =>
    rcases Type.forall.inj eq with ⟨rfl, rfl⟩
    exact ⟨_, rfl, rfl⟩
  all_goals nomatch eq

theorem _root_.TabularTypeInterpreter.«F⊗⊕ω».Type.eq_arr_of_TypeVar_open_eq_arr
  (eq : Type.TypeVar_open A a n = .arr A' B)
  : ∃ A'' B', Type.TypeVar_open A'' a n = A' ∧ Type.TypeVar_open B' a n = B ∧ A = .arr A'' B' := by
  cases A <;> rw [Type.TypeVar_open] at eq
  case arr =>
    rcases Type.arr.inj eq with ⟨rfl, rfl⟩
    exact ⟨_, _, rfl, rfl, rfl⟩
  all_goals nomatch eq

theorem _root_.TabularTypeInterpreter.«F⊗⊕ω».Type.eq_unit_of_TypeVar_open_eq_unit
  (eq : Type.TypeVar_open A a n = .prod (.list [])) : A = .prod (.list []) := by
  cases A <;> rw [Type.TypeVar_open] at eq
  case prod =>
    rename «Type» => A
    cases A <;> rw [Type.TypeVar_open] at eq
    case list =>
      rename List «Type» => A
      rw [List.mapMem_eq_map] at eq
      cases List.map_eq_nil_iff.mp <| Type.list.inj <| Type.prod.inj eq
      rfl
    all_goals nomatch eq
  all_goals nomatch eq

theorem soundness (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) (σke : [[Γc; Γ ⊢ σ : * ⇝ A]]) (Γcw : [[⊢c Γc]])
  (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : [[Δ ⊢ E : A]] := by
  induction Mte using rec
    (motive_2 := fun Γᵢ Γc Γ ψ E ψce =>
      ∀ {A Δ}, [[Γc; Γ ⊢ ψ : C ⇝ A]] → [[⊢c Γc]] → [[Γc ⊢ Γᵢ]] → [[Γc ⊢ Γ ⇝ Δ]] → [[Δ ⊢ E : A]])
    generalizing Δ A with
  | var xinΓ => exact .var (Γwe.soundness Γcw) <| Γwe.TermVarIn_preservation xinΓ σke
  | lam I Mte τ₀ke ih =>
    let .arr τ₀ke' τ₁ke := σke
    rcases τ₀ke.deterministic τ₀ke' with ⟨_, rfl⟩
    rename TypeEnvironment => Γ
    apply Typing.lam <| I ++ Γ.termVarDom
    intro x xnin
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let Γxwe := Γwe.termExt xninΓ τ₀ke
    let τ₁ke' := τ₁ke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
    exact ih _ xninI τ₁ke' Γcw Γᵢw Γxwe
  | app Mte _ Mih Nih =>
    let ⟨_, arrke@(.arr τ₀ke τ₁ke)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    rcases σke.deterministic τ₁ke with ⟨_, rfl⟩
    exact .app (Mih arrke Γcw Γᵢw Γwe) (Nih τ₀ke Γcw Γᵢw Γwe)
  | qualI I ψke _ ih =>
    let .qual ψke' γke κe := σke
    rcases ψke.deterministic ψke' with ⟨_, rfl⟩
    rename TypeEnvironment => Γ
    apply Typing.lam <| I ++ Γ.termVarDom
    intro x xnin
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let Γxwe := Γwe.constrExt xninΓ ψke
    let γke' := γke.weakening Γxwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
    exact ih _ xninI γke' Γcw Γᵢw Γxwe
  | qualE ψce Mte ψih qualih =>
    let ⟨_, qualke@(.qual ψke γke _)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    rcases σke.deterministic γke with ⟨_, rfl⟩
    exact .app (qualih qualke Γcw Γᵢw Γwe) (ψih ψke Γcw Γᵢw Γwe)
  | schemeI I _ κe ih =>
    let .scheme I' σ'ke κe' := σke
    cases κe.deterministic κe'
    rename TypeEnvironment => Γ
    apply Typing.typeLam <| I ++ I' ++ Γ.typeVarDom
    intro a anin
    let ⟨aninII', aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact ih _ aninI (σ'ke _ aninI') Γcw Γᵢw (Γwe.typeExt aninΓ κe)
  | schemeE Mte τke ih =>
    let ⟨_, schemeke@(.scheme I σ'ke κ₀e)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    rename TypeEnvironment => Γ
    rename TypeScheme => σ'
    rename «Type» => A
    let ⟨a, anin⟩ := I ++ σ'.freeTypeVars ++ ↑A.freeTypeVars ++ Γ.typeVarDom |>.exists_fresh
    let ⟨aninIσ'A, aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninIσ', aninA⟩ := List.not_mem_append'.mp aninIσ'A
    let ⟨aninI, aninσ'⟩ := List.not_mem_append'.mp aninIσ'
    let Γawe := Γwe.typeExt aninΓ κ₀e
    let σke' := σ'ke a aninI |>.Monotype_open_preservation Γcw Γawe nofun aninσ' aninA τke
      (Γ' := .empty)
    rcases σke.deterministic σke' with ⟨_, rfl⟩
    exact .typeApp (ih schemeke Γcw Γᵢw Γwe) (τke.soundness Γcw Γwe κ₀e)
  | «let» I Mte σ₀ke Nte Mih Nih =>
    apply Typing.app _ <| Mih σ₀ke Γcw Γᵢw Γwe
    rename TypeEnvironment => Γ
    apply Typing.lam <| I ++ Γ.termVarDom
    intro x xnin
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let Γxwe := Γwe.termExt xninΓ σ₀ke
    let σ₁ke := σke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
    exact Nih _ xninI σ₁ke Γcw Γᵢw Γxwe
  | annot _ ih => exact ih σke Γcw Γᵢw Γwe
  | label =>
    let .floor _ := σke
    exact .prodIntro' (Γwe.soundness Γcw) nofun rfl
  | prod _ _ _ _ _ _ ih =>
    let .prod _ rowke := σke
    rcases rowke.row_inversion with ⟨_, _, _, _, rfl, κeq, _, _, τke⟩
    cases Kind.row.inj κeq
    apply Typing.prodIntro (Γwe.soundness Γcw)
    intro i mem
    exact ih i mem (τke i mem) Γcw Γᵢw Γwe
  | sum _ _ _ _ ih =>
    let .sum _ rowke := σke
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    rw [← Range.map_get!_eq (as := [_]), List.length_singleton]
    let mem : 0 ∈ [0:1] := ⟨Nat.le.refl, Nat.one_pos, Nat.mod_one _⟩
    apply Typing.sumIntro mem <| ih τke Γcw Γᵢw Γwe
    intro i mem
    let 0 := i
    rw [List.get!_cons_zero]
    exact τke.soundness Γcw Γwe .star
  | unlabelProd Mte _ ih =>
    let ⟨_, prodke@(.prod _ rowke)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    rcases σke.deterministic τke with ⟨_, rfl⟩
    apply Typing.prodElim _ ⟨Nat.le.refl, Nat.one_pos, Nat.mod_one _⟩ (A := fun _ => A)
    rw [Range.map, Range.toList, if_pos Nat.one_pos, Range.toList, Nat.zero_add,
        if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_singleton]
    exact ih prodke Γcw Γᵢw Γwe
  | unlabelSum Mte _ τke ih =>
    let ⟨_, sumke@(.sum _ rowke)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke'⟩
    cases Kind.row.inj κeq
    rcases σke.deterministic τke with ⟨_, rfl⟩
    rcases σke.deterministic τke' with ⟨_, rfl⟩
    apply Typing.sumElim' (ih sumke Γcw Γᵢw Γwe) _ (τke.soundness Γcw Γwe .star) <| by
      rw [List.length_singleton, List.length_singleton]
    intro _ mem
    rw [List.zip_cons_cons, List.zip_nil_left] at mem
    cases List.mem_singleton.mp mem
    conv => simp_match
    exact .id (Γwe.soundness Γcw) <| τke.soundness Γcw Γwe .star
  | «prj» Mte _ Mih containih =>
    let ⟨_, prodke@(.prod μke ρ₀ke)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    apply Typing.app _ <| Mih prodke Γcw Γᵢw Γwe
    let .prod _ ρ₁ke := σke
    let Fty := containih (.contain μke ρ₁ke ρ₀ke .star) Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := [_, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl, Nat.two_pos, Nat.mod_one _⟩
    rw [List.length_cons, List.length_singleton, List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv this <| .arr (.prod .listAppIdL) (.prod .listAppIdL)
  | concat Mte Nte ψce Mih Nih concatih =>
    let ⟨_, prod₀ke⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    let ⟨_, prod₁ke⟩ := Nte.to_Kinding Γcw Γᵢw Γwe
    apply Typing.app _ <| Nih prod₁ke Γcw Γᵢw Γwe
    apply Typing.app _ <| Mih prod₀ke Γcw Γᵢw Γwe
    let .prod μke ρ₀ke := prod₀ke
    let .prod _ ρ₁ke := prod₁ke
    let .prod _ ρ₂ke := σke
    let ⟨_, .concat ..⟩ := ψce.to_Kinding Γcw Γᵢw Γwe
    let Fty := concatih (.concat μke ρ₀ke ρ₁ke ρ₂ke .star (.contain μke ρ₀ke ρ₂ke .star)
      (.contain μke ρ₁ke ρ₂ke .star)) Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl, Nat.le.refl.step.step.step, Nat.mod_one _⟩
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton,
        List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₂ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv this <| .arr (.prod .listAppIdL) (.arr (.prod .listAppIdL) (.prod .listAppIdL))
  | «inj» Mte _ Mih containih =>
    let ⟨_, sumke@(.sum μke ρ₀ke)⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    apply Typing.app _ <| Mih sumke Γcw Γᵢw Γwe
    let .sum _ ρ₁ke := σke
    let Fty := containih (.contain μke ρ₀ke ρ₁ke .star) Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := [_, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩
    rw [List.length_cons, List.length_singleton, List.get!_cons_succ, List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv this <| .arr (.sum .listAppIdL) (.sum .listAppIdL)
  | elim Mte Nte ψce τke Mih Nih concatih =>
    let ⟨_, arr₀ke⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    let ⟨_, arr₁ke⟩ := Nte.to_Kinding Γcw Γᵢw Γwe
    apply Typing.app _ <| Nih arr₁ke Γcw Γᵢw Γwe
    apply Typing.app _ <| Mih arr₀ke Γcw Γᵢw Γwe
    let .arr (.sum μke ρ₀ke) τke' := arr₀ke
    rcases τke.deterministic τke' with ⟨_, rfl⟩
    let .arr (.sum _ ρ₁ke) τke'' := arr₁ke
    rcases τke.deterministic τke'' with ⟨_, rfl⟩
    let .arr (.sum _ ρ₂ke) τke''' := σke
    rcases τke.deterministic τke''' with ⟨_, rfl⟩
    let ⟨_, .concat ..⟩ := ψce.to_Kinding Γcw Γᵢw Γwe
    let Fty := concatih (.concat μke ρ₀ke ρ₁ke ρ₂ke .star (.contain μke ρ₀ke ρ₂ke .star)
      (.contain μke ρ₁ke ρ₂ke .star)) Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton,
        List.get!_cons_succ, List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    let A₀lc := ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of
    let A₁lc := ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of
    let A₂lc := ρ₂ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of
    rw [A₀lc.weaken (n := 1).Type_open_id, A₁lc.weaken (n := 1).Type_open_id,
        A₂lc.weaken (n := 1).Type_open_id] at this
    have := this.typeApp <| τke.soundness Γcw Γwe .star
    simp [Type.Type_open] at this
    rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at this
    exact .equiv this <| .arr (.arr (.sum .listAppIdL) .refl) <|
      .arr (.arr (.sum .listAppIdL) .refl) <| .arr (.sum .listAppIdL) .refl
  | sub Mte τse ih =>
    let ⟨_, τ₀ke⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    let ⟨_, _, _, τ₀ke', τ₁ke⟩ := τse.to_Kinding Γcw Γwe
    rcases τ₀ke.deterministic τ₀ke' with ⟨rfl, rfl⟩
    rcases σke.deterministic τ₁ke with ⟨_, rfl⟩
    exact .app (τse.soundness Γcw Γwe τ₀ke τ₁ke .star) (ih τ₀ke Γcw Γᵢw Γwe)
  | member γcin TCce TCih =>
    rename_i A' _ _ _ _ _ _
    let ⟨_, tcke@(.tc γcin' τke)⟩ := TCce.to_Kinding Γcw Γᵢw Γwe
    rcases ClassEnvironmentEntry.mk.inj <| γcin.deterministic γcin' rfl
      with ⟨_, _, rfl, rfl, rfl, rfl⟩
    rcases Γcw.of_ClassEnvironment_in γcin with ⟨_, κe, σ'ke, Aki, TCₛke, Aₛki⟩
    rename TypeEnvironment => Γ
    rename TypeScheme => σ'
    let ⟨a, anin⟩ := Γ.typeVarDom ++ σ'.freeTypeVars ++ ↑A'.freeTypeVars |>.exists_fresh
    let ⟨aninΓσ', aninA'⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓ, aninσ'⟩ := List.not_mem_append'.mp aninΓσ'
    let Γawe := Γwe.typeExt aninΓ κe
    rw [← Γ.empty_append] at Γawe
    let σ'ke' := σ'ke a |>.weakening Γawe (Γ'' := .typeExt .empty ..)
    rw [TypeEnvironment.empty_append] at Γawe σ'ke'
    let σke' := σ'ke'.Monotype_open_preservation Γcw Γawe nofun aninσ' aninA' τke (Γ' := .empty)
    rcases σke.deterministic σke' with ⟨_, rfl⟩
    let Ety := TCih tcke Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := _ :: _)] at Ety
    let πty := Ety.prodElim
      ⟨Nat.le.refl, by rw [List.length_cons]; exact Nat.succ_pos _, Nat.mod_one _⟩
    rw [List.length_cons, List.length_map, Range.length_toList, Nat.sub_zero,
        List.get!_cons_zero] at πty
    simp only at πty
    exact πty
  | «order» M'te ih =>
    rename ProdOrSum => Ξ
    match Ξ with
    | .prod =>
      let .prod _ ρke := σke
      exact ih (.prod .comm ρke) Γcw Γᵢw Γwe
    | .sum =>
      let .sum _ ρke := σke
      exact ih (.sum .comm ρke) Γcw Γᵢw Γwe
  | «ind» Iₘ Iₛ ρke τke κe Mte Nte indce Mih Nih indih =>
    rename_i Γc Γ ρ κ _ τ B K _ _ _ _ _ _
    let ⟨a, anin⟩ := Γ.typeVarDom ++ τ.freeTypeVars ++ ↑B.freeTypeVars ++ Iₘ |>.exists_fresh
    let ⟨aninΓτB, aninI⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓτ, aninB⟩ := List.not_mem_append'.mp aninΓτB
    let ⟨aninΓ, aninτ⟩ := List.not_mem_append'.mp aninΓτ
    let Γawe := Γwe.typeExt aninΓ κe.row
    let τke' := τke _ aninI
    rw [← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at τke'
    let τopρke := τke'.Monotype_open_preservation Γcw Γawe nofun aninτ aninB ρke (Γ' := .empty)
    rcases τopρke.deterministic σke with ⟨_, rfl⟩
    let τopemptyke := τke'.Monotype_open_preservation Γcw Γawe nofun aninτ aninB .empty_row
      (Γ' := .empty)
    apply Typing.app _ <| Nih τopemptyke Γcw Γᵢw Γwe
    let ⟨_, indke@(.ind I₀ I₁ ρke' κe' keBᵣ keBₗ)⟩ := indce.to_Kinding Γcw Γᵢw Γwe
    rename_i Bᵣ Bₗ _ _ _
    rcases ρke.deterministic ρke' with ⟨κeq, rfl⟩
    cases Kind.row.inj κeq
    cases κe.deterministic κe'
    let Fty := indih indke Γcw Γᵢw Γwe
    have := Fty.typeApp <| .lam (Iₘ ++ Γ.typeVarDom) fun a anin =>
      let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp anin
      τke a aninI |>.soundness Γcw (Γwe.typeExt aninΓ κe.row) .star
    simp [Type.Type_open] at this
    rw [ρke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id] at this
    apply Typing.app <| this.equiv <| .arr .refl <| .arr .lamAppL .lamAppL
    apply Typing.typeLam <| Γ.typeVarDom ++ I₀ ++ Iₛ
    intro aₗ aₗnin
    let ⟨aₗninΓI₀, aₗninIₛ⟩ := List.not_mem_append'.mp aₗnin
    let ⟨aₗninΓ, aₗninI₀⟩ := List.not_mem_append'.mp aₗninΓI₀
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    apply Typing.typeLam <| ↑aₗ :: Γ.typeVarDom ++ ↑aₗ :: I₀ ++ ↑aₗ :: Iₛ
    intro aₜ aₜnin
    let ⟨aₜninΓI₀, aₜninIₛ⟩ := List.not_mem_append'.mp aₜnin
    let ⟨aₜninΓ, aₜninI₀⟩ := List.not_mem_append'.mp aₜninΓI₀
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    apply Typing.typeLam <| ↑aₜ :: ↑aₗ :: Γ.typeVarDom ++ ↑aₜ :: ↑aₗ :: I₀ ++ Iₘ ++ ↑aₜ :: ↑aₗ :: Iₛ
    intro aₚ aₚnin
    let ⟨aₚninΓI₀ₘ, aₚninIₛ⟩ := List.not_mem_append'.mp aₚnin
    let ⟨aₚninΓI₀, aₚninIₘ⟩ := List.not_mem_append'.mp aₚninΓI₀ₘ
    let ⟨aₚninΓ, aₚninI₀⟩ := List.not_mem_append'.mp aₚninΓI₀
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    apply Typing.typeLam <| ↑aₚ :: ↑aₜ :: ↑aₗ :: Γ.typeVarDom ++ Γ.typeVarDom ++
      ↑aₚ :: ↑aₜ :: ↑aₗ :: I₀ ++ I₁ ++ Iₘ ++ ↑aₚ :: ↑aₜ :: ↑aₗ :: Iₛ
    intro aᵢ aᵢnin
    let ⟨aᵢninΓΓ'I₀₁ₘ, aᵢninIₛ⟩ := List.not_mem_append'.mp aᵢnin
    let ⟨aᵢninΓΓ'I₀₁, aᵢninIₘ⟩ := List.not_mem_append'.mp aᵢninΓΓ'I₀₁ₘ
    let ⟨aᵢninΓΓ'I₀, aᵢninI₁⟩ := List.not_mem_append'.mp aᵢninΓΓ'I₀₁
    let ⟨aᵢninΓΓ', aᵢninI₀⟩ := List.not_mem_append'.mp aᵢninΓΓ'I₀
    let ⟨aᵢninΓ, aᵢninΓ'⟩ := List.not_mem_append'.mp aᵢninΓΓ'
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    apply Typing.typeLam <| ↑aᵢ :: ↑aₚ :: ↑aₜ :: ↑aₗ :: Γ.typeVarDom ++ ↑aᵢ :: Γ.typeVarDom ++
      ↑aᵢ :: ↑aₚ :: ↑aₜ :: ↑aₗ :: I₀ ++ ↑aᵢ :: I₁ ++ ↑aᵢ :: ↑aₚ :: ↑aₜ :: ↑aₗ :: Iₛ
    intro aₙ aₙnin
    let ⟨aₙninΓΓ'I₀₁, aₙninIₛ⟩ := List.not_mem_append'.mp aₙnin
    let ⟨aₙninΓΓ'I₀, aₙninI₁⟩ := List.not_mem_append'.mp aₙninΓΓ'I₀₁
    let ⟨aₙninΓΓ', aₙninI₀⟩ := List.not_mem_append'.mp aₙninΓΓ'I₀
    let ⟨aₙninΓ, aₙninΓ'⟩ := List.not_mem_append'.mp aₙninΓΓ'
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    let Γaₗₜₚᵢₙwe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
      |>.typeExt aᵢninΓ κe.row |>.typeExt aₙninΓ κe.row
    apply Typing.equiv _ <| .arr .refl <| .arr .refl <| .arr .refl <| .arr .lamAppR .lamAppR
    apply Mih _ aₗninIₛ _ aₜninIₛ _ aₚninIₛ _ aᵢninIₛ _ aₙninIₛ _ Γcw Γᵢw Γaₗₜₚᵢₙwe
    open TypeScheme.KindingAndElaboration in
    let keBᵣ' := keBᵣ _ aₗninI₀ _ aₜninI₀ _ aₚninI₀ _ aᵢninI₀ _ aₙninI₀
    let Γaₗₜₚwe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
    let Γaₗₜₚᵢwe := Γaₗₜₚwe.typeExt aᵢninΓ κe.row
    let Γaₗₜₚᵢₙwe := Γaₗₜₚᵢwe.typeExt aₙninΓ κe.row
    let Bᵣlc := keBᵣ'.soundness Γcw Γaₗₜₚᵢₙwe .constr |>.TypeVarLocallyClosed_of.weaken (n := 5)
      |>.TypeVar_open_drop Nat.le.refl.step.step.step.step
      |>.TypeVar_open_drop Nat.le.refl.step.step.step
      |>.TypeVar_open_drop Nat.le.refl.step.step
      |>.TypeVar_open_drop Nat.le.refl.step
      |>.TypeVar_open_drop Nat.le.refl
    let keBₗ' := keBₗ _ aᵢninI₁ _ aₙninI₁
    let Γaᵢₙwe := Γwe.typeExt aᵢninΓ' κe.row |>.typeExt aₙninΓ' κe.row
    let Bₗlc := keBₗ'.soundness Γcw Γaᵢₙwe .constr |>.TypeVarLocallyClosed_of.weaken (n := 2)
      |>.TypeVar_open_drop Nat.le.refl.step
      |>.TypeVar_open_drop Nat.le.refl
    rw [Bᵣlc.Type_open_id, Bₗlc.weaken (n := 3).Type_open_id] at this ⊢
    rw [Bₗlc.weaken (n := 2).TypeVar_open_id, Bₗlc.weaken (n := 1).TypeVar_open_id,
        Bₗlc.TypeVar_open_id]
    apply qual keBᵣ' _ .star
    let keBₗ'' := keBₗ'.weakening Γaₗₜₚᵢₙwe (Γ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..)
      (Γ'' := .typeExt (.typeExt .empty ..) ..)
    let .qual (.mono ρlc) := ρke.TypeVarLocallyClosed_of
    apply qual keBₗ'' _ .star
    let aₗneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninΓ
    let aₗneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons aᵢninΓ
    let aₗneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₚninΓ
    let aₗneaₜ := List.ne_of_not_mem_cons aₜninΓ
    symm at aₗneaₙ aₗneaᵢ aₗneaₚ aₗneaₜ
    apply arr <| floor <| .var <| .typeExt aₗneaₙ <| .typeExt aₗneaᵢ <| .typeExt aₗneaₚ <|
      .typeExt aₗneaₜ .head
    rw [← Type.TypeVar_open_eq_Type_open_var, ← Type.TypeVar_open_eq_Type_open_var,
        Type.TypeVar_open_comm _ Nat.one_ne_zero (m := 1) (n := 0),
        Type.TypeVar_open_comm _ Nat.one_ne_zero (m := 1) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 2) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 2) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 3) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 3) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 4) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 4) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 5) (n := 0),
        Type.TypeVar_open_comm _ (Nat.succ_ne_zero _) (m := 5) (n := 0)]
    let τopaₚke := τke _ aₚninIₘ
      |>.weakening Γaₗₜₚwe (Γ' := .typeExt (.typeExt .empty ..) ..) (Γ'' := .typeExt .empty ..)
      |>.weakening Γaₗₜₚᵢₙwe (Γ' := .typeExt (.typeExt .empty ..) ..) (Γ'' := .empty)
    let Bopaₚlc := τopaₚke.soundness Γcw Γaₗₜₚᵢₙwe .star |>.TypeVarLocallyClosed_of
    let τopaᵢke := τke _ aᵢninIₘ
      |>.weakening Γaₗₜₚᵢwe (Γ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..) (Γ'' := .typeExt .empty ..)
      |>.weakening Γaₗₜₚᵢₙwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
    let Bopaᵢlc := τopaᵢke.soundness Γcw Γaₗₜₚᵢₙwe .star |>.TypeVarLocallyClosed_of
    rw [Bopaₚlc.weaken (n := 5).TypeVar_open_id, Bopaₚlc.weaken (n := 4).TypeVar_open_id,
        Bopaₚlc.weaken (n := 3).TypeVar_open_id, Bopaₚlc.weaken (n := 2).TypeVar_open_id,
        Bopaₚlc.weaken (n := 1).TypeVar_open_id, Bopaᵢlc.weaken (n := 5).TypeVar_open_id,
        Bopaᵢlc.weaken (n := 4).TypeVar_open_id, Bopaᵢlc.weaken (n := 3).TypeVar_open_id,
        Bopaᵢlc.weaken (n := 2).TypeVar_open_id, Bopaᵢlc.weaken (n := 1).TypeVar_open_id]
    exact arr τopaₚke τopaᵢke
  | splitP Mte splitce Mih splitih =>
    let ⟨_, .prod μke ρ₂ke⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    let ⟨_, splitke@(.split concatke)⟩ := splitce.to_Kinding Γcw Γᵢw Γwe
    let .concat _ liftke ρ₁ke ρ₂ke' κe contain₀ke contain₁ke := concatke
    let .lift I τopke κ₀e ρ₀ke := liftke
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨κeq, rfl⟩
    cases Kind.row.inj κeq
    let .prod _ rowke := σke
    generalize ξτseq : [_, _] = ξτs, κ?eq : none = κ? at rowke
    let .row ξ'ke _ τ'ke _ := rowke
    let length_eq : List.length [_, _] = List.length _ := by rw [ξτseq]
    rw [List.length_map, Range.length_toList, List.length_cons, List.length_singleton] at length_eq
    cases length_eq
    rw [← Range.map_get!_eq (as := [_, _]), List.length_cons, List.length_singleton] at ξτseq
    apply Typing.prodIntro' (Γwe.soundness Γcw) _ <| by
      rw [List.length_cons, List.length_singleton, List.length_map, Range.length_toList]
    intro EA mem
    conv => simp_match
    rw [Range.map, Range.toList, if_pos (Nat.succ_pos _), List.map_cons, Range.toList, Nat.zero_add,
        if_pos (Nat.lt_succ_self _), List.map_cons, Range.toList] at mem
    simp only at mem
    rw [if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_nil] at mem
    let Fty := splitih splitke Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Fty
    cases mem
    · case head =>
      simp only
      apply Typing.app _ <| Mih (.prod μke ρ₂ke) Γcw Γᵢw Γwe
      let πty := Fty.prodElim ⟨Nat.le.refl.step.step, Nat.le.refl.step, Nat.mod_one _⟩
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton,
          List.get!_cons_succ, List.get!_cons_succ, List.get!_cons_zero] at πty
      simp only at πty
      let .contain _ liftke' ρ₂ke'' κe' := contain₀ke
      rcases liftke.deterministic liftke' with ⟨κeq, rfl⟩
      rcases ρ₂ke.deterministic ρ₂ke'' with ⟨_, rfl⟩
      cases Kind.row.inj κeq
      cases κe'
      rw [← Range.map_get!_eq (as := [_, _])] at πty
      let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩
      rw [List.length_cons, List.length_singleton, List.get!_cons_zero] at π'ty
      simp only at π'ty
      have := π'ty.typeApp .id (B := [[λ a : *. a$0]])
      simp [Type.Type_open] at this
      rw [liftke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
          ρ₂ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
      let mem : 0 ∈ [0:2] := ⟨Nat.le.refl, Nat.two_pos, Nat.mod_one _⟩
      let τ'ke' := τ'ke _ mem
      simp only at τ'ke'
      rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτseq _ mem] at τ'ke'
      rw [List.get!_cons_zero] at τ'ke'
      simp only at τ'ke'
      rw [And.right <| τ'ke'.deterministic <| .prod μke liftke]
      exact .equiv this <| .arr (.prod .listAppIdL) <| .prod .listAppIdL
    · case tail mem' =>
      cases mem'
      case tail mem'' => nomatch mem''
      simp only
      apply Typing.app _ <| Mih (.prod μke ρ₂ke) Γcw Γᵢw Γwe
      let πty := Fty.prodElim ⟨Nat.le.refl.step.step.step, Nat.le.refl, Nat.mod_one _⟩
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton,
          List.get!_cons_succ, List.get!_cons_succ, List.get!_cons_succ, List.get!_cons_zero] at πty
      simp only at πty
      let .contain _ ρ₁ke' ρ₂ke'' κe' := contain₁ke
      rcases ρ₁ke.deterministic ρ₁ke' with ⟨κeq, rfl⟩
      rcases ρ₂ke.deterministic ρ₂ke'' with ⟨_, rfl⟩
      cases Kind.row.inj κeq
      cases κe'
      rw [← Range.map_get!_eq (as := [_, _])] at πty
      let π'ty := πty.prodElim ⟨Nat.le.refl, Nat.le.refl.step, Nat.mod_one _⟩
      rw [List.length_cons, List.length_singleton, List.get!_cons_zero] at π'ty
      simp only at π'ty
      have := π'ty.typeApp .id (B := [[λ a : *. a$0]])
      simp [Type.Type_open] at this
      rw [ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
          ρ₂ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
      let mem : 1 ∈ [0:2] := ⟨Nat.le.refl.step, Nat.one_lt_two, Nat.mod_one _⟩
      let τ'ke' := τ'ke _ mem
      simp only at τ'ke'
      rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτseq _ mem] at τ'ke'
      rw [List.get!_cons_succ, List.get!_cons_zero] at τ'ke'
      simp only at τ'ke'
      rw [And.right <| τ'ke'.deterministic <| .prod μke ρ₁ke]
      exact .equiv this <| .arr (.prod .listAppIdL) <| .prod .listAppIdL
  | splitS Mte Nte splitce τ₁ke Mih Nih splitih =>
    let ⟨_, arr₁ke@(.arr sum₁ke τ₁ke')⟩ := Nte.to_Kinding Γcw Γᵢw Γwe
    rcases τ₁ke.deterministic τ₁ke' with ⟨_, rfl⟩
    let .sum _ ρ₁ke := sum₁ke
    apply Typing.app _ <| Nih arr₁ke Γcw Γᵢw Γwe
    let ⟨_, arr₀ke@(.arr sum₀ke τ₁ke'')⟩ := Mte.to_Kinding Γcw Γᵢw Γwe
    let .sum _ ρ₀ke := sum₀ke
    rcases τ₁ke.deterministic τ₁ke'' with ⟨_, rfl⟩
    let .arr (.sum _ ρ₂ke) τ₁ke''' := σke
    rcases τ₁ke.deterministic τ₁ke''' with ⟨_, rfl⟩
    apply Typing.app _ <| Mih arr₀ke Γcw Γᵢw Γwe
    let ⟨_, splitke@(.split concatke)⟩ := splitce.to_Kinding Γcw Γᵢw Γwe
    let .concat _ ρ₀ke' ρ₁ke' ρ₂ke' κe .. := concatke
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨_, rfl⟩
    cases Kind.row.inj κeq
    cases κe
    let Fty := splitih splitke Γcw Γᵢw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl.step, Nat.le.refl.step.step, Nat.mod_one _⟩
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_singleton,
        List.get!_cons_succ, List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    let A₀lc := ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of
    let A₁lc := ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of
    let A₂lc := ρ₂ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of
    rw [A₀lc.weaken (n := 1).Type_open_id, A₁lc.weaken (n := 1).Type_open_id,
        A₂lc.weaken (n := 1).Type_open_id] at this
    have := this.typeApp (τ₁ke.soundness Γcw Γwe .star)
    simp [Type.Type_open] at this
    rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at this
    exact .equiv this <| .arr (.arr (.sum .listAppIdL) .refl) <|
      .arr (.arr (.sum .listAppIdL) .refl) <| .arr (.sum .listAppIdL) .refl

end Term.TypingAndElaboration

end TabularTypeInterpreter
