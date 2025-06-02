import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term
import TabularTypeInterpreter.Lemmas.ClassEnvironment
import TabularTypeInterpreter.Lemmas.TypeEnvironment
import TabularTypeInterpreter.Semantics.InstanceEnvironment
import TabularTypeInterpreter.Semantics.Term
import TabularTypeInterpreter.Theorems.Type

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

namespace Term.TypingAndElaboration

instance : Inhabited Monotype where
  default := .row [] none
in
instance : Inhabited «Type» where
  default := .list []
in
theorem to_Kinding (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : ∃ A, [[Γc; Γ ⊢ σ : * ⇝ A]] := by
  induction Mte generalizing Δ with
  | var xinΓ => exact Γwe.KindingAndElaboration_of_TermVarIn xinΓ
  | lam I _ τ₀ke ih =>
    rename TypeEnvironment => Γ
    let ⟨x, xnin⟩ := I ++ Γ.termVarDom |>.exists_fresh
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let ⟨_, τ₁ke⟩ := ih x xninI Γᵢw Γcw <| Γwe.termExt xninΓ τ₀ke
    exact ⟨_, τ₀ke.arr <| τ₁ke.TermVar_drop (Γ' := .empty)⟩
  | app _ _ ϕih τih =>
    let ⟨_, .arr _ τ₁ke⟩ := ϕih Γᵢw Γcw Γwe
    exact ⟨_, τ₁ke⟩
  | qualI I ψke _ ih =>
    rename TypeEnvironment => Γ
    let ⟨x, xnin⟩ := I ++ Γ.termVarDom |>.exists_fresh
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let ⟨_, γke⟩ := ih x xninI Γᵢw Γcw <| Γwe.constrExt xninΓ ψke
    exact ⟨_, ψke.qual (γke.Constr_drop (Γ' := .empty)) .star⟩
  | qualE _ _ γih =>
    let ⟨_, .qual _ γke _⟩ := γih Γᵢw Γcw Γwe
    exact ⟨_, γke⟩
  | schemeI I _ κe ih =>
    rename TypeScheme => σ'
    rename TypeEnvironment => Γ
    let ⟨a, anin⟩ := I ++ Γ.typeVarDom ++ σ'.freeTypeVars |>.exists_fresh
    let ⟨aninIΓ, aninσ'⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp aninIΓ
    let Γawe := Γwe.typeExt aninΓ κe
    let ⟨_, σ'ke⟩ := ih a aninI Γᵢw Γcw Γawe
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
    let ⟨_, σke⟩ := σih Γᵢw Γcw Γwe
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
    let ⟨_, σ₁ke⟩ := σ₁ih _ xninI Γᵢw Γcw <| Γwe.termExt xninΓ σ₀ke
    exact ⟨_, σ₁ke.TermVar_drop (Γ' := .empty)⟩
  | annot _ ih => exact ih Γᵢw Γcw Γwe
  | label => exact ⟨_, .floor .label⟩
  | prod _ _ ξih τih =>
    let ⟨_, .floor ξke⟩ := ξih Γᵢw Γcw Γwe
    let ⟨_, τke⟩ := τih Γᵢw Γcw Γwe
    exact ⟨_, .prod .comm (.singleton_row ξke τke)⟩
  | sum _ _ ξih τih =>
    let ⟨_, .floor ξke⟩ := ξih Γᵢw Γcw Γwe
    let ⟨_, τke⟩ := τih Γᵢw Γcw Γwe
    exact ⟨_, .sum .comm <| .singleton_row ξke τke⟩
  | unlabelProd _ _ prodih _ =>
    let ⟨_, .prod μke rowke⟩ := prodih Γᵢw Γcw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    exact ⟨_, τke⟩
  | unlabelSum _ _ _ sumih _ =>
    let ⟨_, .sum μke rowke⟩ := sumih Γᵢw Γcw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    exact ⟨_, τke⟩
  | «prj» _ containce prodke =>
    let ⟨_, .prod μke ρ₀ke⟩ := prodke Γᵢw Γcw Γwe
    let ⟨_, .contain _ ρ₁ke ρ₀ke' _⟩ := containce.to_Kinding Γᵢw Γcw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .prod μke ρ₁ke⟩
  | concat _ _ concatce prod₀ih =>
    let ⟨_, .prod μke ρ₀ke⟩ := prod₀ih Γᵢw Γcw Γwe
    let ⟨_, .concat _ ρ₀ke' _ ρ₂ke _ _ _⟩ := concatce.to_Kinding Γᵢw Γcw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .prod μke ρ₂ke⟩
  | «inj» _ containce sumih =>
    let ⟨_, .sum μke ρ₀ke⟩ := sumih Γᵢw Γcw Γwe
    let ⟨_, .contain _ ρ₀ke' ρ₁ke _⟩ := containce.to_Kinding Γᵢw Γcw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .sum μke ρ₁ke⟩
  | elim _ _ concatce τke sum₀ih =>
    let ⟨_, .arr (.sum μke ρ₀ke) _⟩ := sum₀ih Γᵢw Γcw Γwe
    let ⟨_, .concat _ ρ₀ke' _ ρ₂ke _ _ _⟩ := concatce.to_Kinding Γᵢw Γcw Γwe
    let ⟨κeq, _⟩ := ρ₀ke.deterministic ρ₀ke'
    cases Kind.row.inj κeq
    exact ⟨_, .arr (.sum μke ρ₂ke) τke⟩
  | sub _ τ₀₁ee ih =>
    let ⟨_, τ₀ke⟩ := ih Γᵢw Γcw Γwe
    let ⟨_, _, _, τ₀ke', τ₁ke⟩ := τ₀₁ee.to_Kinding Γcw Γwe
    rcases τ₀ke.deterministic τ₀ke' with ⟨rfl, _⟩
    exact ⟨_, τ₁ke⟩
  | member γcin TCτce =>
    rename TypeEnvironment => Γ
    rename Kind => κ
    rename TypeScheme => σ'
    rename «Type» => A
    let ⟨_, .tc γcin' τke⟩ := TCτce.to_Kinding Γᵢw Γcw Γwe
    rcases ClassEnvironmentEntry.mk.inj <| γcin.deterministic γcin' rfl with ⟨_, _, rfl, _⟩
    let ⟨_, κe, σ'ke, _⟩ := Γcw.In_inversion γcin
    let ⟨a, anin⟩ := Γ.typeVarDom ++ σ'.freeTypeVars ++ ↑A.freeTypeVars |>.exists_fresh
    let ⟨aninΓσ', aninA⟩ := List.not_mem_append'.mp anin
    let ⟨aninΓ, aninσ'⟩ := List.not_mem_append'.mp aninΓσ'
    let Γawe := Γwe.typeExt aninΓ κe
    rw [← Γ.empty_append] at Γawe
    let σ'ke' := σ'ke a |>.weakening Γawe (Γ' := Γ) (Γ'' := .typeExt .empty ..)
    rw [TypeEnvironment.empty_append] at Γawe σ'ke'
    exact ⟨_, σ'ke'.Monotype_open_preservation Γcw Γawe nofun aninσ' aninA τke (Γ' := .empty)⟩
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
  | splitP _ splitce prodih =>
    let ⟨_, .prod _ ρ₂ke⟩ := prodih Γᵢw Γcw Γwe
    let ⟨_, .split concatke⟩ := splitce.to_Kinding Γᵢw Γcw Γwe
    let .concat _ ρ₀ke ρ₁ke ρ₂ke' _ _ _ (A₀ := A₀) (A₁ := A₁) := concatke
    let ⟨κeq, _⟩ := ρ₂ke.deterministic ρ₂ke'
    cases Kind.row.inj κeq
    apply Exists.intro _
    apply TypeScheme.KindingAndElaboration.prod .comm
    have : none = Option.someIf Kind.star false := by rw [Option.someIf, if_neg nofun]
    rw [← Range.map_get!_eq (as := [_, _]), this]
    apply TypeScheme.KindingAndElaboration.row
      (A := fun | 0 => A₀.prod | 1 => A₁.prod | _ => default) _ _ _ <|
      .inl <| by
        rw [List.length_cons, List.length_singleton]
        exact Nat.succ_ne_zero _
    · exact fun _ => [[⊗ { }]]
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
        exact .prod .comm ρ₀ke
      | 1 =>
        rw [List.get!_cons_succ, List.get!_cons_zero]
        exact .prod .comm ρ₁ke
  | splitS _ _ splitce _ _ arrρ₁ih =>
    let ⟨_, .arr (.sum _ ρ₁ke) τ₁ke⟩ := arrρ₁ih Γᵢw Γcw Γwe
    let ⟨_, .split concatke⟩ := splitce.to_Kinding Γᵢw Γcw Γwe
    let .concat _ _ ρ₁ke' ρ₂ke .. := concatke
    let ⟨κeq, _⟩ := ρ₁ke.deterministic ρ₁ke'
    cases Kind.row.inj κeq
    exact ⟨_, .arr (.sum .comm ρ₂ke) τ₁ke⟩

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

theorem soundness (Mte : [[Γᵢ; Γc; Γ ⊢ M : σ ⇝ E]]) (σke : [[Γc; Γ ⊢ σ : * ⇝ A]])
  (Γᵢw : [[Γc ⊢ Γᵢ]]) (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : [[Δ ⊢ E : A]] := by
  induction Mte generalizing Δ A with
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
    exact ih _ xninI τ₁ke' Γᵢw Γcw Γxwe
  | app Mte _ Mih Nih =>
    let ⟨_, arrke@(.arr τ₀ke τ₁ke)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    rcases σke.deterministic τ₁ke with ⟨_, rfl⟩
    exact .app (Mih arrke Γᵢw Γcw Γwe) (Nih τ₀ke Γᵢw Γcw Γwe)
  | qualI I ψke _ ih =>
    let .qual ψke' γke κe := σke
    rcases ψke.deterministic ψke' with ⟨_, rfl⟩
    rename TypeEnvironment => Γ
    apply Typing.lam <| I ++ Γ.termVarDom
    intro x xnin
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let Γxwe := Γwe.constrExt xninΓ ψke
    let γke' := γke.weakening Γxwe (Γ' := .constrExt .empty ..) (Γ'' := .empty)
    exact ih _ xninI γke' Γᵢw Γcw Γxwe
  | qualE ψce Mte qualih =>
    let ⟨_, qualke@(.qual ψke γke _)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    rcases σke.deterministic γke with ⟨_, rfl⟩
    exact .app (qualih qualke Γᵢw Γcw Γwe) (ψce.soundness ψke Γᵢw Γcw Γwe)
  | schemeI I _ κe ih =>
    let .scheme I' σ'ke κe' := σke
    cases κe.deterministic κe'
    rename TypeEnvironment => Γ
    apply Typing.typeLam <| I ++ I' ++ Γ.typeVarDom
    intro a anin
    let ⟨aninII', aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    exact ih _ aninI (σ'ke _ aninI') Γᵢw Γcw (Γwe.typeExt aninΓ κe)
  | schemeE Mte τke ih =>
    let ⟨_, schemeke@(.scheme I σ'ke κ₀e)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
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
    exact .typeApp (ih schemeke Γᵢw Γcw Γwe) (τke.soundness Γcw Γwe κ₀e)
  | «let» I Mte σ₀ke Nte Mih Nih =>
    apply Typing.app _ <| Mih σ₀ke Γᵢw Γcw Γwe
    rename TypeEnvironment => Γ
    apply Typing.lam <| I ++ Γ.termVarDom
    intro x xnin
    let ⟨xninI, xninΓ⟩ := List.not_mem_append'.mp xnin
    let Γxwe := Γwe.termExt xninΓ σ₀ke
    let σ₁ke := σke.weakening Γxwe (Γ' := .termExt .empty ..) (Γ'' := .empty)
    exact Nih _ xninI σ₁ke Γᵢw Γcw Γxwe
  | annot _ ih => exact ih σke Γᵢw Γcw Γwe
  | label =>
    let .floor _ := σke
    exact .prodIntro' (Γwe.soundness Γcw) nofun rfl
  | prod _ _ _ ih =>
    let .prod _ rowke := σke
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    exact .singleton <| ih τke Γᵢw Γcw Γwe
  | sum _ _ _ ih =>
    let .sum _ rowke := σke
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    rw [← Range.map_get!_eq (as := [_]), List.length_singleton]
    let mem : 0 ∈ [0:1] := ⟨Nat.le.refl, Nat.one_pos, Nat.mod_one _⟩
    apply Typing.sumIntro mem <| ih τke Γᵢw Γcw Γwe
    intro i mem
    let 0 := i
    rw [List.get!_cons_zero]
    exact τke.soundness Γcw Γwe .star
  | unlabelProd Mte _ ih =>
    let ⟨_, prodke@(.prod _ rowke)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke⟩
    cases Kind.row.inj κeq
    rcases σke.deterministic τke with ⟨_, rfl⟩
    apply Typing.prodElim _ ⟨Nat.le.refl, Nat.one_pos, Nat.mod_one _⟩ (A := fun _ => A)
    rw [Range.map, Range.toList, if_pos Nat.one_pos, Range.toList, Nat.zero_add,
        if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_singleton]
    exact ih prodke Γᵢw Γcw Γwe
  | unlabelSum Mte _ τke ih =>
    let ⟨_, sumke@(.sum _ rowke)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    rcases rowke.singleton_row_inversion with ⟨_, _, κeq, _, rfl, τke'⟩
    cases Kind.row.inj κeq
    rcases σke.deterministic τke with ⟨_, rfl⟩
    rcases σke.deterministic τke' with ⟨_, rfl⟩
    apply Typing.sumElim' (ih sumke Γᵢw Γcw Γwe) _ (τke.soundness Γcw Γwe .star) <| by
      rw [List.length_singleton, List.length_singleton]
    intro _ mem
    rw [List.zip_cons_cons, List.zip_nil_left] at mem
    cases List.mem_singleton.mp mem
    conv => simp_match
    exact .id (Γwe.soundness Γcw) <| τke.soundness Γcw Γwe .star
  | «prj» Mte containce Mih =>
    let ⟨_, prodke@(.prod μke ρ₀ke)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    apply Typing.app _ <| Mih prodke Γᵢw Γcw Γwe
    let .prod _ ρ₁ke := σke
    let Fty := containce.soundness (.contain μke ρ₁ke ρ₀ke .star) Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl, Nat.two_pos, Nat.mod_one _⟩
    rw [List.length_cons, List.length_singleton, List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv this <| .arr (.prod <| .listAppId sorry) (.prod <| .listAppId sorry)   -- TODO lc
  | concat Mte Nte concatce Mih Nih =>
    let ⟨_, prod₀ke⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    let ⟨_, prod₁ke⟩ := Nte.to_Kinding Γᵢw Γcw Γwe
    apply Typing.app _ <| Nih prod₁ke Γᵢw Γcw Γwe
    apply Typing.app _ <| Mih prod₀ke Γᵢw Γcw Γwe
    let .prod μke ρ₀ke := prod₀ke
    let .prod _ ρ₁ke := prod₁ke
    let .prod _ ρ₂ke := σke
    let Fty := concatce.soundness (.concat μke ρ₀ke ρ₁ke ρ₂ke .star (.contain μke ρ₀ke ρ₂ke .star)
      (.contain μke ρ₁ke ρ₂ke .star)) Γᵢw Γcw Γwe
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
    exact .equiv this <| .arr (.prod <| .listAppId sorry) (.arr (.prod <| .listAppId sorry) (.prod <| .listAppId sorry))  -- TODO lc
  | «inj» Mte containce Mih =>
    let ⟨_, sumke@(.sum μke ρ₀ke)⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    apply Typing.app _ <| Mih sumke Γᵢw Γcw Γwe
    let .sum _ ρ₁ke := σke
    let Fty := containce.soundness (.contain μke ρ₀ke ρ₁ke .star) Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _])] at Fty
    let πty := Fty.prodElim ⟨Nat.le.refl.step, Nat.le.refl, Nat.mod_one _⟩
    rw [List.length_cons, List.length_singleton, List.get!_cons_succ, List.get!_cons_zero] at πty
    simp only at πty
    have := πty.typeApp .id (B := [[λ a : *. a$0]])
    simp [Type.Type_open] at this
    rw [ρ₀ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γcw Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv this <| .arr (.sum <| .listAppId sorry) (.sum <| .listAppId sorry)   -- TODO lc
  | elim Mte Nte concatce τke Mih Nih =>
    let ⟨_, arr₀ke⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    let ⟨_, arr₁ke⟩ := Nte.to_Kinding Γᵢw Γcw Γwe
    apply Typing.app _ <| Nih arr₁ke Γᵢw Γcw Γwe
    apply Typing.app _ <| Mih arr₀ke Γᵢw Γcw Γwe
    let .arr (.sum μke ρ₀ke) τke' := arr₀ke
    rcases τke.deterministic τke' with ⟨_, rfl⟩
    let .arr (.sum _ ρ₁ke) τke'' := arr₁ke
    rcases τke.deterministic τke'' with ⟨_, rfl⟩
    let .arr (.sum _ ρ₂ke) τke''' := σke
    rcases τke.deterministic τke''' with ⟨_, rfl⟩
    let Fty := concatce.soundness (.concat μke ρ₀ke ρ₁ke ρ₂ke .star (.contain μke ρ₀ke ρ₂ke .star)
      (.contain μke ρ₁ke ρ₂ke .star)) Γᵢw Γcw Γwe
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
    exact .equiv this <| .arr (.arr (.sum <| .listAppId sorry) .refl) <|
      .arr (.arr (.sum <| .listAppId sorry) .refl) <| .arr (.sum <| .listAppId sorry) .refl   -- TODO lc
  | sub Mte τse ih =>
    let ⟨_, τ₀ke⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    let ⟨_, _, _, τ₀ke', τ₁ke⟩ := τse.to_Kinding Γcw Γwe
    rcases τ₀ke.deterministic τ₀ke' with ⟨rfl, rfl⟩
    rcases σke.deterministic τ₁ke with ⟨_, rfl⟩
    exact .app (τse.soundness Γcw Γwe τ₀ke τ₁ke .star) (ih τ₀ke Γᵢw Γcw Γwe)
  | member γcin TCce =>
    rename_i A' _ _ _ _ _ _
    let ⟨_, TCke@(.tc γcin' τke)⟩ := TCce.to_Kinding Γᵢw Γcw Γwe
    rcases ClassEnvironmentEntry.mk.inj <| γcin.deterministic γcin' rfl
      with ⟨_, _, rfl, rfl, rfl, rfl⟩
    rcases Γcw.In_inversion γcin with ⟨_, κe, σ'ke, Aki, TCₛke, Aₛki⟩
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
    let Ety := TCce.soundness TCke Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := _ :: _)] at Ety
    let πty := Ety.prodElim
      ⟨Nat.le.refl, by rw [List.length_cons]; exact Nat.succ_pos _, Nat.mod_one _⟩
    rw [List.length_cons, List.length_map, Range.length_toList, Nat.sub_zero,
        List.get!_cons_zero] at πty
    simp only at πty
    exact πty
  | «ind» Iₘ Iₛ ρke τke κe Mte Nte indce Mih Nih =>
    rename_i Γc Γ ρ κ τ B K _ _ _ _ _ _
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
    apply Typing.app _ <| Nih τopemptyke Γᵢw Γcw Γwe
    let ⟨_, indke@(.ind I₀ I₁ ρke' κe' keBₗ keBᵣ)⟩ := indce.to_Kinding Γᵢw Γcw Γwe
    rename_i Bₗ Bᵣ _ _ _
    rcases ρke.deterministic ρke' with ⟨κeq, rfl⟩
    cases Kind.row.inj κeq
    cases κe.deterministic κe'
    let Fty := indce.soundness indke Γᵢw Γcw Γwe
    have := Fty.typeApp <| .lam (Iₘ ++ Γ.typeVarDom) fun a anin =>
      let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp anin
      τke a aninI |>.soundness Γcw (Γwe.typeExt aninΓ κe.row) .star
    simp [Type.Type_open] at this
    rw [ρke.soundness Γcw Γwe κe.row |>.TypeVarLocallyClosed_of.Type_open_id] at this
    apply Typing.app <| this.equiv <| .arr .refl <| .arr (.lamApp sorry) (.lamApp sorry) -- TODO kinding
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
      ↑aᵢ :: I₁ ++ ↑aᵢ :: ↑aₚ :: ↑aₜ :: ↑aₗ :: Iₛ
    intro aₙ aₙnin
    let ⟨aₙninΓΓ'I₁, aₙninIₛ⟩ := List.not_mem_append'.mp aₙnin
    let ⟨aₙninΓΓ', aₙninI₁⟩ := List.not_mem_append'.mp aₙninΓΓ'I₁
    let ⟨aₙninΓ, aₙninΓ'⟩ := List.not_mem_append'.mp aₙninΓΓ'
    simp [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open]
    let Γaₗₜₚᵢwe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
      |>.typeExt aᵢninΓ κe.row
    let Γaₗₜₚᵢₙwe := Γaₗₜₚᵢwe.typeExt aₙninΓ κe.row
    apply Typing.equiv _ <| .arr .refl <| .arr .refl <| .arr .refl <| .arr (.symm <| .lamApp sorry) (.symm <| .lamApp sorry)  -- TODO kinding
    apply Mih _ aₗninIₛ _ aₜninIₛ _ aₚninIₛ _ aᵢninIₛ _ aₙninIₛ _ Γᵢw Γcw Γaₗₜₚᵢₙwe
    open TypeScheme.KindingAndElaboration in
    let keBₗ' := keBₗ _ aₗninI₀ _ aₜninI₀ _ aₚninI₀ _ aᵢninI₀
    let Γaₗₜₚwe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κe |>.typeExt aₚninΓ κe.row
    let Γaₗₜₚᵢwe := Γaₗₜₚwe.typeExt aᵢninΓ κe.row
    let Γaₗₜₚᵢₙwe := Γaₗₜₚᵢwe.typeExt aₙninΓ κe.row
    let Bₗlc := keBₗ'.soundness Γcw Γaₗₜₚᵢwe .constr |>.TypeVarLocallyClosed_of.weaken (n := 5)
      |>.TypeVar_open_drop Nat.le.refl.step.step.step
      |>.TypeVar_open_drop Nat.le.refl.step.step
      |>.TypeVar_open_drop Nat.le.refl.step
      |>.TypeVar_open_drop Nat.le.refl
    let keBᵣ' := keBᵣ _ aᵢninI₁ _ aₙninI₁
    let Γaᵢₙwe := Γwe.typeExt aᵢninΓ' κe.row |>.typeExt aₙninΓ' κe.row
    let Bᵣlc := keBᵣ'.soundness Γcw Γaᵢₙwe .constr |>.TypeVarLocallyClosed_of.weaken (n := 2)
      |>.TypeVar_open_drop Nat.le.refl.step
      |>.TypeVar_open_drop Nat.le.refl
    rw [Bₗlc.Type_open_id, Bᵣlc.weaken (n := 3).Type_open_id] at this ⊢
    rw [Bᵣlc.weaken (n := 2).TypeVar_open_id, Bᵣlc.weaken (n := 1).TypeVar_open_id,
        Bᵣlc.TypeVar_open_id]
    let keBₗ'' := keBₗ'.weakening Γaₗₜₚᵢₙwe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
    rw [keBₗ''.soundness Γcw Γaₗₜₚᵢₙwe .constr |>.TypeVarLocallyClosed_of.TypeVar_open_id]
    apply qual keBₗ'' _ .star
    let keBᵣ'' := keBᵣ'.weakening Γaₗₜₚᵢₙwe (Γ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..)
      (Γ'' := .typeExt (.typeExt .empty ..) ..)
    let .qual (.mono ρlc) := ρke.TypeVarLocallyClosed_of
    apply qual keBᵣ'' _ .star
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
  | splitP Mte splitce Mih =>
    let ⟨_, .prod _ ρ₂ke⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    let ⟨_, splitke@(.split concatke)⟩ := splitce.to_Kinding Γᵢw Γcw Γwe
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
    let Fty := splitce.soundness splitke Γᵢw Γcw Γwe
    rw [← Range.map_get!_eq (as := [_, _, _, _])] at Fty
    cases mem
    · case head =>
      simp only
      apply Typing.app _ <| Mih (.prod .comm ρ₂ke) Γᵢw Γcw Γwe
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
      rw [And.right <| τ'ke'.deterministic <| .prod .comm liftke]
      exact .equiv this <| .arr (.prod <| .listAppId sorry) <| .prod <| .listAppId sorry  -- TODO lc
    · case tail mem' =>
      cases mem'
      case tail mem'' => nomatch mem''
      simp only
      apply Typing.app _ <| Mih (.prod .comm ρ₂ke) Γᵢw Γcw Γwe
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
      rw [And.right <| τ'ke'.deterministic <| .prod .comm ρ₁ke]
      exact .equiv this <| .arr (.prod <| .listAppId sorry) <| .prod <| .listAppId sorry  -- TODO lc
  | splitS Mte Nte splitce τ₁ke Mih Nih =>
    let ⟨_, arr₁ke@(.arr sum₁ke τ₁ke')⟩ := Nte.to_Kinding Γᵢw Γcw Γwe
    rcases τ₁ke.deterministic τ₁ke' with ⟨_, rfl⟩
    let .sum _ ρ₁ke := sum₁ke
    apply Typing.app _ <| Nih arr₁ke Γᵢw Γcw Γwe
    let ⟨_, arr₀ke@(.arr sum₀ke τ₁ke'')⟩ := Mte.to_Kinding Γᵢw Γcw Γwe
    let .sum _ ρ₀ke := sum₀ke
    rcases τ₁ke.deterministic τ₁ke'' with ⟨_, rfl⟩
    let .arr (.sum _ ρ₂ke) τ₁ke''' := σke
    rcases τ₁ke.deterministic τ₁ke''' with ⟨_, rfl⟩
    apply Typing.app _ <| Mih arr₀ke Γᵢw Γcw Γwe
    let ⟨_, splitke@(.split concatke)⟩ := splitce.to_Kinding Γᵢw Γcw Γwe
    let .concat _ ρ₀ke' ρ₁ke' ρ₂ke' κe .. := concatke
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    rcases ρ₁ke.deterministic ρ₁ke' with ⟨_, rfl⟩
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨_, rfl⟩
    cases Kind.row.inj κeq
    cases κe
    let Fty := splitce.soundness splitke Γᵢw Γcw Γwe
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
    exact .equiv this <| .arr (.arr (.sum <| .listAppId sorry) .refl) <|
      .arr (.arr (.sum <| .listAppId sorry) .refl) <| .arr (.sum <| .listAppId sorry) .refl   -- TODO lc

end Term.TypingAndElaboration

end TabularTypeInterpreter
