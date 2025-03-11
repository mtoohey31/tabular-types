import Aesop
import TabularTypeInterpreter.Lemmas.TypeEnvironment.Basic
import TabularTypeInterpreter.Semantics.Type

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

namespace Monotype

@[elab_as_elim]
def rec_uniform {motive : Monotype → Prop} (var : ∀ a, motive (.var a))
  (app : ∀ φ τ, motive φ → motive τ → motive (.app φ τ))
  (arr : ∀ τ₀ τ₁, motive τ₀ → motive τ₁ → motive (.arr τ₀ τ₁)) (label : ∀ ℓ, motive (.label ℓ))
  (floor : ∀ ξ, motive ξ → motive (.floor ξ)) (comm : ∀ u, motive (.comm u))
  (row : ∀ ξτs κ?, (∀ ξτ ∈ ξτs, motive ξτ.fst ∧ motive ξτ.snd) → motive (.row ξτs κ?))
  (prodOrSum : ∀ Ξ μ ρ, motive μ → motive ρ → motive (.prodOrSum Ξ μ ρ))
  (lift : ∀ κ τ ρ, motive τ → motive ρ → motive (.lift (.mk κ τ) ρ))
  (contain : ∀ ρ₀ μ ρ₁, motive ρ₀ → motive μ → motive ρ₁ → motive (.contain ρ₀ μ ρ₁))
  (concat : ∀ ρ₀ μ ρ₁ ρ₂, motive ρ₀ → motive μ → motive ρ₁ → motive ρ₂ → motive (.concat ρ₀ μ ρ₁ ρ₂))
  (typeClass : ∀ TC τ, motive τ → motive (.typeClass TC τ))
  (all : ∀ κ ψ ρ, motive ψ → motive ρ → motive (.all (.mk κ ψ) ρ))
  («ind» : ∀ ρ, motive ρ → motive (.ind ρ))
  (split : ∀ κ τ ρ₀ ρ₁ ρ₂, motive τ → motive ρ₀ → motive ρ₁ → motive ρ₂ → motive (.split (.mk κ τ) ρ₀ ρ₁ ρ₂))
  (τ : Monotype) : motive τ :=
  Monotype.rec (motive_1 := fun | .mk _ τ => motive τ) (motive_2 := motive)
    (motive_3 := fun τss => ∀ τs ∈ τss, motive τs.fst ∧ motive τs.snd)
    (motive_4 := fun τs => motive τs.fst ∧ motive τs.snd) (fun _ _ mτ => mτ) var app arr label
    floor comm row prodOrSum (fun | .mk κ τ, ρ, mτ, mρ => lift κ τ ρ mτ mρ) contain concat typeClass
    (fun | .mk κ τ, ρ, mτ, mρ => all κ τ ρ mτ mρ) «ind»
    (fun | .mk κ τ, ρ₀, ρ₁, ρ₂, mτ, mρ₀, mρ₁, mρ₂ => split κ τ ρ₀ ρ₁ ρ₂ mτ mρ₀ mρ₁ mρ₂) nofun
    (fun _ _ mhead mtail _ mem => match mem with | .head _ => mhead | .tail _ mem' => mtail _ mem') (fun _ _ mτ₀ mτ₁ => ⟨mτ₀, mτ₁⟩) τ

@[simp]
theorem TypeVar_open_sizeOf (τ : Monotype) : sizeOf (τ.TypeVar_open a n) = sizeOf τ := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    rw [TypeVar_open, List.mapMem_eq_map, row.sizeOf_spec, row.sizeOf_spec,
        List.sizeOf_map_eq_of_eq_id_of_mem]
    intro ξτ mem
    let (ξ, τ) := ξτ
    rw [Prod.mk.sizeOf_spec, Prod.mk.sizeOf_spec, ih _ mem |>.left, ih _ mem |>.right]
  all_goals aesop
    (add simp [TypeVar_open, TypeLambda.TypeVar_open, var.sizeOf_spec, app.sizeOf_spec,
      arr.sizeOf_spec, floor.sizeOf_spec, comm.sizeOf_spec, row.sizeOf_spec, prodOrSum.sizeOf_spec,
      lift.sizeOf_spec, contain.sizeOf_spec, concat.sizeOf_spec,
      typeClass.sizeOf_spec, all.sizeOf_spec, ind.sizeOf_spec, split.sizeOf_spec,
      TypeLambda.mk.sizeOf_spec])

@[simp]
theorem TypeVar_open_sizeOf' (τ : Monotype) : (τ.TypeVar_open a n).sizeOf' = τ.sizeOf' := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    rw [TypeVar_open, List.mapMem_eq_map, sizeOf', List.mapMem_eq_map, sizeOf', List.mapMem_eq_map,
        List.map_map, List.sum_map_eq_of_eq_of_mem]
    intro ξτ mem
    rw [Function.comp, ih _ mem |>.left, ih _ mem |>.right]
  all_goals aesop
    (add simp [TypeVar_open, TypeLambda.TypeVar_open, sizeOf', TypeLambda.sizeOf'])

@[simp]
theorem TypeVar_close_sizeOf' (τ : Monotype) : (τ.TypeVar_close a n).sizeOf' = τ.sizeOf' := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    rw [TypeVar_close, List.mapMem_eq_map, sizeOf', List.mapMem_eq_map, sizeOf', List.mapMem_eq_map,
        List.map_map, List.sum_map_eq_of_eq_of_mem]
    intro ξτ mem
    rw [Function.comp, ih _ mem |>.left, ih _ mem |>.right]
  all_goals aesop
    (add simp [TypeVar_close, TypeLambda.TypeVar_close, sizeOf', TypeLambda.sizeOf'])

@[simp]
theorem sizeOf_pos (τ : Monotype) : 0 < sizeOf τ := by cases τ <;> simp_arith

@[simp]
theorem sizeOf'_pos (τ : Monotype) : 0 < τ.sizeOf' := by cases τ <;> simp_arith [sizeOf']

theorem TypeVar_open_comm (τ : Monotype)
  : m ≠ n → (τ.TypeVar_open a m).TypeVar_open a' n = (τ.TypeVar_open a' n).TypeVar_open a m := by
  induction τ using rec_uniform generalizing m n
  case row ih =>
    intro mnen
    rw [TypeVar_open, TypeVar_open, TypeVar_open, TypeVar_open, List.mapMem_eq_map,
        List.mapMem_eq_map, List.mapMem_eq_map, List.mapMem_eq_map, List.map_map, List.map_map]
    apply row.injEq .. |>.mpr ⟨_, rfl⟩
    apply List.map_eq_map_iff.mpr
    intro _ mem
    simp
    exact ⟨ih _ mem |>.left mnen, ih _ mem |>.right mnen⟩
  all_goals aesop (add simp [TypeVar_open, TypeLambda.TypeVar_open])

theorem TypeVar_open_eq_Monotype_open_var : TypeVar_open τ a n = τ.Monotype_open (.var a) n := by
  induction τ using rec_uniform generalizing n
  case row _ _ ih =>
    rw [TypeVar_open, Monotype_open, List.mapMem_eq_map, List.mapMem_eq_map]
    apply row.injEq .. |>.mpr ⟨_, rfl⟩
    apply List.map_eq_map_iff.mpr
    intro ξτ mem
    rw [ih ξτ mem |>.left, ih ξτ mem |>.right]
  all_goals aesop
    (add simp [TypeVar_open, Monotype_open, TypeLambda.TypeVar_open, TypeLambda.Monotype_open])

namespace TypeVarLocallyClosed

theorem weakening (τlc : TypeVarLocallyClosed τ m) : TypeVarLocallyClosed τ (m + n) := by
  induction τlc using rec
    (motive_1 := fun | .mk κ τ, m, _ => τ.TypeVarLocallyClosed (m + n + 1)) <;> aesop
      (simp_config := { arith := true }) (add safe constructors TypeVarLocallyClosed,
        safe constructors TypeLambda.TypeVarLocallyClosed, 20% [of_eq, Nat.lt_add_right])
where
  of_eq {τ m n} (τlc : TypeVarLocallyClosed τ m) (eq : m = n) : τ.TypeVarLocallyClosed n := by
    rwa [eq] at τlc

theorem TypeVar_open_id : TypeVarLocallyClosed τ n → τ.TypeVar_open a n = τ := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    intro rowlc
    let .row ξslc τslc := rowlc
    rw [TypeVar_open, List.mapMem_eq_map]
    congr
    apply List.map_eq_id_of_eq_id_of_mem
    intro _ mem
    let ξlc := ξslc _ mem
    conv at ξlc => simp_match
    let τlc := τslc _ mem
    conv at τlc => simp_match
    congr
    · exact ih _ mem |>.left ξlc
    · exact ih _ mem |>.right τlc
  all_goals aesop
    (add simp [TypeVar_open, TypeLambda.TypeVar_open], 50% cases TypeVarLocallyClosed,
      safe cases TypeLambda.TypeVarLocallyClosed)

theorem TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed τ n → (τ.TypeVar_close a n).TypeVar_open a n = τ := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    intro rowlc
    let .row ξslc τslc := rowlc
    rw [TypeVar_close, List.mapMem_eq_map, TypeVar_open, List.mapMem_eq_map, List.map_map]
    congr
    apply List.map_eq_id_of_eq_id_of_mem
    intro _ mem
    let ξlc := ξslc _ mem
    conv at ξlc => simp_match
    let τlc := τslc _ mem
    conv at τlc => simp_match
    simp
    congr
    · exact ih _ mem |>.left ξlc
    · exact ih _ mem |>.right τlc
  all_goals aesop
    (add simp [TypeVar_open, TypeVar_close, TypeLambda.TypeVar_open, TypeLambda.TypeVar_close],
      50% cases TypeVarLocallyClosed, safe cases TypeLambda.TypeVarLocallyClosed)

theorem TypeVar_open_drop
  : m < n → (TypeVar_open τ a m).TypeVarLocallyClosed n → TypeVarLocallyClosed τ n := by
  induction τ using rec_uniform generalizing m n
  case row ih =>
    intro mltn rowoplc
    rw [TypeVar_open, List.mapMem_eq_map] at rowoplc
    let .row ξopslc τopslc := rowoplc
    apply row
    · intro _ mem
      let ξoplc := ξopslc _ <| List.mem_map.mpr ⟨_, mem, rfl⟩
      conv at ξoplc => simp_match
      exact ih _ mem |>.left mltn ξoplc
    · intro _ mem
      let τoplc := τopslc _ <| List.mem_map.mpr ⟨_, mem, rfl⟩
      conv at τoplc => simp_match
      exact ih _ mem |>.right mltn τoplc
  all_goals aesop
    (add simp [TypeVar_open, TypeLambda.TypeVar_open], safe cases TypeVarLocallyClosed,
      safe cases TypeLambda.TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed,
      safe constructors TypeLambda.TypeVarLocallyClosed)

theorem Monotype_open_TypeVar_close_eq_TypeVar_subst (τlc : TypeVarLocallyClosed τ n)
  : (τ.TypeVar_close a n).Monotype_open τ' n = τ.TypeVar_subst a τ' := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    let .row ξslc τslc := τlc
    rw [TypeVar_close, List.mapMem_eq_map, Monotype_open, List.mapMem_eq_map, List.map_map,
        TypeVar_subst, List.mapMem_eq_map]
    apply row.injEq .. |>.mpr ⟨_, rfl⟩
    apply List.map_eq_map_iff.mpr
    intro _ mem
    let ξlc := ξslc _ mem
    conv at ξlc => simp_match
    let τlc := τslc _ mem
    conv at τlc => simp_match
    simp
    exact ⟨ih _ mem |>.left ξlc, ih _ mem |>.right τlc⟩
  case lift ih₀ ih₁ =>
    let .lift (.mk τ'lc) ρke := τlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst, TypeLambda.TypeVar_close,
        TypeLambda.Monotype_open, TypeLambda.TypeVar_subst, ih₀ τ'lc, ih₁ ρke]
  case all ih₀ ih₁ =>
    let .all (.mk ψlc) ρke := τlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst, TypeLambda.TypeVar_close,
        TypeLambda.Monotype_open, TypeLambda.TypeVar_subst, ih₀ ψlc, ih₁ ρke]
  case split ih₀ ih₁ ih₂ ih₃ =>
    let .split (.mk τ'lc) ρ₀ke ρ₁ke ρ₂ke := τlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst, TypeLambda.TypeVar_close,
        TypeLambda.Monotype_open, TypeLambda.TypeVar_subst, ih₀ τ'lc, ih₁ ρ₀ke, ih₂ ρ₁ke, ih₃ ρ₂ke]
  all_goals aesop
    (add simp [TypeVar_close, Monotype_open, TypeVar_subst], safe cases TypeVarLocallyClosed)

end TypeVarLocallyClosed

theorem TypeVar_open_Monotype_open_comm (τ : Monotype) {τ'} : TypeVarLocallyClosed τ' m → m ≠ n →
    (τ.TypeVar_open a m).Monotype_open τ' n = (τ.Monotype_open τ' n).TypeVar_open a m := by
  induction τ using rec_uniform generalizing m n
  case row ih =>
    intro τ'lc mnen
    rw [TypeVar_open, List.mapMem_eq_map, Monotype_open, List.mapMem_eq_map, List.map_map,
        Monotype_open, List.mapMem_eq_map, TypeVar_open, List.mapMem_eq_map, List.map_map]
    apply row.injEq .. |>.mpr ⟨_, rfl⟩
    apply List.map_eq_map_iff.mpr
    intro _ mem
    simp
    exact ⟨ih _ mem |>.left τ'lc mnen, ih _ mem |>.right τ'lc mnen⟩
  all_goals aesop
    (add simp [TypeVar_open, Monotype_open, TypeLambda.TypeVar_open, TypeLambda.Monotype_open],
      20% [TypeVarLocallyClosed.TypeVar_open_id, Eq.symm, TypeVarLocallyClosed.weakening])

theorem not_mem_freeTypeVars_TypeVar_open_intro
  : a ∉ freeTypeVars τ → a ≠ a' → a ∉ (τ.TypeVar_open a' n).freeTypeVars := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    intro anin ne
    rw [TypeVar_open, freeTypeVars]
    simp [Function.comp]
    intro I ξ τ mem eq
    cases eq
    have := ih (ξ, τ) mem
    rw [freeTypeVars, List.mapMem_eq_map] at anin
    let ⟨xninξ, xninτ⟩ := List.not_mem_append'.mp <|
      List.not_mem_flatten.mp anin (ξ.freeTypeVars ++ τ.freeTypeVars) <|
      List.mem_map.mpr ⟨(ξ, τ), mem, rfl⟩
    exact List.not_mem_append'.mpr ⟨this.left xninξ ne, this.right xninτ ne⟩
  all_goals aesop
    (add simp [TypeVar_open, TypeLambda.TypeVar_open, freeTypeVars, TypeLambda.freeTypeVars])

theorem not_mem_freeTypeVars_TypeVar_close : a ∉ (TypeVar_close τ a n).freeTypeVars := by
  induction τ using rec_uniform generalizing n
  case row ih =>
    rw [TypeVar_close, List.mapMem_eq_map, freeTypeVars, List.mapMem_eq_map, List.map_map]
    apply List.not_mem_flatten.mpr
    intro ξτfreeTypeVars mem
    rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
    simp only [Function.comp]
    apply List.not_mem_append'.mpr
    exact ⟨ih _ mem' |>.left, ih _ mem' |>.right⟩
  all_goals aesop
    (add simp [TypeVar_close, freeTypeVars, TypeLambda.TypeVar_close, TypeLambda.freeTypeVars],
      safe cases TypeVar)

end Monotype

namespace QualifiedType

@[simp]
theorem sizeOf_pos (γ : QualifiedType) : 0 < sizeOf γ := by cases γ <;> simp_arith

@[simp]
theorem TypeVar_open_sizeOf (γ : QualifiedType) : sizeOf (γ.TypeVar_open a n) = sizeOf γ := by
  match γ with
  | .mono τ => rw [TypeVar_open, mono.sizeOf_spec, mono.sizeOf_spec, τ.TypeVar_open_sizeOf]
  | .qual ψ γ =>
    rw [TypeVar_open, qual.sizeOf_spec, qual.sizeOf_spec, ψ.TypeVar_open_sizeOf,
        γ.TypeVar_open_sizeOf]

@[simp]
theorem sizeOf'_pos (γ : QualifiedType) : 0 < γ.sizeOf' := by cases γ <;> simp_arith [sizeOf']

@[simp]
theorem TypeVar_open_sizeOf' (γ : QualifiedType) : (γ.TypeVar_open a n).sizeOf' = γ.sizeOf' := by
  match γ with
  | .mono τ => rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']
  | .qual ψ γ => rw [TypeVar_open, sizeOf', sizeOf', ψ.TypeVar_open_sizeOf', γ.TypeVar_open_sizeOf']

@[simp]
theorem TypeVar_close_sizeOf' (γ : QualifiedType) : (γ.TypeVar_close a n).sizeOf' = γ.sizeOf' := by
  match γ with
  | .mono τ => rw [TypeVar_close, sizeOf', sizeOf', τ.TypeVar_close_sizeOf']
  | .qual ψ γ => rw [TypeVar_close, sizeOf', sizeOf', ψ.TypeVar_close_sizeOf', γ.TypeVar_close_sizeOf']

theorem TypeVar_open_eq_Monotype_open_var : TypeVar_open γ a n = γ.Monotype_open (.var a) n := by
  induction γ <;> aesop
    (add simp [TypeVar_open, Monotype_open], safe Monotype.TypeVar_open_eq_Monotype_open_var)

namespace TypeVarLocallyClosed

theorem weakening (γlc : TypeVarLocallyClosed γ m) : TypeVarLocallyClosed γ (m + n) := by
  induction γlc <;> aesop (simp_config := { arith := true })
    (add safe constructors TypeVarLocallyClosed, 20% Monotype.TypeVarLocallyClosed.weakening)

theorem TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed γ n → (γ.TypeVar_close a n).TypeVar_open a n = γ := by
  induction γ <;> aesop
    (add simp [TypeVar_open, TypeVar_close], 50% cases TypeVarLocallyClosed,
      20% Monotype.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id)

theorem TypeVar_open_drop
  : m < n → (TypeVar_open γ a m).TypeVarLocallyClosed n → TypeVarLocallyClosed γ n := by
  induction γ generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed,
      20% Monotype.TypeVarLocallyClosed.TypeVar_open_drop)

theorem Monotype_open_TypeVar_close_eq_TypeVar_subst (γlc : TypeVarLocallyClosed γ n)
  : (γ.TypeVar_close a n).Monotype_open τ n = γ.TypeVar_subst a τ := by
  match γ with
  | .mono .. =>
    let .mono τlc := γlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst,
        τlc.Monotype_open_TypeVar_close_eq_TypeVar_subst]
  | .qual .. =>
    let .qual ψlc γ'lc := γlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst,
        γ'lc.Monotype_open_TypeVar_close_eq_TypeVar_subst,
        ψlc.Monotype_open_TypeVar_close_eq_TypeVar_subst]

end TypeVarLocallyClosed

theorem TypeVar_open_comm (γ : QualifiedType)
  : m ≠ n → (γ.TypeVar_open a m).TypeVar_open a' n = (γ.TypeVar_open a' n).TypeVar_open a m := by
  induction γ <;> aesop (add simp TypeVar_open, 20% Monotype.TypeVar_open_comm)

theorem TypeVar_open_Monotype_open_comm (γ : QualifiedType) {τ : Monotype}
  : τ.TypeVarLocallyClosed m → m ≠ n →
    (γ.TypeVar_open a m).Monotype_open τ n = (γ.Monotype_open τ n).TypeVar_open a m := by
  induction γ <;> aesop
    (add simp [TypeVar_open, Monotype_open], 20% Monotype.TypeVar_open_Monotype_open_comm)

theorem not_mem_freeTypeVars_TypeVar_open_intro (anin : a ∉ freeTypeVars γ) (anea' : a ≠ a')
  : a ∉ (γ.TypeVar_open a' n).freeTypeVars := by
  match γ with
  | .mono .. =>
    rw [TypeVar_open]
    rw [freeTypeVars] at anin ⊢
    exact Monotype.not_mem_freeTypeVars_TypeVar_open_intro anin anea'
  | .qual .. =>
    rw [TypeVar_open]
    rw [freeTypeVars] at anin ⊢
    let ⟨aninψ, aninγ'⟩ := List.not_mem_append'.mp anin
    exact List.not_mem_append'.mpr ⟨
      Monotype.not_mem_freeTypeVars_TypeVar_open_intro aninψ anea',
      not_mem_freeTypeVars_TypeVar_open_intro aninγ' anea'
    ⟩

theorem not_mem_freeTypeVars_TypeVar_close : a ∉ (TypeVar_close γ a n).freeTypeVars := by
  induction γ with
  | mono _ => exact Monotype.not_mem_freeTypeVars_TypeVar_close
  | qual _ _ ih =>
    rw [TypeVar_close, freeTypeVars]
    apply List.not_mem_append'.mpr
    exact ⟨Monotype.not_mem_freeTypeVars_TypeVar_close, ih⟩

end QualifiedType

namespace TypeScheme

@[simp]
theorem TypeVar_open_sizeOf (σ : TypeScheme) : sizeOf (σ.TypeVar_open a n) = sizeOf σ := by
  match σ with
  | .qual γ => rw [TypeVar_open, qual.sizeOf_spec, qual.sizeOf_spec, γ.TypeVar_open_sizeOf]
  | .quant _ σ => rw [TypeVar_open, quant.sizeOf_spec, quant.sizeOf_spec, σ.TypeVar_open_sizeOf]

@[simp]
theorem sizeOf'_pos (σ : TypeScheme) : 0 < σ.sizeOf' := by cases σ <;> simp_arith [sizeOf']

@[simp]
theorem TypeVar_open_sizeOf' (σ : TypeScheme) : (σ.TypeVar_open a n).sizeOf' = σ.sizeOf' := by
  match σ with
  | .qual γ => rw [TypeVar_open, sizeOf', sizeOf', γ.TypeVar_open_sizeOf']
  | .quant _ σ => rw [TypeVar_open, sizeOf', sizeOf', σ.TypeVar_open_sizeOf']

@[simp]
theorem TypeVar_close_sizeOf' (σ : TypeScheme) : (σ.TypeVar_close a n).sizeOf' = σ.sizeOf' := by
  match σ with
  | .qual γ => rw [TypeVar_close, sizeOf', sizeOf', γ.TypeVar_close_sizeOf']
  | .quant _ σ => rw [TypeVar_close, sizeOf', sizeOf', σ.TypeVar_close_sizeOf']

theorem TypeVar_open_eq_Monotype_open_var : TypeVar_open σ a n = σ.Monotype_open (.var a) n := by
  induction σ generalizing n <;> aesop
    (add simp [TypeVar_open, Monotype_open], safe [Monotype.TypeVar_open_eq_Monotype_open_var,
                                                   QualifiedType.TypeVar_open_eq_Monotype_open_var])

namespace TypeVarLocallyClosed

theorem weakening (σlc : TypeVarLocallyClosed σ m) : TypeVarLocallyClosed σ (m + n) := by
  induction σlc <;> aesop (simp_config := { arith := true })
    (add safe constructors TypeVarLocallyClosed,
      20% [of_eq, QualifiedType.TypeVarLocallyClosed.weakening])
where
  of_eq {σ m n} (σlc : TypeVarLocallyClosed σ m) (eq : m = n) : σ.TypeVarLocallyClosed n := by
    rwa [eq] at σlc

theorem TypeVar_open_TypeVar_close_id
  : TypeVarLocallyClosed σ n → (σ.TypeVar_close a n).TypeVar_open a n = σ  := by
  induction σ generalizing n <;> aesop
    (add simp [TypeVar_open, TypeVar_close], 50% cases TypeVarLocallyClosed,
      20% [QualifiedType.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id])

theorem TypeVar_open_drop
  : m < n → (TypeVar_open σ a m).TypeVarLocallyClosed n → TypeVarLocallyClosed σ n := by
  induction σ generalizing m n <;> aesop
    (add simp TypeVar_open, safe cases TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed,
      20% QualifiedType.TypeVarLocallyClosed.TypeVar_open_drop)

theorem Monotype_open_TypeVar_close_eq_TypeVar_subst (σlc : TypeVarLocallyClosed σ n)
  : (σ.TypeVar_close a n).Monotype_open τ n = σ.TypeVar_subst a τ := by
  match σ with
  | .qual .. =>
    let .qual γlc := σlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst,
        γlc.Monotype_open_TypeVar_close_eq_TypeVar_subst]
  | .quant .. =>
    let .quant σ'lc := σlc
    rw [TypeVar_close, Monotype_open, TypeVar_subst,
        σ'lc.Monotype_open_TypeVar_close_eq_TypeVar_subst]

end TypeVarLocallyClosed

theorem TypeVar_open_comm (σ : TypeScheme)
  : m ≠ n → (σ.TypeVar_open a m).TypeVar_open a' n = (σ.TypeVar_open a' n).TypeVar_open a m := by
  induction σ generalizing m n <;> aesop
    (add simp TypeVar_open, 20% [QualifiedType.TypeVar_open_comm, Monotype.TypeVar_open_comm])

theorem TypeVar_open_Monotype_open_comm (σ : TypeScheme) {τ : Monotype}
  : τ.TypeVarLocallyClosed m → m ≠ n →
    (σ.TypeVar_open a m).Monotype_open τ n = (σ.Monotype_open τ n).TypeVar_open a m := by
  induction σ generalizing m n <;> aesop
    (add simp [TypeVar_open, Monotype_open],
      20% [QualifiedType.TypeVar_open_Monotype_open_comm, Monotype.TypeVarLocallyClosed.weakening])

theorem not_mem_freeTypeVars_TypeVar_open_intro (anin : a ∉ freeTypeVars σ) (anea' : a ≠ a')
  : a ∉ (σ.TypeVar_open a' n).freeTypeVars := by
  match σ with
  | .qual _ =>
    rw [TypeVar_open]
    rw [freeTypeVars] at anin ⊢
    exact QualifiedType.not_mem_freeTypeVars_TypeVar_open_intro anin anea'
  | .quant .. =>
    rw [TypeVar_open]
    rw [freeTypeVars] at anin ⊢
    exact not_mem_freeTypeVars_TypeVar_open_intro anin anea'

theorem not_mem_freeTypeVars_TypeVar_close : a ∉ (TypeVar_close σ a n).freeTypeVars := by
  induction σ generalizing n with
  | qual _ => exact QualifiedType.not_mem_freeTypeVars_TypeVar_close
  | quant _ _ ih =>
    rw [TypeVar_close, freeTypeVars]
    exact ih

namespace KindingAndElaboration

local instance : Inhabited Monotype where
  default := .row [] none
in
local instance : Inhabited «Type» where
  default := .list []
in
theorem empty_row : [[Γc; Γ ⊢ ⟨ : κ ⟩ : R κ ⇝ { }]] := by
  have : some κ = Option.filter (fun _ => true) (some κ) := by rw [Option.filter, if_pos rfl]
  rw (occs := .pos [2]) [← Range.map_get!_eq (as := [])]
  rw [← Range.map_get!_eq (as := []),
      Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = ([].get! i, [].get! i)
        nomatch mem
      ), this]
  apply KindingAndElaboration.row (fun _ mem => by rw [List.length_nil] at mem; nomatch mem) _
    (fun _ mem => by rw [List.length_nil] at mem; nomatch mem) (.inr rfl)
    (B := fun _ => default)
  rw [Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = Monotype.label ((fun i => .zero) i)
    nomatch mem
  )]
  apply Monotype.label.Uniqueness.concrete
  intro _ mem
  rw [List.length_nil] at mem
  nomatch Nat.not_lt_zero _ mem.upper

local instance : Inhabited Monotype where
  default := .row [] none
in
local instance : Inhabited «Type» where
  default := .list []
in
theorem singleton_row (ξke : [[Γc; Γ ⊢ ξ : L ⇝ B]]) (τke : [[Γc; Γ ⊢ τ : κ ⇝ A]])
  : [[Γc; Γ ⊢ ⟨ξ ▹ τ⟩ : R κ ⇝ {A}]] := by
  have : none = Option.filter (fun _ => false) (some κ) := by
    rw [Option.filter, if_neg nofun]
  rw (occs := .pos [2]) [← Range.map_get!_eq (as := [_])]
  rw [← Range.map_get!_eq (as := [_]), Range.map_eq_of_eq_of_mem'' (by
        intro i mem
        show _ = (ξ, τ)
        cases Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ mem.upper
        rw [List.get!_cons_zero]
      ), Range.map_eq_of_eq_of_mem'' (f := fun i => [A].get! i) (by
        intro i mem
        show _ = A
        simp only
        cases Nat.eq_zero_of_le_zero <| Nat.le_of_lt_succ mem.upper
        rw [List.get!_cons_zero]
      ), this,
      List.length_singleton, List.length_singleton]
  apply row (ξ := fun _ => ξ) (τ := fun _ => τ) (A := fun _ => A) (B := fun _ => B) _ _ _ <|
    .inl Nat.one_ne_zero
  · intros
    exact ξke
  · rw [Range.map, Range.toList, if_pos (Nat.succ_pos _), Range.toList, Nat.zero_add,
        if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_singleton]
    exact .var
  · intros
    exact τke

theorem empty_row_inversion (rowke : [[Γc; Γ ⊢ ⟨ : κ'⟩ : κ ⇝ A]]) : κ = [[R κ']] ∧ A = [[{ }]] := by
  generalize ξτseq : [] = ξτs, κ?eq : some κ' = κ? at rowke
  let .row .. := rowke
  rw [Option.someIf] at κ?eq
  split at κ?eq
  case isFalse => nomatch κ?eq
  cases κ?eq
  cases Nat.eq_zero_of_le_zero <| Range.toList_eq_nil_iff.mp <| List.map_eq_nil_iff.mp ξτseq.symm
  rw [Range.map, Range.toList_eq_nil_iff.mpr (Nat.le_refl _), List.map_nil]
  exact ⟨rfl, rfl⟩

theorem singleton_row_inversion (rowke : [[Γc; Γ ⊢ ⟨ξ ▹ τ⟩ : κ ⇝ A]])
  : (∃ B, [[Γc; Γ ⊢ ξ : L ⇝ B]]) ∧
    ∃ κ', κ = [[R κ']] ∧ ∃ A', A = [[{A'}]] ∧ [[Γc; Γ ⊢ τ : κ' ⇝ A']] := by
  generalize ξτseq : [_] = ξτs, κ?eq : none = κ? at rowke
  let .row ξ'ke _ τ'ke _ := rowke
  let length_eq : List.length [_] = List.length _ := by rw [ξτseq]
  rw [List.length_map, Range.length_toList, List.length_singleton] at length_eq
  cases length_eq
  rw [Range.map, Range.toList, if_pos Nat.one_pos, List.map_cons] at ξτseq ⊢
  let mem : 0 ∈ [0:1] := ⟨Nat.le.refl, Nat.one_pos, Nat.mod_one _⟩
  let ξ'ke' := ξ'ke 0 mem
  let τ'ke' := τ'ke 0 mem
  simp only at ξ'ke' τ'ke'
  let ⟨ξeq, τeq⟩ := Prod.mk.inj <| And.left <| List.cons.inj ξτseq
  rw [← ξeq] at ξ'ke'
  rw [← τeq] at τ'ke'
  rw [Range.toList, Nat.zero_add, if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_nil]
  exact ⟨⟨_, ξ'ke'⟩, _, rfl, _, rfl, τ'ke'⟩

theorem row_inversion
  (rowke : [[Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i in [:n] /> </ : κ' // b />⟩ : κ ⇝ A]])
  : (∃ B, ∀ i ∈ [:n], [[Γc; Γ ⊢ ξ@i : L ⇝ B@i]]) ∧ [[unique(</ ξ@i // i in [:n] />)]] ∧
    (∃ B κ'', A = [[{</ B@i // i in [:n] />}]] ∧ κ = [[R κ'']] ∧ (n ≠ 0 ∨ b) ∧ (b → κ' = κ'') ∧
      ∀ i ∈ [:n], [[Γc; Γ ⊢ τ@i : κ'' ⇝ B@i]]) := by
  generalize ξτseq : ([:n].map fun i => (ξ i, τ i)) = ξτs at rowke
  generalize κ''eq : Option.someIf κ' b = κ'' at rowke
  let .row ξke uni τke h := rowke
  rename Nat => n'
  let length_eq : List.length (Range.map ..) = List.length _ := by rw [ξτseq]
  let neqn' : n = n' := by
    repeat rw [List.length_map, Std.Range.length_toList] at length_eq
    exact length_eq
  cases neqn'
  let ξτeqs := Std.Range.eq_of_mem_of_map_eq ξτseq
  rw [Range.map_eq_of_eq_of_mem'' (by rw [← And.left <| Prod.mk.inj <| ξτeqs · ·])] at uni
  exact ⟨
    ⟨
      _,
      fun i imem => by
        rw [And.left <| Prod.mk.inj <| ξτeqs i imem]
        exact ξke i imem
    ⟩,
    uni,
    ⟨
      _,
      _,
      rfl,
      rfl,
      match h with
      | .inl h => .inl h
      | .inr h => by
        rw [BoolId, id] at h
        rw [h, Option.someIf_true] at κ''eq
        exact .inr <| And.right <| Option.eq_of_someIf_eq_some κ''eq,
      by
        intro beq
        rw [beq, Option.someIf_true] at κ''eq
        symm at κ''eq ⊢
        exact And.left <| Option.eq_of_someIf_eq_some κ''eq,
      by
        intro i imem
        rw [And.right <| Prod.mk.inj <| ξτeqs i imem]
        exact τke i imem
    ⟩
  ⟩

theorem TypeVarLocallyClosed_of (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]]) : σ.TypeVarLocallyClosed := by
  induction σke
  case scheme I _ _ ih =>
    let ⟨a, anin⟩ := I.exists_fresh
    exact .quant <| ih a anin |>.weakening.TypeVar_open_drop Nat.zero_lt_one
  case row ih₀ ih₁ =>
    apply TypeVarLocallyClosed.qual <| .mono <| .row _ _
    · intro _ mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      conv => simp_match
      let .qual (.mono ξlc) := ih₀ _ <| Range.mem_of_mem_toList mem'
      exact ξlc
    · intro _ mem
      rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
      conv => simp_match
      let .qual (.mono τlc) := ih₁ _ <| Range.mem_of_mem_toList mem'
      exact τlc
  case lift I _ _ _ ih₀ ih₁ =>
    let ⟨a, anin⟩ := I.exists_fresh
    let .qual (.mono τlc) := ih₀ a anin
    let .qual (.mono ρlc) := ih₁
    exact .qual <| .mono <| .lift (.mk <| τlc.weakening.TypeVar_open_drop Nat.one_pos) ρlc
  case «ind» ih₀ _ _ =>
    let .qual (.mono ρlc) := ih₀
    exact .qual <| .mono <| .ind ρlc
  case all I _ _ _ ih₀ ih₁ =>
    let ⟨a, anin⟩ := I.exists_fresh
    let .qual (.mono ψlc) := ih₀ a anin
    let .qual (.mono ρlc) := ih₁
    exact .qual <| .mono <| .all (.mk <| ψlc.weakening.TypeVar_open_drop Nat.one_pos) ρlc
  case split ih =>
    let .qual (.mono (.concat (.lift «λτlc» ρ₀lc) _ ρ₁lc ρ₂lc)) := ih
    exact .qual <| .mono <| .split «λτlc» ρ₀lc ρ₁lc ρ₂lc
  all_goals aesop (add safe cases TypeVarLocallyClosed,
    40% cases QualifiedType.TypeVarLocallyClosed, safe constructors TypeVarLocallyClosed,
    safe constructors QualifiedType.TypeVarLocallyClosed,
    safe constructors Monotype.TypeVarLocallyClosed)

end KindingAndElaboration

end TypeScheme

namespace Monotype.label.Uniqueness

local instance : Inhabited Monotype where
  default := .row [] none
in
def Monotype_open_preservation (uni : Uniqueness (List.map (TypeVar_open · a n) ξ))
  : Uniqueness (ξ.map (·.Monotype_open τ n)) := by
  generalize ξ'eq : ξ.map (·.TypeVar_open a n) = ξ' at uni
  match uni with
  | concrete ne (ℓ := ℓ) =>
    let length_eq : List.length (List.map ..) = List.length _ := by rw [ξ'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Nat.sub_zero] at length_eq
    rw [← Range.map_get!_eq (as := ξ), length_eq, List.map_map] at ξ'eq ⊢
    rw [Range.map_eq_of_eq_of_mem (by
      intro i mem
      simp only [Function.comp]
      show _ = Monotype.label (ℓ i)
      have := Range.eq_of_mem_of_map_eq ξ'eq i mem
      simp only [Function.comp] at this
      generalize ξ''eq : ξ.get! i = ξ'' at *
      cases ξ'' <;> rw [TypeVar_open] at this
      case label => rw [Monotype_open, label.inj this]
      all_goals nomatch this
    )]
    exact concrete ne
  | var =>
    let [_] := ξ
    exact var

def Perm_preservation {ξ' : Nat → Monotype} (uni : [[unique(</ ξ@i // i in [:n] />)]])
  (perm : List.Perm p [:n]) (eq : ∀ i, ξ' i = ξ (p.get! i))
  : [[unique(</ ξ'@i // i in [:n] />)]] := by
  generalize ξseq : ([:n].map fun i => ξ i) = ξs at uni
  match uni with
  | concrete ne (ℓ := ℓ) =>
    let lengths_eq : List.length (Range.map ..) = List.length _ := by rw [ξseq]
    rw [List.length_map, List.length_map, Std.Range.length_toList,
        Std.Range.length_toList, Nat.sub_zero, Nat.sub_zero] at lengths_eq
    cases lengths_eq
    let lengths_eq := perm.length_eq
    rw [Std.Range.length_toList] at lengths_eq
    cases lengths_eq
    rw [Range.map_eq_of_eq_of_mem'' (by
      intro i imem
      show ξ' i = label (ℓ (p.get! i))
      rw [← Std.Range.eq_of_mem_of_map_eq ξseq (p.get! i) <| Std.Range.mem_of_mem_toList <|
            perm.mem_iff.mp <| List.get!_mem imem.upper]
      exact eq i
    )]
    apply concrete
    intro i imem
    simp only
    let pimem := Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.upper
    intro j jmem
    let pjmem := Std.Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem jmem.upper
    match Nat.lt_trichotomy (p.get! i) (p.get! j) with
    | .inl piltpj =>
      exact ne _ ⟨Nat.zero_le _, pimem.right⟩ _
        ⟨Nat.succ_le_of_lt piltpj, pjmem.upper, Nat.mod_one _⟩
    | .inr (.inl pieqpj) =>
      let inej : i ≠ j := Nat.ne_of_lt <| Nat.lt_of_succ_le jmem.left
      let count_le_one : [:p.length].toList.count (p.get! i) ≤ 1 := Std.Range.count_toList_le_one
      rw [← perm.count_eq (p.get! i)] at count_le_one
      let two_le_count := List.two_le_count_of_get!_eq_of_ne imem.upper jmem.upper pieqpj inej
      nomatch Nat.not_lt_of_le count_le_one <| Nat.lt_of_succ_le two_le_count
    | .inr (.inr pjltpi) =>
      apply Ne.symm
      exact ne _ ⟨Nat.zero_le _, pjmem.right⟩ _
        ⟨Nat.succ_le_of_lt pjltpi, pimem.upper, Nat.mod_one _⟩
  | var =>
    let lengths_eq : List.length (Range.map ..) = List.length _ := by rw [ξseq]
    rw [List.length_map, Std.Range.length_toList, List.length_singleton, Nat.sub_zero] at lengths_eq
    cases lengths_eq
    rw [Range.map, Range.toList, if_pos Nat.one_pos, Range.toList, Nat.zero_add,
        if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map_singleton]
    exact var

end Monotype.label.Uniqueness

namespace TypeScheme.KindingAndElaboration

theorem weakening (σke : [[Γc; Γ, Γ'' ⊢ σ : κ ⇝ A]])
  (ΓΓ'Γ''we : [[Γc ⊢ Γ, Γ', Γ'' ⇝ Δ]]) : [[Γc; Γ, Γ', Γ'' ⊢ σ : κ ⇝ A]] := by match σke with
  | var aκinΓΓ'' => exact var <| match aκinΓΓ''.append_elim with
    | .inl ⟨aκinΓ, aninΓ''⟩ => ΓΓ'Γ''we.TypeVarIn_weakening aκinΓ
    | .inr aκinΓ'' => aκinΓ''.append_inr.append_inr
  | app φke τke => exact app (φke.weakening ΓΓ'Γ''we) (τke.weakening ΓΓ'Γ''we)
  | arr τ₀ke τ₁ke => exact arr (τ₀ke.weakening ΓΓ'Γ''we) (τ₁ke.weakening ΓΓ'Γ''we)
  | qual ψke γke κe => exact qual (ψke.weakening ΓΓ'Γ''we) (γke.weakening ΓΓ'Γ''we) κe
  | scheme I σ'ke κ₀e =>
    apply scheme (I ++ [[(Γ, Γ', Γ'')]].typeVarDom) _ κ₀e
    intro a anin
    let ⟨aninI, aninΓΓ'Γ''⟩ := List.not_mem_append'.mp anin
    rw [← TypeEnvironment.append, ← TypeEnvironment.append]
    exact σ'ke a aninI |>.weakening <| ΓΓ'Γ''we.typeExt aninΓΓ'Γ'' κ₀e
  | label => exact label
  | floor ξke => exact floor <| ξke.weakening ΓΓ'Γ''we
  | comm => exact comm
  | row ξke uni τke h =>
    exact row (ξke · · |>.weakening ΓΓ'Γ''we) uni (τke · · |>.weakening ΓΓ'Γ''we) h
  | prod μke ρke => exact prod (μke.weakening ΓΓ'Γ''we) (ρke.weakening ΓΓ'Γ''we)
  | sum μke ρke => exact sum (μke.weakening ΓΓ'Γ''we) (ρke.weakening ΓΓ'Γ''we)
  | lift I τke κ₀e ρke =>
    apply lift (I ++ [[(Γ, Γ', Γ'')]].typeVarDom) _ κ₀e <| ρke.weakening ΓΓ'Γ''we
    intro a anin
    let ⟨aninI, aninΓΓ'Γ''⟩ := List.not_mem_append'.mp anin
    rw [← TypeEnvironment.append, ← TypeEnvironment.append]
    exact τke a aninI |>.weakening <| ΓΓ'Γ''we.typeExt aninΓΓ'Γ'' κ₀e
  | contain μke ρ₀ke ρ₁ke κe =>
    exact contain (μke.weakening ΓΓ'Γ''we) (ρ₀ke.weakening ΓΓ'Γ''we) (ρ₁ke.weakening ΓΓ'Γ''we) κe
  | concat μke ρ₀ke ρ₁ke ρ₂ke κe concat₀₂ke concat₁₂ke =>
    exact concat (μke.weakening ΓΓ'Γ''we) (ρ₀ke.weakening ΓΓ'Γ''we) (ρ₁ke.weakening ΓΓ'Γ''we)
      (ρ₂ke.weakening ΓΓ'Γ''we) κe (concat₀₂ke.weakening ΓΓ'Γ''we) (concat₁₂ke.weakening ΓΓ'Γ''we)
  | tc γcin τke => exact tc γcin <| τke.weakening ΓΓ'Γ''we
  | all I ψke κe ρke =>
    apply all (I ++ [[(Γ, Γ', Γ'')]].typeVarDom) _ κe <| ρke.weakening ΓΓ'Γ''we
    intro a anin
    let ⟨aninI, aninΓΓ'Γ''⟩ := List.not_mem_append'.mp anin
    rw [← TypeEnvironment.append, ← TypeEnvironment.append]
    exact ψke a aninI |>.weakening <| ΓΓ'Γ''we.typeExt aninΓΓ'Γ'' κe
  | «ind» I₀ I₁ ρke κe keBᵣ keBₗ =>
    apply «ind» (I₀ ++ [[(Γ, Γ', Γ'')]].typeVarDom) (I₁ ++ [[(Γ, Γ', Γ'')]].typeVarDom)
      (ρke.weakening ΓΓ'Γ''we) κe
    · intro aₗ aₗnin aₜ aₜnin aₚ aₚnin aᵢ aᵢnin aₙ aₙnin
      let ⟨aₗninI₀, aₗninΓΓ'Γ''⟩ := List.not_mem_append'.mp aₗnin
      rw [← List.cons_append] at aₜnin
      let ⟨aₜninI₀, aₜninΓΓ'Γ''⟩ := List.not_mem_append'.mp aₜnin
      let aₜninΓΓ'Γ''aₗ := List.not_mem_cons.mpr ⟨List.ne_of_not_mem_cons aₜninI₀, aₜninΓΓ'Γ''⟩
      rw [← List.cons_append, ← List.cons_append] at aₚnin
      let ⟨aₚninI₀, aₚninΓΓ'Γ''⟩ := List.not_mem_append'.mp aₚnin
      let aₚninΓΓ'Γ''aₗaₜ := List.not_mem_cons.mpr ⟨
        List.ne_of_not_mem_cons aₚninI₀,
        List.not_mem_cons.mpr ⟨
          List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₚninI₀,
          aₚninΓΓ'Γ''
        ⟩
      ⟩
      rw [← List.cons_append, ← List.cons_append, ← List.cons_append] at aᵢnin
      let ⟨aᵢninI₀, aᵢninΓΓ'Γ''⟩ := List.not_mem_append'.mp aᵢnin
      let aᵢninΓΓ'Γ''aₗaₜaₚ := List.not_mem_cons.mpr ⟨
        List.ne_of_not_mem_cons aᵢninI₀,
        List.not_mem_cons.mpr ⟨
          List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aᵢninI₀,
          List.not_mem_cons.mpr ⟨
            List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
              List.not_mem_of_not_mem_cons aᵢninI₀,
            aᵢninΓΓ'Γ''
          ⟩
        ⟩
      ⟩
      rw [← List.cons_append, ← List.cons_append, ← List.cons_append, ← List.cons_append] at aₙnin
      let ⟨aₙninI₀, aₙninΓΓ'Γ''⟩ := List.not_mem_append'.mp aₙnin
      let aₙninΓΓ'Γ''aₗaₜaₚᵢ := List.not_mem_cons.mpr ⟨
        List.ne_of_not_mem_cons aₙninI₀,
        List.not_mem_cons.mpr ⟨
          List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninI₀,
          List.not_mem_cons.mpr ⟨
            List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
              List.not_mem_of_not_mem_cons aₙninI₀,
            List.not_mem_cons.mpr ⟨
              List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
                List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninI₀,
              aₙninΓΓ'Γ''
            ⟩
          ⟩
        ⟩
      ⟩
      repeat rw [← TypeEnvironment.append]
      exact keBᵣ aₗ aₗninI₀ aₜ aₜninI₀ aₚ aₚninI₀ aᵢ aᵢninI₀ aₙ aₙninI₀ |>.weakening <|
        ΓΓ'Γ''we.typeExt aₗninΓΓ'Γ'' .label |>.typeExt aₜninΓΓ'Γ''aₗ κe
          |>.typeExt aₚninΓΓ'Γ''aₗaₜ κe.row |>.typeExt aᵢninΓΓ'Γ''aₗaₜaₚ κe.row
          |>.typeExt aₙninΓΓ'Γ''aₗaₜaₚᵢ κe.row
    · intro aᵢ aᵢnin aₙ aₙnin
      let ⟨aᵢninI₁, aᵢninΓΓ'Γ''⟩ := List.not_mem_append'.mp aᵢnin
      rw [← List.cons_append] at aₙnin
      let ⟨aₙninI₁, aₙninΓΓ'Γ''⟩ := List.not_mem_append'.mp aₙnin
      let aₙninΓΓ'Γ''aᵢ := List.not_mem_cons.mpr ⟨List.ne_of_not_mem_cons aₙninI₁, aₙninΓΓ'Γ''⟩
      repeat rw [← TypeEnvironment.append]
      exact keBₗ aᵢ aᵢninI₁ aₙ aₙninI₁ |>.weakening <|
        ΓΓ'Γ''we.typeExt aᵢninΓΓ'Γ'' κe.row |>.typeExt aₙninΓΓ'Γ''aᵢ κe.row
  | split concatke => exact split <| concatke.weakening ΓΓ'Γ''we
termination_by σ.sizeOf'
decreasing_by
  all_goals simp_arith
  · case _ ξ _ τ _ _ _ _ i mem =>
    apply Nat.le_of_add_right_le (k := (τ i).sizeOf')
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem mem
  · case _ ξ _ τ _ _ _ _ i mem =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem mem
  · exact Monotype.sizeOf'_pos _

theorem TermVar_drop (σke : [[Γc; Γ, x : σ₁, Γ' ⊢ σ₀ : κ ⇝ A]])
  : [[Γc; Γ, Γ' ⊢ σ₀ : κ ⇝ A]] := match σke with
  | var aκinΓxσΓ' => var <| match aκinΓxσΓ'.append_elim with
    | .inl ⟨.termExt aκinΓ, aninΓ'⟩ => aκinΓ.append_inl aninΓ'
    | .inr aκinΓ' => aκinΓ'.append_inr
  | app φke τke => app φke.TermVar_drop τke.TermVar_drop
  | arr τ₀ke τ₁ke => arr τ₀ke.TermVar_drop τ₁ke.TermVar_drop
  | qual ψke γke κe => qual ψke.TermVar_drop γke.TermVar_drop κe
  | scheme I σ'ke κ₀e => by
    apply scheme I _ κ₀e
    intro a anin
    rw [← TypeEnvironment.append]
    exact σ'ke a anin |>.TermVar_drop
  | label => label
  | floor ξke => floor ξke.TermVar_drop
  | comm => comm
  | row ξke uni τke h => row (ξke · · |>.TermVar_drop) uni (τke · · |>.TermVar_drop) h
  | prod μke ρke => prod μke.TermVar_drop ρke.TermVar_drop
  | sum μke ρke => sum μke.TermVar_drop ρke.TermVar_drop
  | lift I τke κ₀e ρke => by
    apply lift I _ κ₀e ρke.TermVar_drop
    intro a anin
    rw [← TypeEnvironment.append]
    exact τke a anin |>.TermVar_drop
  | contain μke ρ₀ke ρ₁ke κe => contain μke.TermVar_drop ρ₀ke.TermVar_drop ρ₁ke.TermVar_drop κe
  | concat μke ρ₀ke ρ₁ke ρ₂ke κe concat₀₂ke concat₁₂ke =>
    concat μke.TermVar_drop ρ₀ke.TermVar_drop ρ₁ke.TermVar_drop ρ₂ke.TermVar_drop κe
      concat₀₂ke.TermVar_drop concat₁₂ke.TermVar_drop
  | tc γcin τke => tc γcin τke.TermVar_drop
  | all I ψke κ₀e ρke => by
    apply all I _ κ₀e ρke.TermVar_drop
    intro a anin
    rw [← TypeEnvironment.append]
    exact ψke a anin |>.TermVar_drop
  | «ind» I₀ I₁ ρke κe keBᵣ keBₗ => by
    apply «ind» I₀ I₁ ρke.TermVar_drop κe
    · intro _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin
      repeat rw [← TypeEnvironment.append]
      exact keBᵣ _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin |>.TermVar_drop
    · intro _ aᵢnin _ aₙnin
      repeat rw [← TypeEnvironment.append]
      exact keBₗ _ aᵢnin _ aₙnin |>.TermVar_drop
  | split concatke => split concatke.TermVar_drop
termination_by σ₀.sizeOf'
decreasing_by
  all_goals simp_arith
  · case _ ξ _ τ _ _ _ _ i mem =>
    apply Nat.le_of_add_right_le (k := (τ i).sizeOf')
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem mem
  · case _ ξ _ τ _ _ _ _ i mem =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem mem
  · exact Monotype.sizeOf'_pos _

theorem Constr_drop (σke : [[Γc; Γ, ψ ⇝ x, Γ' ⊢ σ : κ ⇝ A]])
  : [[Γc; Γ, Γ' ⊢ σ : κ ⇝ A]] := match σke with
  | var aκinΓψxΓ' => var <| match aκinΓψxΓ'.append_elim with
    | .inl ⟨.constrExt aκinΓ, aninΓ'⟩ => aκinΓ.append_inl aninΓ'
    | .inr aκinΓ' => aκinΓ'.append_inr
  | app φke τke => app φke.Constr_drop τke.Constr_drop
  | arr τ₀ke τ₁ke => arr τ₀ke.Constr_drop τ₁ke.Constr_drop
  | qual ψke γke κe => qual ψke.Constr_drop γke.Constr_drop κe
  | scheme I σ'ke κ₀e => by
    apply scheme I _ κ₀e
    intro a anin
    rw [← TypeEnvironment.append]
    exact σ'ke a anin |>.Constr_drop
  | label => label
  | floor ξke => floor ξke.Constr_drop
  | comm => comm
  | row ξke uni τke h => row (ξke · · |>.Constr_drop) uni (τke · · |>.Constr_drop) h
  | prod μke ρke => prod μke.Constr_drop ρke.Constr_drop
  | sum μke ρke => sum μke.Constr_drop ρke.Constr_drop
  | lift I τke κ₀e ρke => by
    apply lift I _ κ₀e ρke.Constr_drop
    intro a anin
    rw [← TypeEnvironment.append]
    exact τke a anin |>.Constr_drop
  | contain μke ρ₀ke ρ₁ke κe => contain μke.Constr_drop ρ₀ke.Constr_drop ρ₁ke.Constr_drop κe
  | concat μke ρ₀ke ρ₁ke ρ₂ke κe concat₀₂ke concat₁₂ke =>
    concat μke.Constr_drop ρ₀ke.Constr_drop ρ₁ke.Constr_drop ρ₂ke.Constr_drop κe
      concat₀₂ke.Constr_drop concat₁₂ke.Constr_drop
  | tc γcin τke => tc γcin τke.Constr_drop
  | all I ψke κ₀e ρke => by
    apply all I _ κ₀e ρke.Constr_drop
    intro a anin
    rw [← TypeEnvironment.append]
    exact ψke a anin |>.Constr_drop
  | «ind» I₀ I₁ ρke κe keBᵣ keBₗ => by
    apply «ind» I₀ I₁ ρke.Constr_drop κe
    · intro _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin
      repeat rw [← TypeEnvironment.append]
      exact keBᵣ _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin |>.Constr_drop
    · intro _ aᵢnin _ aₙnin
      repeat rw [← TypeEnvironment.append]
      exact keBₗ _ aᵢnin _ aₙnin |>.Constr_drop
  | split concatke => split concatke.Constr_drop
termination_by σ.sizeOf'
decreasing_by
  all_goals simp_arith
  · case _ ξ _ τ _ _ _ _ i mem =>
    apply Nat.le_of_add_right_le (k := (τ i).sizeOf')
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem mem
  · case _ ξ _ τ _ _ _ _ i mem =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem mem
  · exact Monotype.sizeOf'_pos _

end TypeScheme.KindingAndElaboration

end TabularTypeInterpreter
