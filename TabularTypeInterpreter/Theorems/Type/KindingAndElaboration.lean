import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.Lemmas.ClassEnvironment
import TabularTypeInterpreter.Lemmas.Type.Basic
import TabularTypeInterpreter.Lemmas.TypeEnvironment.Basic
import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

theorem TypeScheme.KindingAndElaboration.deterministic (σke₀ : [[Γc; Γ ⊢ σ : κ₀ ⇝ A]])
  (σke₁ : [[Γc; Γ ⊢ σ : κ₁ ⇝ B]]) : κ₀ = κ₁ ∧ A = B := match σke₀, σke₁ with
  | .var aκ₀in, .var aκ₁in => ⟨aκ₀in.deterministic aκ₁in, rfl⟩
  | .app ϕ₀ke τ₀ke, .app ϕ₁ke τ₁ke =>
    let ⟨κ₀eq, Aeq⟩ := ϕ₀ke.deterministic ϕ₁ke
    ⟨Kind.arr.inj κ₀eq |>.right, Type.app.injEq .. |>.mpr ⟨Aeq, τ₀ke.deterministic τ₁ke |>.right⟩⟩
  | .arr τ₀₀ke τ₁₀ke, .arr τ₀₁ke τ₁₁ke => ⟨
      rfl,
      Type.arr.injEq .. |>.mpr ⟨
        τ₀₀ke.deterministic τ₀₁ke |>.right,
        τ₁₀ke.deterministic τ₁₁ke |>.right
      ⟩
    ⟩
  | .qual ψ₀ke γ₀ke _, .qual ψ₁ke γ₁ke _ =>
    let ⟨κeq, Beq⟩ := γ₀ke.deterministic γ₁ke
    ⟨κeq, Type.arr.injEq .. |>.mpr ⟨ψ₀ke.deterministic ψ₁ke |>.right, Beq⟩⟩
  | .scheme I₀ σ₀ke κ₀e (A := A₀), .scheme I₁ σ₁ke κ₁e (A := A₁) =>
    let ⟨a, anin⟩ := I₀ ++ I₁ ++ ↑A₀.freeTypeVars ++ ↑A₁.freeTypeVars |>.exists_fresh
    let ⟨aninI₀I₁A₀, aninA₁⟩ := List.not_mem_append'.mp anin
    let ⟨aninI₀I₁, aninA₀⟩ := List.not_mem_append'.mp aninI₀I₁A₀
    let ⟨aninI₀, aninI₁⟩ := List.not_mem_append'.mp aninI₀I₁
    let ⟨κeq, Aopeq⟩ := σ₀ke a aninI₀ |>.deterministic <| σ₁ke a aninI₁
    ⟨
      κeq,
      Type.forall.injEq .. |>.mpr ⟨
        κ₀e.deterministic κ₁e,
        Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA₀ aninA₁ Aopeq
      ⟩
    ⟩

  | .label, .label
  | .floor _, .floor _
  | .comm, .comm => ⟨rfl, rfl⟩
  | .row ξ₀ke _ τ₀ke h (n := n), σke₁ => by
    let ⟨_, _, ⟨_, _, Aeq, κeq, _, κ'eq, τ₁ke⟩⟩ := σke₁.row_inversion (n := n)
    cases κeq
    cases Aeq
    constructor
    · match h with
      | .inl nnezero =>
        let τ₀₀ke := τ₀ke 0 ⟨Nat.le_refl _, Nat.pos_of_ne_zero nnezero, Nat.mod_one _⟩
        let τ₁₀ke := τ₁ke 0 ⟨Nat.le_refl _, Nat.pos_of_ne_zero nnezero, Nat.mod_one _⟩
        exact Kind.row.injEq .. |>.mpr <| τ₀₀ke.deterministic τ₁₀ke |>.left
      | .inr beq => exact Kind.row.injEq .. |>.mpr <| κ'eq beq
    · apply Type.list.injEq .. |>.mpr
      apply Range.map_eq_of_eq_of_mem
      intro i imem
      exact And.right <| τ₀ke i imem |>.deterministic <| τ₁ke i imem
  | .prod _ ρ₀ke, .prod _ ρ₁ke =>
    ⟨rfl, Type.prod.injEq .. |>.mpr <| ρ₀ke.deterministic ρ₁ke |>.right⟩
  | .sum _ ρ₀ke, .sum _ ρ₁ke =>
    ⟨rfl, Type.sum.injEq .. |>.mpr <| ρ₀ke.deterministic ρ₁ke |>.right⟩
  | .lift I₀ τ₀ke κ₀e ρ₀ke (A := A₀), .lift I₁ τ₁ke κ₁e ρ₁ke (A := A₁) =>
    let ⟨a, anin⟩ := I₀ ++ I₁ ++ ↑A₀.freeTypeVars ++ ↑A₁.freeTypeVars |>.exists_fresh
    let ⟨aninI₀I₁A₀, aninA₁⟩ := List.not_mem_append'.mp anin
    let ⟨aninI₀I₁, aninA₀⟩ := List.not_mem_append'.mp aninI₀I₁A₀
    let ⟨aninI₀, aninI₁⟩ := List.not_mem_append'.mp aninI₀I₁
    let ⟨κeq, Beq⟩ := τ₀ke a aninI₀ |>.deterministic <| τ₁ke a aninI₁
    ⟨
      Kind.row.injEq .. |>.mpr κeq,
      Type.listApp.injEq .. |>.mpr ⟨
        Type.lam.injEq .. |>.mpr
          ⟨κ₀e.deterministic κ₁e, Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA₀ aninA₁ Beq⟩,
        ρ₀ke.deterministic ρ₁ke |>.right
      ⟩
    ⟩

  | .contain _ ρ₀₀ke ρ₁₀ke κ₀e, .contain _ ρ₀₁ke ρ₁₁ke κ₁e => by
    let ⟨κeq, A₀eq⟩ := ρ₀₀ke.deterministic ρ₀₁ke
    let ⟨_, A₁eq⟩ := ρ₁₀ke.deterministic ρ₁₁ke
    cases κeq
    exact ⟨
      rfl,
      Type.prod.injEq .. |>.mpr <| Type.list.injEq .. |>.mpr <| List.cons.injEq .. |>.mpr ⟨
        Type.forall.injEq .. |>.mpr ⟨
          «F⊗⊕ω».Kind.arr.injEq .. |>.mpr ⟨κ₀e.deterministic κ₁e, rfl⟩,
          Type.arr.injEq .. |>.mpr ⟨
            Type.prod.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₁eq⟩,
            Type.prod.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₀eq⟩
          ⟩
        ⟩,
        List.cons.injEq .. |>.mpr ⟨
          Type.forall.injEq .. |>.mpr ⟨
            «F⊗⊕ω».Kind.arr.injEq .. |>.mpr ⟨κ₀e.deterministic κ₁e, rfl⟩,
            Type.arr.injEq .. |>.mpr ⟨
              Type.sum.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₀eq⟩,
              Type.sum.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₁eq⟩
            ⟩
          ⟩,
          rfl
        ⟩
      ⟩
    ⟩
  | .concat _ ρ₀₀ke ρ₁₀ke ρ₂₀ke κ₀e containᵣ₀ containₗ₀,
    .concat _ ρ₀₁ke ρ₁₁ke ρ₂₁ke κ₁e containᵣ₁ containₗ₁ => by
    let ⟨κeq, A₀eq⟩ := ρ₀₀ke.deterministic ρ₀₁ke
    let ⟨_, A₁eq⟩ := ρ₁₀ke.deterministic ρ₁₁ke
    let ⟨_, A₂eq⟩ := ρ₂₀ke.deterministic ρ₂₁ke
    cases κeq
    let ⟨_, Bᵣeq⟩ := containᵣ₀.deterministic containᵣ₁
    let ⟨_, Bₗeq⟩ := containₗ₀.deterministic containₗ₁
    exact ⟨
      rfl,
      Type.prod.injEq .. |>.mpr <| Type.list.injEq .. |>.mpr <| List.cons.injEq .. |>.mpr ⟨
        Type.forall.injEq .. |>.mpr ⟨
          «F⊗⊕ω».Kind.arr.injEq .. |>.mpr ⟨κ₀e.deterministic κ₁e, rfl⟩,
          Type.arr.injEq .. |>.mpr ⟨
            Type.prod.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₀eq⟩,
            Type.arr.injEq .. |>.mpr ⟨
              Type.prod.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₁eq⟩,
              Type.prod.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₂eq⟩
            ⟩
          ⟩
        ⟩,
        List.cons.injEq .. |>.mpr ⟨
          Type.forall.injEq .. |>.mpr ⟨
            «F⊗⊕ω».Kind.arr.injEq .. |>.mpr ⟨κ₀e.deterministic κ₁e, rfl⟩,
            Type.forall.injEq .. |>.mpr ⟨
              rfl,
              Type.arr.injEq .. |>.mpr ⟨
                Type.arr.injEq .. |>.mpr ⟨
                  Type.sum.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₀eq⟩,
                  rfl
                ⟩,
                Type.arr.injEq .. |>.mpr ⟨
                  Type.arr.injEq .. |>.mpr ⟨
                    Type.sum.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₁eq⟩,
                    rfl
                  ⟩,
                  Type.arr.injEq .. |>.mpr ⟨
                    Type.sum.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨rfl, A₂eq⟩,
                    rfl
                  ⟩
                ⟩
              ⟩
            ⟩
          ⟩,
          List.cons.injEq .. |>.mpr ⟨Bᵣeq, List.cons.injEq .. |>.mpr ⟨Bₗeq, rfl⟩⟩
        ⟩
      ⟩
    ⟩
  | .tc mem₀ τ₀ke, .tc mem₁ τ₁ke => by
    let ⟨TCₛAₛeq, _, _, _, _, Aeq⟩ := ClassEnvironmentEntry.mk.inj <| mem₀.deterministic mem₁ rfl
    cases Aeq
    cases τ₀ke.deterministic τ₁ke |>.right
    constructor
    · rfl
    · apply Type.prod.injEq .. |>.mpr <| Type.list.injEq .. |>.mpr <| List.cons.injEq .. |>.mpr
        ⟨rfl, _⟩
      let lengths_eq : List.length (Range.map ..) = List.length _ := by rw [TCₛAₛeq]
      rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at lengths_eq
      cases lengths_eq
      apply Range.map_eq_of_eq_of_mem
      intro i imem
      rw [And.right <| ClassEnvironmentEntrySuper.mk.inj <|
            Range.eq_of_mem_of_map_eq TCₛAₛeq i imem]
  | .all I₀ ψ₀ke κ₀e ρ₀ke (A := A₀), .all I₁ ψ₁ke κ₁e ρ₁ke (A := A₁) =>
    let ⟨a, anin⟩ := I₀ ++ I₁ ++ ↑A₀.freeTypeVars ++ ↑A₁.freeTypeVars |>.exists_fresh
    let ⟨aninI₀I₁A₀, aninA₁⟩ := List.not_mem_append'.mp anin
    let ⟨aninI₀I₁, aninA₀⟩ := List.not_mem_append'.mp aninI₀I₁A₀
    let ⟨aninI₀, aninI₁⟩ := List.not_mem_append'.mp aninI₀I₁
    ⟨
      rfl,
      Type.prod.injEq .. |>.mpr <| Type.listApp.injEq .. |>.mpr ⟨
        Type.lam.injEq .. |>.mpr ⟨
          κ₀e.deterministic κ₁e,
          Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA₀ aninA₁ <| And.right <|
            ψ₀ke a aninI₀ |>.deterministic <| ψ₁ke a aninI₁
        ⟩,
        ρ₀ke.deterministic ρ₁ke |>.right
      ⟩
    ⟩
  | .ind I₀₀ I₁₀ ρ₀ke κ₀e keBₗ₀ keBᵣ₀ (Bₗ := Bₗ₀) (Bᵣ := Bᵣ₀),
    .ind I₀₁ I₁₁ ρ₁ke κ₁e  keBₗ₁ keBᵣ₁ (Bₗ := Bₗ₁) (Bᵣ := Bᵣ₁) => open «Type» in by
    let ⟨κeq, Aeq⟩ := ρ₀ke.deterministic ρ₁ke
    cases κeq

    let ⟨aₗ₀, aₗ₀nin⟩ := I₀₀ ++ I₀₁ ++ ↑Bₗ₀.freeTypeVars ++ ↑Bₗ₁.freeTypeVars |>.exists_fresh
    let ⟨aₗ₀nin₀₁Bₗ₀, aₗ₀ninBₗ₁⟩ := List.not_mem_append'.mp aₗ₀nin
    let ⟨aₗ₀nin₀₁, aₗ₀ninBₗ₀⟩ := List.not_mem_append'.mp aₗ₀nin₀₁Bₗ₀
    let ⟨aₗ₀nin₀, aₗ₀nin₁⟩ := List.not_mem_append'.mp aₗ₀nin₀₁
    let I₀₀ₗ := aₗ₀ :: I₀₀
    let I₀₁ₗ := aₗ₀ :: I₀₁
    let ⟨aₜ₀, aₜ₀nin⟩ := I₀₀ₗ ++ I₀₁ₗ ++ ↑Bₗ₀.freeTypeVars ++ ↑Bₗ₁.freeTypeVars |>.exists_fresh
    let ⟨aₜ₀nin₀₁Bₗ₀, aₜ₀ninBₗ₁⟩ := List.not_mem_append'.mp aₜ₀nin
    let ⟨aₜ₀nin₀₁, aₜ₀ninBₗ₀⟩ := List.not_mem_append'.mp aₜ₀nin₀₁Bₗ₀
    let ⟨aₜ₀nin₀, aₜ₀nin₁⟩ := List.not_mem_append'.mp aₜ₀nin₀₁
    let I₀₀ₗₜ := aₜ₀ :: I₀₀ₗ
    let I₀₁ₗₜ := aₜ₀ :: I₀₁ₗ
    let ⟨aₚ₀, aₚ₀nin⟩ := I₀₀ₗₜ ++ I₀₁ₗₜ ++ ↑Bₗ₀.freeTypeVars ++ ↑Bₗ₁.freeTypeVars |>.exists_fresh
    let ⟨aₚ₀nin₀₁Bₗ₀, aₚ₀ninBₗ₁⟩ := List.not_mem_append'.mp aₚ₀nin
    let ⟨aₚ₀nin₀₁, aₚ₀ninBₗ₀⟩ := List.not_mem_append'.mp aₚ₀nin₀₁Bₗ₀
    let ⟨aₚ₀nin₀, aₚ₀nin₁⟩ := List.not_mem_append'.mp aₚ₀nin₀₁
    let I₀₀ₗₜₚ := aₚ₀ :: I₀₀ₗₜ
    let I₀₁ₗₜₚ := aₚ₀ :: I₀₁ₗₜ
    let ⟨aᵢ₀, aᵢ₀nin⟩ := I₀₀ₗₜₚ ++ I₀₁ₗₜₚ ++ ↑Bₗ₀.freeTypeVars ++ ↑Bₗ₁.freeTypeVars |>.exists_fresh
    let ⟨aᵢ₀nin₀₁Bₗ₀, aᵢ₀ninBₗ₁⟩ := List.not_mem_append'.mp aᵢ₀nin
    let ⟨aᵢ₀nin₀₁, aᵢ₀ninBₗ₀⟩ := List.not_mem_append'.mp aᵢ₀nin₀₁Bₗ₀
    let ⟨aᵢ₀nin₀, aᵢ₀nin₁⟩ := List.not_mem_append'.mp aᵢ₀nin₀₁
    let ⟨_, Bₗopeq⟩ := keBₗ₀ aₗ₀ aₗ₀nin₀ aₜ₀ aₜ₀nin₀ aₚ₀ aₚ₀nin₀ aᵢ₀ aᵢ₀nin₀ |>.deterministic <|
      keBₗ₁ aₗ₀ aₗ₀nin₁ aₜ₀ aₜ₀nin₁ aₚ₀ aₚ₀nin₁ aᵢ₀ aᵢ₀nin₁
    let aₜ₀neaₗ₀ := List.ne_of_not_mem_cons aₜ₀nin₀
    let aₜ₀ninBₗ₀op :=
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₜ₀neaₗ₀ aₜ₀ninBₗ₀ (n := 4)
    let aₜ₀ninBₗ₁op :=
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₜ₀neaₗ₀ aₜ₀ninBₗ₁ (n := 4)
    let aₚ₀neaₗ₀ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₚ₀nin₀
    let aₚ₀neaₜ₀ := List.ne_of_not_mem_cons aₚ₀nin₀
    let aₚ₀ninBₗ₀op := TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₚ₀neaₜ₀ (n := 3) <|
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₚ₀neaₗ₀ aₚ₀ninBₗ₀ (n := 4)
    let aₚ₀ninBₗ₁op := TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₚ₀neaₜ₀ (n := 3) <|
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₚ₀neaₗ₀ aₚ₀ninBₗ₁ (n := 4)
    let aᵢ₀neaₚ₀ := List.ne_of_not_mem_cons aᵢ₀nin₀
    let aᵢ₀neaₜ₀ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aᵢ₀nin₀
    let aᵢ₀neaₗ₀ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
      List.not_mem_of_not_mem_cons aᵢ₀nin₀
    let aᵢ₀ninBₗ₀op := TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aᵢ₀neaₚ₀ (n := 2) <|
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aᵢ₀neaₜ₀ (n := 3) <|
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aᵢ₀neaₗ₀ aᵢ₀ninBₗ₀ (n := 4)
    let aᵢ₀ninBₗ₁op := TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aᵢ₀neaₚ₀ (n := 2) <|
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aᵢ₀neaₜ₀ (n := 3) <|
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aᵢ₀neaₗ₀ aᵢ₀ninBₗ₁ (n := 4)
    let Bₗeq := TypeVar_open_inj_of_not_mem_freeTypeVars aₗ₀ninBₗ₀ aₗ₀ninBₗ₁ <|
      TypeVar_open_inj_of_not_mem_freeTypeVars aₜ₀ninBₗ₀op aₜ₀ninBₗ₁op <|
      TypeVar_open_inj_of_not_mem_freeTypeVars aₚ₀ninBₗ₀op aₚ₀ninBₗ₁op <|
      TypeVar_open_inj_of_not_mem_freeTypeVars aᵢ₀ninBₗ₀op aᵢ₀ninBₗ₁op Bₗopeq

    let ⟨aᵢ₁, aᵢ₁nin⟩ := I₁₀ ++ I₁₁ ++ ↑Bᵣ₀.freeTypeVars ++ ↑Bᵣ₁.freeTypeVars |>.exists_fresh
    let ⟨aᵢ₁nin₀₁Bᵣ₀, aᵢ₁ninBᵣ₁⟩ := List.not_mem_append'.mp aᵢ₁nin
    let ⟨aᵢ₁nin₀₁, aᵢ₁ninBᵣ₀⟩ := List.not_mem_append'.mp aᵢ₁nin₀₁Bᵣ₀
    let ⟨aᵢ₁nin₀, aᵢ₁nin₁⟩ := List.not_mem_append'.mp aᵢ₁nin₀₁
    let I₁₀ᵢ := aᵢ₁ :: I₁₀
    let I₁₁ᵢ := aᵢ₁ :: I₁₁
    let ⟨aₙ₁, aₙ₁nin⟩ := I₁₀ᵢ ++ I₁₁ᵢ ++ ↑Bᵣ₀.freeTypeVars ++ ↑Bᵣ₁.freeTypeVars |>.exists_fresh
    let ⟨aₙ₁nin₀₁Bᵣ₀, aₙ₁ninBᵣ₁⟩ := List.not_mem_append'.mp aₙ₁nin
    let ⟨aₙ₁nin₀₁, aₙ₁ninBᵣ₀⟩ := List.not_mem_append'.mp aₙ₁nin₀₁Bᵣ₀
    let ⟨aₙ₁nin₀, aₙ₁nin₁⟩ := List.not_mem_append'.mp aₙ₁nin₀₁
    let ⟨_, Bᵣopeq⟩ := keBᵣ₀ aᵢ₁ aᵢ₁nin₀ aₙ₁ aₙ₁nin₀ |>.deterministic <|
      keBᵣ₁ aᵢ₁ aᵢ₁nin₁ aₙ₁ aₙ₁nin₁
    let aₙ₁neaᵢ₁ := List.ne_of_not_mem_cons aₙ₁nin₀
    let aₙ₁ninBᵣ₀op :=
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₙ₁neaᵢ₁ aₙ₁ninBᵣ₀ (n := 1)
    let aₙ₁ninBᵣ₁op :=
      TypeVar_open_not_mem_freeTypeVars_preservation_of_ne aₙ₁neaᵢ₁ aₙ₁ninBᵣ₁ (n := 1)
    let Bᵣeq := TypeVar_open_inj_of_not_mem_freeTypeVars aᵢ₁ninBᵣ₀ aᵢ₁ninBᵣ₁ <|
      TypeVar_open_inj_of_not_mem_freeTypeVars aₙ₁ninBᵣ₀op aₙ₁ninBᵣ₁op Bᵣopeq

    exact ⟨
      rfl,
      forall.injEq .. |>.mpr ⟨
        «F⊗⊕ω».Kind.arr.injEq .. |>.mpr
          ⟨«F⊗⊕ω».Kind.list.injEq .. |>.mpr <| κ₀e.deterministic κ₁e, rfl⟩,
        arr.injEq .. |>.mpr ⟨
          forall.injEq .. |>.mpr ⟨
            rfl,
            forall.injEq .. |>.mpr ⟨
              κ₀e.deterministic κ₁e,
              forall.injEq .. |>.mpr ⟨
                «F⊗⊕ω».Kind.list.injEq .. |>.mpr <| κ₀e.deterministic κ₁e,
                forall.injEq .. |>.mpr ⟨
                  «F⊗⊕ω».Kind.list.injEq .. |>.mpr <| κ₀e.deterministic κ₁e,
                  forall.injEq .. |>.mpr ⟨
                    «F⊗⊕ω».Kind.list.injEq .. |>.mpr <| κ₀e.deterministic κ₁e,
                    arr.injEq .. |>.mpr ⟨Bₗeq, arr.injEq .. |>.mpr ⟨Bᵣeq, rfl⟩⟩
                  ⟩,
                ⟩,
              ⟩,
            ⟩,
          ⟩,
          arr.injEq .. |>.mpr ⟨
            rfl,
            app.injEq .. |>.mpr ⟨rfl, Aeq⟩
          ⟩
        ⟩
      ⟩
    ⟩
  | .split lift₀ke, .split lift₁ke => lift₀ke.deterministic lift₁ke
termination_by σ.sizeOf'
decreasing_by
  all_goals simp_arith
  · case _ ξ τ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    apply Nat.le_trans <| Nat.le_add_left (τ 0).sizeOf' (ξ 0).sizeOf'
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Std.Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem ⟨Nat.le_refl _, Nat.pos_of_ne_zero nnezero, Nat.mod_one _⟩
  · case _ ξ τ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem imem
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _

mutual

theorem TypeScheme.KindingAndElaboration.soundness (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]])
  (Γcw : [[⊢c Γc]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (κe : [[⊢ κ ⇝ K]]) : [[Δ ⊢ A : K]] := open TypeScheme in
  match σ, σke with
  | .qual (.mono (.var _)), .var aκinΓ => .var <| Γwe.TypeVarIn_preservation aκinΓ κe
  | .qual (.mono (.app ϕ τ)), .app ϕke τke (κ₀ := κ₀) =>
    let ⟨K₀, κ₀e⟩ := κ₀.Elaboration_total
    .app (ϕke.soundness Γcw Γwe (.arr κ₀e κe)) (τke.soundness Γcw Γwe κ₀e)
  | .qual (.mono (.arr τ₀ τ₁)), .arr τ₀ke τ₁ke =>
    let .star := κe
    .arr (τ₀ke.soundness Γcw Γwe .star) (τ₁ke.soundness Γcw Γwe .star)
  | .quant κ' σ', .scheme I σ'ke κ'e =>
    .scheme (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      σ'ke a aninI |>.soundness Γcw (Γwe.typeExt aninΓ κ'e) κe
  | .qual (.qual ψ γ), .qual ϕke γke κe' => by
    cases κe.deterministic κe'
    exact .arr (ϕke.soundness Γcw Γwe .constr) (γke.soundness Γcw Γwe κe')
  | .qual (.mono (.label _)), .label => let .label := κe; .unit
  | .qual (.mono (.floor _)), .floor _ => let .star := κe; .unit
  | .qual (.mono (.comm _)), .comm => let .comm := κe; .unit
  | .qual (.mono (.row ..)), .row _ _ τke _ =>
    let .row κ'e := κe
    .list fun i imem => τke i imem |>.soundness Γcw Γwe κ'e
  | .qual (.mono (.prodOrSum .prod μ ρ)), .prod μke ρke =>
    let .star := κe
    .prod <| ρke.soundness Γcw Γwe <| .row .star
  | .qual (.mono (.prodOrSum .sum μ ρ)), .sum μke ρke =>
    let .star := κe
    .sum <| ρke.soundness Γcw Γwe <| .row .star
  | .qual (.mono (.lift (.mk κ' τ) ρ)), σke =>
    let .row κ₁e := κe
    let .lift I τke κ₀e ρke := σke
    let Aopki : «F⊗⊕ω».Kinding .. := .lam (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      τke a aninI |>.soundness Γcw (Γwe.typeExt aninΓ κ₀e) κ₁e
    .listApp Aopki (ρke.soundness Γcw Γwe κ₀e.row)
  | .qual (.mono (.contain ρ₀ μ ρ₁)), .contain _ ρ₀ke ρ₁ke κ'e (K := K') (A₀ := A₀) (A₁ := A₁) => by
    let .constr := κe
    apply Kinding.prod
    let A i : «Type» := match i with
      | 0 => [[∀ a : K' ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧)]]
      | 1 => [[∀ a : K' ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)]]
      | _ => .list []
    let Δwf := Γwe.soundness Γcw
    let A₀k := ρ₀ke.soundness Γcw Γwe κ'e.row
    let A₁k := ρ₁ke.soundness Γcw Γwe κ'e.row
    have := Kinding.list (Δ := Δ) (A := A) (K := .star) (n := 2)
      fun | 0, _ => .prj_evidence Δwf A₀k A₁k | 1, _ => .inj_evidence Δwf A₀k A₁k
    simp [Range.map, Range.toList, A] at this
    exact this
  | .qual (.mono (.concat ρ₀ μ ρ₁ ρ₂)), .concat _ ρ₀ke ρ₁ke ρ₂ke κ'e containₗ containᵣ (K := K')
      (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (Bₗ := Bₗ) (Bᵣ := Bᵣ) => by
    let .constr := κe
    apply Kinding.prod
    let A i : «Type» := match i with
      | 0 => [[∀ a : K' ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧)]]
      | 1 => [[∀ a : K' ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0]]
      | 2 => Bₗ
      | 3 => Bᵣ
      | _ => .list []
    let Δwf := Γwe.soundness Γcw
    let A₀k := ρ₀ke.soundness Γcw Γwe κ'e.row
    let A₁k := ρ₁ke.soundness Γcw Γwe κ'e.row
    let A₂k := ρ₂ke.soundness Γcw Γwe κ'e.row
    have := Kinding.list (Δ := Δ) (A := A) (K := .star) (n := 4)
      fun
        | 0, _ => .concat_evidence Δwf A₀k A₁k A₂k
        | 1, _ => .elim_evidence Δwf A₀k A₁k A₂k
        | 2, _ => containₗ.soundness Γcw Γwe .constr
        | 3, _ => containᵣ.soundness Γcw Γwe .constr
    simp [Range.map, Range.toList, A] at this
    exact this
  | .qual (.mono (.typeClass _ τ)),
    .tc inΓc τke (κ := κ') (A := A') (Aₛ := Aₛ) (B := B) (n := n) => by
    let .constr := κe
    apply Kinding.prod
    let A'' i := if i = 0 then A'.Type_open B else (Aₛ (i - 1)).Type_open B
    have := Kinding.list (Δ := Δ) (n := n + 1) (A := A'') (K := .star) ?h
    rw [Range.map, Range.toList, if_pos (Nat.zero_lt_succ _), List.map] at this
    simp only at this
    dsimp only [A''] at this
    rw [if_pos rfl, ← Range.map, ← Range.map_shift (Nat.le_refl 1), Nat.sub_self,
        Nat.add_sub_cancel] at this
    exact this
    intro i ⟨_, iltnsucc, _⟩
    dsimp only [A'']
    let ⟨K', κ'e⟩ := κ'.Elaboration_total
    let Bk := τke.soundness Γcw Γwe κ'e
    let ⟨_, κ'e', _, A'k, _, Aₛk⟩ := Γcw.In_inversion inΓc
    cases κ'e.deterministic κ'e'
    split
    · case isTrue h =>
      let ⟨a, anin⟩ := Γ.typeVarDom ++ ↑A'.freeTypeVars |>.exists_fresh
      let ⟨aninΓ, aninA'⟩ := List.not_mem_append'.mp anin
      rw [← Δ.empty_append] at Γwe Bk ⊢
      exact A'k a |>.weakening (Δ := .empty) (Δ'' := .typeExt .empty ..)
       (Γwe.soundness Γcw |>.typeVarExt <| Γwe.TypeVarNotInDom_preservation aninΓ)
        |>.Type_open_preservation (Δ' := .empty) aninA' Bk
    · case isFalse h =>
      let ⟨a, anin⟩ := Γ.typeVarDom ++ ↑(Aₛ (i - 1)).freeTypeVars |>.exists_fresh
      let ⟨aninΓ, aninAₛ⟩ := List.not_mem_append'.mp anin
      rw [Nat.add_comm] at iltnsucc
      have : i - 1 < n := Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h) iltnsucc
      rw [← Δ.empty_append] at Γwe Bk ⊢
      exact Aₛk a (i - 1) ⟨Nat.zero_le _, this, Nat.mod_one _⟩ |>.weakening (Δ := .empty)
        (Δ'' := .typeExt .empty ..)
        (Γwe.soundness Γcw |>.typeVarExt <| Γwe.TypeVarNotInDom_preservation aninΓ)
        |>.Type_open_preservation (Δ' := .empty) aninAₛ Bk
  | .qual (.mono (.all (.mk κ ψ) ρ)), .all I ψke κe' ρke =>
    let .constr := κe
    let Aopki : «F⊗⊕ω».Kinding .. := .lam (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      ψke a aninI |>.soundness Γcw (Γwe.typeExt aninΓ κe') .constr
    .prod <| .listApp Aopki <| ρke.soundness Γcw Γwe κe'.row
  | .qual (.mono (.ind ρ)), .ind I₀ I₁ ρke κ'e keBₗ keBᵣ => by
    let .constr := κe
    apply Kinding.ind_evidence (Γwe.soundness Γcw) (ρke.soundness Γcw Γwe κ'e.row)
      (I₀ := I₀ ++ Γ.typeVarDom) (I₁ := I₁ ++ Γ.typeVarDom)
    · intro aₗ aₗnin aₜ aₜnin aₚ aₚnin aᵢ aᵢnin aₙ aₙnin
      let ⟨aₗninI₀, aₗninΓ⟩ := List.not_mem_append'.mp aₗnin

      let ⟨aₜneaₗ, aₜnin'⟩ := List.not_mem_cons.mp aₜnin
      let ⟨aₜninI₀, aₜninΓ⟩ := List.not_mem_append'.mp aₜnin'
      let aₜninI₀' := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninI₀⟩
      let aₜninΓ' := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninΓ⟩

      let ⟨aₚneaₜ, aₚnin'⟩ := List.not_mem_cons.mp aₚnin
      let ⟨aₚneaₗ, aₚnin''⟩ := List.not_mem_cons.mp aₚnin'
      let ⟨aₚninI₀, aₚninΓ⟩ := List.not_mem_append'.mp aₚnin''
      let aₚninI₀' := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninI₀⟩⟩
      let aₚninΓ' := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninΓ⟩⟩

      let ⟨aᵢneaₚ, aᵢnin'⟩ := List.not_mem_cons.mp aᵢnin
      let ⟨aᵢneaₜ, aᵢnin''⟩ := List.not_mem_cons.mp aᵢnin'
      let ⟨aᵢneaₗ, aᵢnin'''⟩ := List.not_mem_cons.mp aᵢnin''
      let ⟨aᵢninI₀, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin'''
      let aᵢninI₀' := List.not_mem_cons.mpr
        ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninI₀⟩⟩⟩
      let aᵢninΓ' := List.not_mem_cons.mpr
        ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninΓ⟩⟩⟩

      let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
      let ⟨aₙneaₚ, aₙnin''⟩ := List.not_mem_cons.mp aₙnin'
      let ⟨aₙneaₜ, aₙnin'''⟩ := List.not_mem_cons.mp aₙnin''
      let ⟨aₙneaₗ, aₙnin''''⟩ := List.not_mem_cons.mp aₙnin'''
      let ⟨aₙninI₀, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin''''
      let aₙninI₀' := List.not_mem_cons.mpr ⟨
        aₙneaᵢ,
        List.not_mem_cons.mpr
          ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninI₀⟩⟩⟩
      ⟩
      let aₙninΓ' := List.not_mem_cons.mpr ⟨
        aₙneaᵢ,
        List.not_mem_cons.mpr
          ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninΓ⟩⟩⟩
      ⟩

      specialize keBₗ aₗ aₗninI₀ aₜ aₜninI₀' aₚ aₚninI₀' aᵢ aᵢninI₀'
      let Γawe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ' κ'e |>.typeExt aₚninΓ' κ'e.row
        |>.typeExt aᵢninΓ' κ'e.row |>.typeExt aₙninΓ' κ'e.row
      let Bₗki := keBₗ.weakening Γawe (Γ' := .typeExt .empty ..) (Γ'' := .empty)
        |>.soundness Γcw Γawe .constr
      rw [Bₗki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact Bₗki
    · intro aᵢ aᵢnin aₙ aₙnin
      let ⟨aᵢninI₁, aᵢninΓ⟩ := List.not_mem_append'.mp aᵢnin
      let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
      let ⟨aₙninI₁, aₙninΓ⟩ := List.not_mem_append'.mp aₙnin'
      let aₙninI₁' := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninI₁⟩
      let aₙninΓ' := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninΓ⟩
      exact keBᵣ _ aᵢninI₁ _ aₙninI₁' |>.soundness Γcw
        (Γwe.typeExt aᵢninΓ κ'e.row |>.typeExt aₙninΓ' κ'e.row) .constr
  | .qual (.mono (.split «λτ» ρ₀ ρ₁ ρ₂)), σke =>
    let .split concatke := σke
    concatke.soundness Γcw Γwe κe
termination_by Γ.sizeOf' + σ.sizeOf'
decreasing_by
  all_goals simp_arith
  · case _ ξ τ _ _ _ _ _ _ _ _ =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply Nat.le_trans _ <| Nat.le_add_right ..
    apply List.le_sum_of_mem'
    rw [Range.map_eq_of_eq_of_mem (by
      intro j _
      show _ = (ξ j).sizeOf' + (τ j).sizeOf'
      simp only [Function.comp]
    )]
    exact Range.mem_map_of_mem imem
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _
  · rw [TypeEnvironment.append, TypeEnvironment.append, TypeEnvironment.append,
        TypeEnvironment.sizeOf', TypeEnvironment.sizeOf', TypeEnvironment.sizeOf',
        TypeEnvironment.sizeOf', TypeEnvironment.sizeOf']
    simp_arith

theorem TypeEnvironment.WellFormednessAndElaboration.soundness (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  (Γcw : [[⊢c Γc]]) : [[⊢ Δ]] := match Γwe with
  | .empty => .empty
  | .typeExt Γ'we anin κe =>
    Γ'we.soundness Γcw |>.typeVarExt <| Γ'we.TypeVarNotInDom_preservation anin
  | .termExt Γ'we xnin σke => Γ'we.soundness Γcw |>.termVarExt
      (Γ'we.TermVarNotInDom_preservation xnin) (σke.soundness Γcw Γ'we .star)
  | .constrExt Γ'we xnin ψke => Γ'we.soundness Γcw
      |>.termVarExt (Γ'we.TermVarNotInDom_preservation xnin) (ψke.soundness Γcw Γ'we .constr)
termination_by Γ.sizeOf'

end

end TabularTypeInterpreter
