import Lott.DSL.Elab.UniversalJudgement
import TabularTypeInterpreter.Syntax
import TabularTypeInterpreter.«F⊗⊕ω»

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax "⊢ " κ " ⇝ " K : Kind.Elaboration

judgement Kind.Elaboration :=

─────── star
⊢ * ⇝ *

⊢ κ₀ ⇝ K₀
⊢ κ₁ ⇝ K₁
─────────────────── arr
⊢ κ₀ ↦ κ₁ ⇝ K₀ ↦ K₁

─────── label
⊢ L ⇝ *

─────── comm
⊢ U ⇝ *

⊢ κ ⇝ K
─────────── row
⊢ R κ ⇝ L K

─────── constr
⊢ C ⇝ *

instance : Coe TypeVarId «F⊗⊕ω».TypeVarId where coe a := a

instance : Coe TypeVarId «F⊗⊕ω».TypeVar where coe a := .free a

judgement_syntax a " : " κ " ∈ " Γ : TypeEnvironment.TypeVarIn (id a)

judgement TypeEnvironment.TypeVarIn :=

──────────────── head
a : κ ∈ Γ, a : κ

a ≠ a'
a : κ ∈ Γ
────────────────── typeExt
a : κ ∈ Γ, a' : κ'

a : κ ∈ Γ
──────────────── termExt
a : κ ∈ Γ, x : σ

a : κ ∈ Γ
──────────────── constrExt
a : κ ∈ Γ, ψ ⇝ x

judgement_syntax ℓ " ≠ " ℓ' : Label.Ne

def Label.Ne := _root_.Ne (α := Label)

judgement_syntax "unique" "(" sepBy(ξ, ", ") ")" : Monotype.label.Uniqueness

judgement Monotype.label.Uniqueness :=

</ </ ℓ@i ≠ ℓ@j // j ∈ [i + 1:n] /> // i ∈ [:n] />
────────────────────────────────────────────────── concrete
unique(</ ℓ@i // i ∈ [:n] />)

───────── var
unique(ξ)

judgement_syntax TC " ≠ " TC' : TypeClass.Ne

def TypeClass.Ne := _root_.Ne (α := TypeClass)

judgement_syntax m " ≠ " m' : Member.Ne

def Member.Ne := _root_.Ne (α := Member)

judgement_syntax γc " ∈ " Γc : ClassEnvironment.In

judgement ClassEnvironment.In :=

─────────── head
γc ∈ Γc, γc

(</ TCₛ@i a ⇝ Aₛ@i // i ∈ [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
TC ≠ TC'
m ≠ m'
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ext {TC}
(</ TCₛ@i a ⇝ Aₛ@i // i ∈ [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc, (</ TC'ₛ@i a' ⇝ Aₛ'@i // i ∈ [:m] /> ⇒ TC' a' : κ') ↦ m' : σ' ⇝ A'

def TypeEnvironment.typeVarDom : TypeEnvironment → List TypeVarId
  | .empty => []
  | .typeExt Γ a _ => a :: Γ.typeVarDom
  | .termExt Γ .. => Γ.typeVarDom
  | .constrExt Γ .. => Γ.typeVarDom

def TypeEnvironment.termVarDom : TypeEnvironment → List TermVarId
  | .empty => []
  | .typeExt Γ .. => Γ.termVarDom
  | .termExt Γ x _ => x :: Γ.termVarDom
  | .constrExt Γ _ x => x :: Γ.termVarDom

judgement_syntax a " ∉ " "dom" "(" Γ ")" : TypeEnvironment.TypeVarNotInDom (id a)

def TypeEnvironment.TypeVarNotInDom a (Γ : TypeEnvironment) := a ∉ Γ.typeVarDom

instance : Coe TermVarId «F⊗⊕ω».TermVarId where coe x := x

judgement_syntax x " ∉ " "dom'" "(" Γ ")" : TypeEnvironment.TermVarNotInDom (id x)

def TypeEnvironment.TermVarNotInDom x (Γ : TypeEnvironment) := x ∉ Γ.termVarDom

judgement_syntax Γc "; " Γ " ⊢ " σ " : " κ " ⇝ " A : TypeScheme.KindingAndElaboration

judgement_syntax Γc " ⊢ " Γ " ⇝ " Δ : TypeEnvironment.WellFormednessAndElaboration

judgement_syntax "⊢c " Γc : ClassEnvironment.WellFormedness

mutual

judgement TypeScheme.KindingAndElaboration :=

a : κ ∈ Γ
───────────────── var
Γc; Γ ⊢ a : κ ⇝ a

Γc; Γ ⊢ φ : κ₀ ↦ κ₁ ⇝ A
Γc; Γ ⊢ τ : κ₀ ⇝ B
─────────────────────── app
Γc; Γ ⊢ φ τ : κ₁ ⇝ A B

Γc; Γ ⊢ τ₀ : * ⇝ A
Γc; Γ ⊢ τ₁ : * ⇝ B
─────────────────────────── arr
Γc; Γ ⊢ τ₀ → τ₁ : * ⇝ A → B

Γc; Γ ⊢ ψ : C ⇝ A
Γc; Γ ⊢ γ : κ ⇝ B
⊢ κ ⇝ *
───────────────────────── qual
Γc; Γ ⊢ ψ ⇒ γ : κ ⇝ A → B

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ σ^a : κ₁ ⇝ A^a
⊢ κ₀ ⇝ K₀
─────────────────────────────────────── scheme (I : List TypeVarId)
Γc; Γ ⊢ ∀ a : κ₀. σ : κ₁ ⇝ ∀ a : K₀. A

───────────────────── label
Γc; Γ ⊢ ℓ : L ⇝ ⊗ { }

Γc; Γ ⊢ ξ : L ⇝ A
─────────────────────── floor
Γc; Γ ⊢ ⌊ξ⌋ : * ⇝ ⊗ { }

───────────────────── comm
Γc; Γ ⊢ u : U ⇝ ⊗ { }

</ Γc; Γ ⊢ ξ@i : L ⇝ B@i // i ∈ [:n] />
unique(</ ξ@i // i ∈ [:n] />)
</ Γc; Γ ⊢ τ@i : κ ⇝ A@i // i ∈ [:n] />
───────────────────────────────────────────────────────────────────── row
Γc; Γ ⊢ ⟨</ ξ@i ▹ τ@i // i ∈ [:n] />⟩ : R κ ⇝ {</ A@i // i ∈ [:n] />}

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ : R * ⇝ A
──────────────────────── prod
Γc; Γ ⊢ Π(μ) ρ : * ⇝ ⊗ A

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ : R * ⇝ A
──────────────────────── sum
Γc; Γ ⊢ Σ(μ) ρ : * ⇝ ⊕ A

∀ a ∉ I, Γc; Γ, a : κ₀ ⊢ τ^a : κ₁ ⇝ A^a
⊢ κ₀ ⇝ K₀
Γc; Γ ⊢ ρ : R κ₀ ⇝ B
─────────────────────────────────────────────────────── lift (I : List TypeVarId)
Γc; Γ ⊢ Lift (λ a : κ₀. τ) ρ : R κ₁ ⇝ (λ a : K₀. A) ⟦B⟧

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
⊢ κ ⇝ K
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────── contain
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₁ : C ⇝ ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)}

Γc; Γ ⊢ μ : U ⇝ B
Γc; Γ ⊢ ρ₀ : R κ ⇝ A₀
Γc; Γ ⊢ ρ₁ : R κ ⇝ A₁
Γc; Γ ⊢ ρ₂ : R κ ⇝ A₂
⊢ κ ⇝ K
Γc; Γ ⊢ ρ₀ ≲(μ) ρ₂ : C ⇝ Bₗ
Γc; Γ ⊢ ρ₁ ≲(μ) ρ₂ : C ⇝ Bᵣ
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── concat
Γc; Γ ⊢ ρ₀ ⊙(μ) ρ₁ ~ ρ₂ : C ⇝ ⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0, Bₗ, Bᵣ}

⊢c Γc
(</ TCₛ@i a ⇝ Aₛ@i // i ∈ [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
Γc; Γ ⊢ τ : κ ⇝ B
────────────────────────────────────────────────────────────── tc {TC}
Γc; Γ ⊢ TC τ : C ⇝ ⊗ {A^^B, </ Aₛ@i^^B // i ∈ [:n] /> }

∀ a ∉ I, Γc; Γ, a : κ ⊢ ψ^a : C ⇝ A^a
⊢ κ ⇝ K
Γc; Γ ⊢ ρ : R κ ⇝ B
───────────────────────────────────────────────────── all (I : List TypeVarId)
Γc; Γ ⊢ All (λ a : κ. ψ) ρ : C ⇝ ⊗ ((λ a : K. A) ⟦B⟧)

Γc; Γ ⊢ ρ : R κ ⇝ A
⊢ κ ⇝ K
∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀, Γc; Γ, aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ, aₙ : R κ ⊢ ⟨aₗ ▹ aₜ⟩ ⊙(N) aₚ ~ aᵢ : C ⇝ Bᵣ^aₙ^aᵢ^aₚ^aₜ^aₗ
∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, Γc; Γ, aᵢ : R κ, aₙ : R κ ⊢ aᵢ ⊙(N) aₙ ~ ρ : C ⇝ Bₗ^aₙ^aᵢ
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ind (I₀ I₁)
Γc; Γ ⊢ Ind ρ : C ⇝ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → aₗ$4 → aₘ$5 aₚ$2 → aₘ$5 aₙ$0) → aₘ$5 { } → aₘ$5 A

Γc; Γ ⊢ (Lift (λ a : *. τ) ρ₀) ⊙(C) ρ₁ ~ ρ₂ : C ⇝ A
─────────────────────────────────────────────────── split
Γc; Γ ⊢ Split (λ a : *. τ) ρ₀ ⊙' ρ₁ ~ ρ₂ : C ⇝ A

judgement TypeEnvironment.WellFormednessAndElaboration :=

────────── empty
Γc ⊢ ε ⇝ ε

Γc ⊢ Γ ⇝ Δ
a ∉ dom(Γ)
⊢ κ ⇝ K
──────────────────────── typeExt
Γc ⊢ Γ, a : κ ⇝ Δ, a : K

Γc ⊢ Γ ⇝ Δ
x ∉ dom'(Γ)
Γc; Γ ⊢ σ : * ⇝ A
──────────────────────── termExt
Γc ⊢ Γ, x : σ ⇝ Δ, x : A

Γc ⊢ Γ ⇝ Δ
x ∉ dom'(Γ)
Γc; Γ ⊢ ψ : C ⇝ A
──────────────────────── constrExt
Γc ⊢ Γ, ψ ⇝ x ⇝ Δ, x : A

judgement ClassEnvironment.WellFormedness :=

──── empty
⊢c ε

⊢c Γc
⊢ κ ⇝ K
∀ a, Γc; ε, a : κ ⊢ σ : * ⇝ A^a
∀ a, ε, a : K ⊢ A^a : *
</ ∀ a, Γc; ε, a : κ ⊢ TCₛ@i a : * ⇝ Aₛ@i^a // i ∈ [:n] />
</ ∀ a, ε, a : K ⊢ Aₛ@i^a : * // i ∈ [:n] />
──────────────────────────────────────────────────────────────── ext {TC}
⊢c Γc, (</ TCₛ@i a ⇝ Aₛ@i // i ∈ [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A

end

namespace Kind

theorem Elaboration_total (κ : Kind) : ∃ K, [[⊢ κ ⇝ K]] := match κ with
  | .star => .intro _ .star
  | .arr κ₀ κ₁ =>
    let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
    let ⟨_, κ₁e⟩ := κ₁.Elaboration_total
    .intro _ <| .arr κ₀e κ₁e
  | .label => .intro _ .label
  | .comm => .intro _ .comm
  | .row κ =>
    let ⟨_, κe⟩ := κ.Elaboration_total
    .intro _ <| .row κe
  | .constr => .intro _ .constr

theorem Elaboration.deterministic (κe₀ : [[⊢ κ ⇝ K₀]]) (κe₁ : [[⊢ κ ⇝ K₁]]) : K₀ = K₁ :=
  match κ, κe₀, κe₁ with
  | .star, .star, .star => rfl
  | .arr _ _, .arr κ₀e κ₁e, .arr κ₀e' κ₁e' =>
    let .refl _ := κ₀e.deterministic κ₀e'
    let .refl _ := κ₁e.deterministic κ₁e'
    rfl
  | .label, .label, .label => rfl
  | .comm, .comm, .comm => rfl
  | .row _, .row κ'e, .row κ'e' => let .refl _ := κ'e.deterministic κ'e'; rfl
  | .constr, .constr, .constr => rfl

end Kind

theorem TypeEnvironment.WellFormednessAndElaboration.TypeVarIn_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  (aκinΓ : [[a : κ ∈ Γ]]) (κe : [[⊢ κ ⇝ K]]) : [[a : K ∈ Δ]] :=
  match Γwe, aκinΓ with
  | .typeExt _ _ κe' (K := K'), .head => let .refl _ := κe.deterministic κe'; .head
  | .typeExt Γ'we _ _ (a := a') , .typeExt anea'' aκinΓ' =>
    Γ'we.TypeVarIn_preservation aκinΓ' κe |>.typeVarExt anea''
  | .termExt Γ'we .., .termExt aκinΓ' => Γ'we.TypeVarIn_preservation aκinΓ' κe |>.termVarExt
  | .constrExt Γ'we .., .constrExt aκinΓ' => Γ'we.TypeVarIn_preservation aκinΓ' κe |>.termVarExt

namespace «F⊗⊕ω».Kinding

theorem unit : [[Δ ⊢ ⊗ { } : *]] := by
  have := list (Δ := Δ) (A := fun _ => .list []) (K := .star) (n := 0) (fun _ => nomatch ·)
  simp [Coe.coe, Std.Range.toList] at this
  exact prod this

theorem prj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp [«Type».TypeVar_open]
  apply arr
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
      apply A₁ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
      apply A₀ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin

theorem inj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
      apply A₀ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
      apply A₁ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin

theorem concat_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  (A₂ki : [[Δ ⊢ A₂ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
      apply A₀ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
      rw [Environment.empty_append]
      exact Δwf.typeVarExt anin
  · apply arr
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
        apply A₁ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
        rw [Environment.empty_append]
        exact Δwf.typeVarExt anin
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₂ki.TypeVarLocallyClosed_of.TypeVar_open_eq, ← Δ.empty_append]
        apply A₂ki.weakening (Δ' := .empty) (Δ'' := .typeExt .empty a _)
        rw [Environment.empty_append]
        exact Δwf.typeVarExt anin

theorem elim_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  (A₂ki : [[Δ ⊢ A₂ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0 : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp [«Type».TypeVar_open]
  apply scheme (I := a :: Δ.typeVarDom)
  intro aₜ aₜnin
  let aₜnea := List.ne_of_not_mem_cons aₜnin
  simp [«Type».TypeVar_open]
  apply arr
  · apply arr
    · apply sum
      apply listApp
      · exact var <| .typeVarExt .head aₜnea.symm
      · let A₀lc := A₀ki.TypeVarLocallyClosed_of
        rw [A₀lc.weaken (n := 1) |>.TypeVar_open_eq, A₀lc.TypeVar_open_eq, ← Δ.empty_append]
        apply A₀ki.weakening (Δ' := .empty) (Δ'' := .typeExt (.typeExt .empty a _) aₜ _)
        rw [Environment.empty_append]
        exact Δwf.typeVarExt anin |>.typeVarExt aₜnin
    · exact var .head
  · apply arr
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₁lc := A₁ki.TypeVarLocallyClosed_of
          rw [A₁lc.weaken (n := 1) |>.TypeVar_open_eq, A₁lc.TypeVar_open_eq, ← Δ.empty_append]
          apply A₁ki.weakening (Δ' := .empty) (Δ'' := .typeExt (.typeExt .empty a _) aₜ _)
          rw [Environment.empty_append]
          exact Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₂lc := A₂ki.TypeVarLocallyClosed_of
          rw [A₂lc.weaken (n := 1) |>.TypeVar_open_eq, A₂lc.TypeVar_open_eq, ← Δ.empty_append]
          apply A₂ki.weakening (Δ' := .empty) (Δ'' := .typeExt (.typeExt .empty a _) aₜ _)
          rw [Environment.empty_append]
          exact Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head

theorem ind_evidence (Δwf : [[⊢ Δ]])
  (Bᵣki : [[Δ, aₗ : *, aₜ : K, aₚ : L K, aᵢ : L K, aₙ : L K ⊢ Bᵣ^aₙ^aᵢ^aₚ^aₜ^aₗ : *]])
  (Bₗki : [[Δ, aᵢ : L K, aₙ : L K ⊢ Bₗ^aₙ^aᵢ : *]])
  : [[Δ ⊢ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → aₗ$4 → aₘ$5 aₚ$2 → aₘ$5 aₙ$0) → aₘ$5 { } → aₘ$5 A : *]] := sorry

end «F⊗⊕ω».Kinding

mutual

@[simp]
theorem TypeLambda.TypeVar_open_sizeOf («λτ» : TypeLambda)
  : sizeOf («λτ».TypeVar_open a n) = sizeOf «λτ» := open TypeLambda in by
  let .mk κ τ := «λτ»
  rw [TypeVar_open, mk.sizeOf_spec, mk.sizeOf_spec, τ.TypeVar_open_sizeOf]

@[simp]
theorem Monotype.TypeVar_open_sizeOf (τ : Monotype) : sizeOf (τ.TypeVar_open a n) = sizeOf τ :=
  open Monotype in by
  match τ with
  | .var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [var.sizeOf_spec, var.sizeOf_spec, ← h]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | .var (.free _) =>
    rw [TypeVar_open]
    split <;> rfl
  | .app φ τ =>
    rw [TypeVar_open, app.sizeOf_spec, app.sizeOf_spec, φ.TypeVar_open_sizeOf,
        τ.TypeVar_open_sizeOf]
  | .arr τ₀ τ₁ =>
    rw [TypeVar_open, arr.sizeOf_spec, arr.sizeOf_spec, τ₀.TypeVar_open_sizeOf,
        τ₁.TypeVar_open_sizeOf]
  | .label _ => rw [TypeVar_open]
  | .floor ξ => rw [TypeVar_open, floor.sizeOf_spec, floor.sizeOf_spec, ξ.TypeVar_open_sizeOf]
  | .comm _ => rw [TypeVar_open]
  | .row ξτs =>
    rw [TypeVar_open, List.mapMem_eq_map]
    match ξτs with
    | [] => rw [List.map]
    | (ξ, τ) :: ξτs' =>
      rw [List.map, row.sizeOf_spec, row.sizeOf_spec, List.cons.sizeOf_spec, List.cons.sizeOf_spec,
          Prod.mk.sizeOf_spec, Prod.mk.sizeOf_spec, ξ.TypeVar_open_sizeOf, τ.TypeVar_open_sizeOf]
      have : sizeOf ((row ξτs').TypeVar_open a n) = sizeOf (row ξτs') :=
        (row ξτs').TypeVar_open_sizeOf
      rw [TypeVar_open, List.mapMem_eq_map, row.sizeOf_spec, row.sizeOf_spec] at this
      rw [Nat.add_comm (n := 1) (m := (1 + sizeOf ξ + _)), Nat.add_assoc, this,
          ← Nat.add_assoc (m := 1), ← Nat.add_comm (n := 1) (m := (1 + sizeOf ξ + _))]
  | .prod μ ρ =>
    rw [TypeVar_open, prod.sizeOf_spec, prod.sizeOf_spec, μ.TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .sum μ ρ =>
    rw [TypeVar_open, sum.sizeOf_spec, sum.sizeOf_spec, μ.TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .lift «λτ» ρ =>
    rw [TypeVar_open, lift.sizeOf_spec, lift.sizeOf_spec, «λτ».TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .contain ρ₀ μ ρ₁ =>
    rw [TypeVar_open, contain.sizeOf_spec, contain.sizeOf_spec, ρ₀.TypeVar_open_sizeOf,
        μ.TypeVar_open_sizeOf, ρ₁.TypeVar_open_sizeOf]
  | .concat ρ₀ μ ρ₁ ρ₂ =>
    rw [TypeVar_open, concat.sizeOf_spec, concat.sizeOf_spec, ρ₀.TypeVar_open_sizeOf,
        μ.TypeVar_open_sizeOf, ρ₁.TypeVar_open_sizeOf, ρ₂.TypeVar_open_sizeOf]
  | .typeClass _ τ =>
    rw [TypeVar_open, typeClass.sizeOf_spec, typeClass.sizeOf_spec, τ.TypeVar_open_sizeOf]
  | .all «λτ» ρ =>
    rw [TypeVar_open, all.sizeOf_spec, all.sizeOf_spec, «λτ».TypeVar_open_sizeOf,
        ρ.TypeVar_open_sizeOf]
  | .ind ρ => rw [TypeVar_open, ind.sizeOf_spec, ind.sizeOf_spec, ρ.TypeVar_open_sizeOf]
  | .split «λτ» ρ₀ ρ₁ ρ₂ =>
    rw [TypeVar_open, split.sizeOf_spec, split.sizeOf_spec, «λτ».TypeVar_open_sizeOf,
        ρ₀.TypeVar_open_sizeOf, ρ₁.TypeVar_open_sizeOf, ρ₂.TypeVar_open_sizeOf]

end

@[simp]
theorem Monotype.sizeOf_pos (τ : Monotype) : 0 < sizeOf τ := by cases τ <;> simp_arith

mutual

@[simp]
noncomputable
def TypeLambda.sizeOf' : TypeLambda → Nat | .mk κ τ => 1 + sizeOf κ + τ.sizeOf'

@[simp]
noncomputable
def Monotype.sizeOf' : Monotype → Nat
  | .var a => 1 + sizeOf a
  | .app φ τ => 1 + φ.sizeOf' + τ.sizeOf'
  | .arr τ₀ τ₁ => 1 + τ₀.sizeOf' + τ₁.sizeOf'
  | .label ℓ => 1 + sizeOf ℓ
  | .floor ξ => 1 + ξ.sizeOf'
  | .comm u => 1 + sizeOf u
  | .row ξτs => 1 + (List.sum <| ξτs.mapMem fun (ξ, τ) _ => ξ.sizeOf' + τ.sizeOf')
  | .prod μ ρ => 1 + μ.sizeOf' + ρ.sizeOf'
  | .sum μ ρ => 1 + μ.sizeOf' + ρ.sizeOf'
  | .lift «λτ» ρ => 1 + «λτ».sizeOf' + ρ.sizeOf'
  | .contain ρ₀ μ ρ₁ => 1 + ρ₀.sizeOf' + μ.sizeOf' + ρ₁.sizeOf'
  | .concat ρ₀ μ ρ₁ ρ₂ => 1 + ρ₀.sizeOf' + μ.sizeOf' + ρ₁.sizeOf' + ρ₂.sizeOf'
  | .typeClass _ τ => 1 + τ.sizeOf'
  | .all «λτ» ρ => 1 + «λτ».sizeOf' + ρ.sizeOf'
  | .ind ρ => 14 + ρ.sizeOf'
  | .split «λτ» ρ₀ ρ₁ ρ₂ => 5 + «λτ».sizeOf' + ρ₀.sizeOf' + ρ₁.sizeOf' + ρ₂.sizeOf'

end

@[simp]
theorem Monotype.sizeOf'_pos (τ : Monotype) : 0 < τ.sizeOf' := by cases τ <;> simp_arith [sizeOf']

mutual

@[simp]
theorem TypeLambda.TypeVar_open_sizeOf' («λτ» : TypeLambda)
  : («λτ».TypeVar_open a n).sizeOf' = «λτ».sizeOf' := open TypeLambda in by
  let .mk κ τ := «λτ»
  rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']

@[simp]
theorem Monotype.TypeVar_open_sizeOf' (τ : Monotype) : (τ.TypeVar_open a n).sizeOf' = τ.sizeOf' :=
  open Monotype in by
  match τ with
  | .var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [sizeOf', sizeOf', ← h]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | .var (.free _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      rw [sizeOf', sizeOf']
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse h => rfl
  | .app φ τ =>
    rw [TypeVar_open, sizeOf', sizeOf', φ.TypeVar_open_sizeOf', τ.TypeVar_open_sizeOf']
  | .arr τ₀ τ₁ =>
    rw [TypeVar_open, sizeOf', sizeOf', τ₀.TypeVar_open_sizeOf', τ₁.TypeVar_open_sizeOf']
  | .label _ => rw [TypeVar_open]
  | .floor ξ => rw [TypeVar_open, sizeOf', sizeOf', ξ.TypeVar_open_sizeOf']
  | .comm _ => rw [TypeVar_open]
  | .row ξτs =>
    rw [TypeVar_open, List.mapMem_eq_map]
    match ξτs with
    | [] => rw [List.map]
    | (ξ, τ) :: ξτs' =>
      rw [List.map, sizeOf', sizeOf', List.mapMem_eq_map, List.map_cons, List.sum_cons,
          ξ.TypeVar_open_sizeOf', τ.TypeVar_open_sizeOf']
      have : ((row ξτs').TypeVar_open a n).sizeOf' = (row ξτs').sizeOf' :=
        (row ξτs').TypeVar_open_sizeOf'
      rw [TypeVar_open, List.mapMem_eq_map, sizeOf', sizeOf', List.mapMem_eq_map] at this
      rw [← Nat.add_assoc, Nat.add_comm (n := 1), Nat.add_assoc, this, List.mapMem, List.sum_cons,
          ← Nat.add_assoc, Nat.add_comm (m := 1), Nat.add_assoc]
  | .prod μ ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', μ.TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .sum μ ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', μ.TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .lift «λτ» ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', «λτ».TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .contain ρ₀ μ ρ₁ =>
    rw [TypeVar_open, sizeOf', sizeOf', ρ₀.TypeVar_open_sizeOf', μ.TypeVar_open_sizeOf',
        ρ₁.TypeVar_open_sizeOf']
  | .concat ρ₀ μ ρ₁ ρ₂ =>
    rw [TypeVar_open, sizeOf', sizeOf', ρ₀.TypeVar_open_sizeOf', μ.TypeVar_open_sizeOf',
        ρ₁.TypeVar_open_sizeOf', ρ₂.TypeVar_open_sizeOf']
  | .typeClass _ τ =>
    rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']
  | .all «λτ» ρ =>
    rw [TypeVar_open, sizeOf', sizeOf', «λτ».TypeVar_open_sizeOf', ρ.TypeVar_open_sizeOf']
  | .ind ρ => rw [TypeVar_open, sizeOf', sizeOf', ρ.TypeVar_open_sizeOf']
  | .split «λτ» ρ₀ ρ₁ ρ₂ =>
    rw [TypeVar_open, sizeOf', sizeOf', «λτ».TypeVar_open_sizeOf', ρ₀.TypeVar_open_sizeOf',
        ρ₁.TypeVar_open_sizeOf', ρ₂.TypeVar_open_sizeOf']

end
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
noncomputable
def sizeOf' : QualifiedType → Nat
  | .mono τ => 1 + τ.sizeOf'
  | .qual ψ γ => 1 + ψ.sizeOf' + γ.sizeOf'

@[simp]
theorem sizeOf'_pos (γ : QualifiedType) : 0 < γ.sizeOf' := by cases γ <;> simp_arith [sizeOf']

@[simp]
theorem TypeVar_open_sizeOf' (γ : QualifiedType) : (γ.TypeVar_open a n).sizeOf' = γ.sizeOf' := by
  match γ with
  | .mono τ => rw [TypeVar_open, sizeOf', sizeOf', τ.TypeVar_open_sizeOf']
  | .qual ψ γ => rw [TypeVar_open, sizeOf', sizeOf', ψ.TypeVar_open_sizeOf', γ.TypeVar_open_sizeOf']

end QualifiedType

theorem ClassEnvironment.WellFormedness.ext_eliml (Γcγcw : [[⊢c Γc, γc]]) : [[⊢c Γc]] :=
  let .ext Γcw .. := Γcγcw
  Γcw

namespace TypeScheme

@[simp]
theorem TypeVar_open_sizeOf (σ : TypeScheme) : sizeOf (σ.TypeVar_open a n) = sizeOf σ := by
  match σ with
  | .qual γ => rw [TypeVar_open, qual.sizeOf_spec, qual.sizeOf_spec, γ.TypeVar_open_sizeOf]
  | .quant _ σ => rw [TypeVar_open, quant.sizeOf_spec, quant.sizeOf_spec, σ.TypeVar_open_sizeOf]

@[simp]
noncomputable
def sizeOf' : TypeScheme → Nat
  | .qual γ => 1 + γ.sizeOf'
  | .quant _ σ => 2 + σ.sizeOf'

@[simp]
theorem sizeOf'_pos (σ : TypeScheme) : 0 < σ.sizeOf' := by cases σ <;> simp_arith [sizeOf']

@[simp]
theorem TypeVar_open_sizeOf' (σ : TypeScheme) : (σ.TypeVar_open a n).sizeOf' = σ.sizeOf' := by
  match σ with
  | .qual γ => rw [TypeVar_open, sizeOf', sizeOf', γ.TypeVar_open_sizeOf']
  | .quant _ σ => rw [TypeVar_open, sizeOf', sizeOf', σ.TypeVar_open_sizeOf']

theorem of_ClassEnvironmentWellFormedness_of_ClassEnvironment_in {TC} (Γcw : [[⊢c Γc]])
  (TCin : [[(</ TCₛ@i a ⇝ Aₛ@i // i ∈ [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc]]) (κe : [[⊢ κ ⇝ K]])
  : ∀ a, [[ε, a : K ⊢ A^a : *]] ∧ ∀ i ∈ [:n], [[ε, a : K ⊢ Aₛ@i^a : *]] := by
  intro a
  generalize γceq : ClassEnvironmentEntry.mk
    (List.map (fun i => [(TCₛ i, Aₛ i)]) (Coe.coe [:n])).flatten TC κ m σ A = γc at TCin
  match TCin with
  | .head =>
    let .ext _ κ'e _ Aopki _ Aₛopki := Γcw
    let ⟨TCₛAₛeq, _, κeqκ', _, _, AeqA'⟩ := ClassEnvironmentEntry.mk.inj γceq
    cases κeqκ'
    cases AeqA'
    cases κe.deterministic κ'e
    exact ⟨
      Aopki a,
      fun i inin => by
        rw [List.map_singleton_flatten, List.map_singleton_flatten] at TCₛAₛeq
        let length_eq : List.length (List.map _ _) = List.length _ := by rw [TCₛAₛeq]
        dsimp [Coe.coe] at length_eq
        rw [List.length_map, List.length_map, Std.Range.length_toList, Std.Range.length_toList,
            Nat.sub_zero, Nat.sub_zero] at length_eq
        cases length_eq
        rw [And.right <| Prod.mk.inj <| Std.Range.eq_of_mem_of_map_eq' TCₛAₛeq i inin]
        exact Aₛopki i inin a
    ⟩
  | .ext TCin' .. =>
    let ⟨TCₛAₛeq, _, κeqκ', _, _, AeqA'⟩ := ClassEnvironmentEntry.mk.inj γceq
    cases κeqκ'
    cases AeqA'
    let ⟨Aopki, Aₛopki⟩ :=
      of_ClassEnvironmentWellFormedness_of_ClassEnvironment_in Γcw.ext_eliml TCin' κe a
    exact ⟨
      Aopki,
      fun i inin => by
        rw [List.map_singleton_flatten, List.map_singleton_flatten] at TCₛAₛeq
        let length_eq : List.length (List.map _ _) = List.length _ := by rw [TCₛAₛeq]
        dsimp [Coe.coe] at length_eq
        rw [List.length_map, List.length_map, Std.Range.length_toList, Std.Range.length_toList,
            Nat.sub_zero, Nat.sub_zero] at length_eq
        cases length_eq
        rw [And.right <| Prod.mk.inj <| Std.Range.eq_of_mem_of_map_eq' TCₛAₛeq i inin]
        exact Aₛopki i inin
    ⟩

end TypeScheme

namespace TypeEnvironment

@[simp]
noncomputable
def sizeOf' : TypeEnvironment → Nat
  | .empty => 1
  | .typeExt Γ _ _ => 1 + Γ.sizeOf'
  | .termExt Γ _ σ => 1 + Γ.sizeOf' + σ.sizeOf'
  | .constrExt Γ ψ _ => 3 + Γ.sizeOf' + ψ.sizeOf'

namespace WellFormednessAndElaboration

theorem TypeVarNotInDom_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (anin : [[a ∉ dom(Γ)]])
  : [[a ∉ dom(Δ)]] := fun ainΔ => match Γwe with
  | .empty => nomatch ainΔ
  | .typeExt Γ'we .. => match List.mem_cons.mp ainΔ with
    | .inl (.refl _) => anin <| .head _
    | .inr ainΔ' => Γ'we.TypeVarNotInDom_preservation (List.not_mem_of_not_mem_cons anin) ainΔ'
  | .termExt Γ'we .. | .constrExt Γ'we .. => Γ'we.TypeVarNotInDom_preservation anin ainΔ

theorem TermVarNotInDom_preservation (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (xnin : [[x ∉ dom'(Γ)]])
  : [[x ∉ dom(Δ)]] := fun xinΔ => match Γwe with
  | .empty => nomatch xinΔ
  | .typeExt Γ'we .. => Γ'we.TermVarNotInDom_preservation xnin xinΔ
  | .termExt Γ'we .. | .constrExt Γ'we .. => match List.mem_cons.mp xinΔ with
    | .inl (.refl _) => xnin <| .head _
    | .inr xinΔ' => Γ'we.TermVarNotInDom_preservation (List.not_mem_of_not_mem_cons xnin) xinΔ'

end WellFormednessAndElaboration

end TypeEnvironment

mutual

theorem TypeScheme.KindingAndElaboration.soundness (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (κe : [[⊢ κ ⇝ K]]) : [[Δ ⊢ A : K]] := open TypeScheme in match σ, σke with
  | .qual (.mono (.var _)), .var aκinΓ => .var <| Γwe.TypeVarIn_preservation aκinΓ κe
  | .qual (.mono (.app φ τ)), .app φke τke (κ₀ := κ₀) =>
    let ⟨K₀, κ₀e⟩ := κ₀.Elaboration_total
    .app (φke.soundness Γwe (.arr κ₀e κe)) (τke.soundness Γwe κ₀e)
  | .qual (.mono (.arr τ₀ τ₁)), .arr τ₀ke τ₁ke =>
    let .star := κe
    .arr (τ₀ke.soundness Γwe .star) (τ₁ke.soundness Γwe .star)
  | .quant κ' σ', .scheme I σ'ke κ'e =>
    .scheme (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      σ'ke a aninI |>.soundness (Γwe.typeExt aninΓ κ'e) κe
  | .qual (.qual ψ γ), .qual φke γke κe' => by
    cases κe.deterministic κe'
    exact .arr (φke.soundness Γwe .constr) (γke.soundness Γwe κe')
  | .qual (.mono (.label _)), .label => let .label := κe; .unit
  | .qual (.mono (.floor _)), .floor _ => let .star := κe; .unit
  | .qual (.mono (.comm _)), .comm => let .comm := κe; .unit
  | .qual (.mono (.row ..)), .row _ _ τke =>
    let .row κ'e := κe
    .list fun i imem => τke i imem |>.soundness Γwe κ'e
  | .qual (.mono (.prod μ ρ)), .prod μke ρke =>
    let .star := κe
    .prod <| ρke.soundness Γwe <| .row .star
  | .qual (.mono (.sum μ ρ)), .sum μke ρke =>
    let .star := κe
    .sum <| ρke.soundness Γwe <| .row .star
  | .qual (.mono (.lift (.mk κ' τ) ρ)), σke =>
    let .row κ₁e := κe
    let .lift I τke κ₀e ρke := σke
    let Aopki : «F⊗⊕ω».Kinding .. := .lam (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      τke a aninI |>.soundness (Γwe.typeExt aninΓ κ₀e) κ₁e
    .listApp Aopki (ρke.soundness Γwe κ₀e.row)
  | .qual (.mono (.contain ρ₀ μ ρ₁)), .contain _ ρ₀ke ρ₁ke κ'e (K := K') (A₀ := A₀) (A₁ := A₁) => by
    let .constr := κe
    apply Kinding.prod
    let A i : «Type» := match i with
      | 0 => [[∀ a : K' ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧)]]
      | 1 => [[∀ a : K' ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)]]
      | _ => .list []
    let Δwf := Γwe.soundness
    let A₀k := ρ₀ke.soundness Γwe κ'e.row
    let A₁k := ρ₁ke.soundness Γwe κ'e.row
    have := Kinding.list (Δ := Δ) (A := A) (K := .star) (n := 2)
      fun | 0, _ => .prj_evidence Δwf A₀k A₁k | 1, _ => .inj_evidence Δwf A₀k A₁k
    simp [Coe.coe, Std.Range.toList, A] at this
    exact this
  | .qual (.mono (.concat ρ₀ μ ρ₁ ρ₂)), .concat _ ρ₀ke ρ₁ke ρ₂ke κ'e containl containr (K := K')
      (A₀ := A₀) (A₁ := A₁) (A₂ := A₂) (Bₗ := Bₗ) (Bᵣ := Bᵣ) => by
    let .constr := κe
    apply Kinding.prod
    let A i : «Type» := match i with
      | 0 => [[∀ a : K' ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧)]]
      | 1 => [[∀ a : K' ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0]]
      | 2 => Bₗ
      | 3 => Bᵣ
      | _ => .list []
    let Δwf := Γwe.soundness
    let A₀k := ρ₀ke.soundness Γwe κ'e.row
    let A₁k := ρ₁ke.soundness Γwe κ'e.row
    let A₂k := ρ₂ke.soundness Γwe κ'e.row
    have := Kinding.list (Δ := Δ) (A := A) (K := .star) (n := 4)
      fun
        | 0, _ => .concat_evidence Δwf A₀k A₁k A₂k
        | 1, _ => .elim_evidence Δwf A₀k A₁k A₂k
        | 2, _ => containl.soundness Γwe .constr
        | 3, _ => containr.soundness Γwe .constr
    simp [Coe.coe, Std.Range.toList, A] at this
    exact this
  | .qual (.mono (.typeClass _ τ)),
    .tc Γcw inΓc τke (κ := κ') (A := A') (Aₛ := Aₛ) (B := B) (n := n) => by
    let .constr := κe
    apply Kinding.prod
    let A'' i := if i = 0 then A'.Type_open B else (Aₛ (i - 1)).Type_open B
    have := Kinding.list (Δ := Δ) (n := n + 1) (A := A'') (K := .star) ?h
    rw [List.map_singleton_flatten] at *
    dsimp only [Coe.coe] at this
    rw [Std.Range.toList, if_neg (nomatch ·), if_pos (Nat.zero_lt_succ _), List.map] at this
    simp only at this
    dsimp only [A''] at this
    rw [if_pos rfl, ← Std.Range.map_shift (Nat.le_refl 1), Nat.sub_self, Nat.add_sub_cancel] at this
    exact this
    intro i ⟨_, iltnsucc⟩
    dsimp only [A'']
    let ⟨K', κ'e⟩ := κ'.Elaboration_total
    let Bk := τke.soundness Γwe κ'e
    split
    · case isTrue h =>
      let ⟨a, anin⟩ := Γ.typeVarDom ++ ↑A'.fv |>.exists_fresh
      let ⟨aninΓ, aninA'⟩ := List.not_mem_append'.mp anin
      let ⟨A'k, _⟩ := of_ClassEnvironmentWellFormedness_of_ClassEnvironment_in Γcw inΓc κ'e a
      exact A'k.weakening (Γwe.soundness.typeVarExt <| Γwe.TypeVarNotInDom_preservation aninΓ)
        (Δ'' := .empty) |>.Type_open_preservation (Δ' := .empty) aninA' Bk
    · case isFalse h =>
      let ⟨a, anin⟩ := Γ.typeVarDom ++ ↑(Aₛ (i - 1)).fv |>.exists_fresh
      let ⟨aninΓ, aninAₛ⟩ := List.not_mem_append'.mp anin
      let ⟨_, Aₛke⟩ := of_ClassEnvironmentWellFormedness_of_ClassEnvironment_in Γcw inΓc κ'e a
      rw [Nat.add_comm] at iltnsucc
      have : i - 1 < n := Nat.sub_lt_left_of_lt_add (Nat.pos_of_ne_zero h) iltnsucc
      exact Aₛke (i - 1) ⟨Nat.zero_le _, this⟩
        |>.weakening (Γwe.soundness.typeVarExt <| Γwe.TypeVarNotInDom_preservation aninΓ)
          (Δ'' := .empty) |>.Type_open_preservation (Δ' := .empty) aninAₛ Bk
  | .qual (.mono (.all (.mk κ ψ) ρ)), .all I ψke κe' ρke =>
    let .constr := κe
    let Aopki : «F⊗⊕ω».Kinding .. := .lam (I := Γ.typeVarDom ++ I) fun a anin =>
      let ⟨aninΓ, aninI⟩ := List.not_mem_append'.mp anin
      ψke a aninI |>.soundness (Γwe.typeExt aninΓ κe') .constr
    .prod <| .listApp Aopki <| ρke.soundness Γwe κe'.row
  | .qual (.mono (.ind ρ)), .ind I₀ I₁ ρke κ'e Bᵣke Bₗke =>
    let .constr := κe
    let ⟨aₗ, aₗnin⟩ := Γ.typeVarDom ++ I₀ |>.exists_fresh
    let ⟨aₗninΓ, aₗnin₀⟩ := List.not_mem_append'.mp aₗnin
    let Γₗ := Γ.typeExt aₗ _
    let I₀ₗ : List TypeVarId := aₗ :: I₀
    let ⟨aₜ, aₜnin⟩ := Γₗ.typeVarDom ++ I₀ₗ |>.exists_fresh
    let ⟨aₜninΓ, aₜnin₀⟩ := List.not_mem_append'.mp aₜnin
    let Γₗₜ := Γₗ.typeExt aₜ _
    let I₀ₗₜ : List TypeVarId := aₜ :: I₀ₗ
    let ⟨aₚ, aₚnin⟩ := Γₗₜ.typeVarDom ++ I₀ₗₜ |>.exists_fresh
    let ⟨aₚninΓ, aₚnin₀⟩ := List.not_mem_append'.mp aₚnin
    let Γₗₜₚ := Γₗₜ.typeExt aₚ _
    let I₀ₗₜₚ : List TypeVarId := aₚ :: I₀ₗₜ
    let ⟨aᵢ, aᵢnin⟩ := Γₗₜₚ.typeVarDom ++ I₀ₗₜₚ ++ I₁ |>.exists_fresh
    let ⟨aᵢninΓₗₜₚ₀, aᵢnin₁⟩ := List.not_mem_append'.mp aᵢnin
    let ⟨aᵢninΓₗₜₚ, aᵢnin₀⟩ := List.not_mem_append'.mp aᵢninΓₗₜₚ₀
    let aᵢninΓ := List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons
      <| List.not_mem_of_not_mem_cons <| aᵢninΓₗₜₚ
    let Γₗₜₚᵢ := Γₗₜₚ.typeExt aᵢ _
    let I₀ₗₜₚᵢ : List TypeVarId := aᵢ :: I₀ₗₜₚ
    let I₁ᵢ : List TypeVarId := aᵢ :: I₁
    let ⟨aₙ, aₙnin⟩ := Γₗₜₚᵢ.typeVarDom ++ I₀ₗₜₚᵢ ++ I₁ᵢ |>.exists_fresh
    let ⟨aₙninΓₗₜₚᵢ₀, aₙnin₁⟩ := List.not_mem_append'.mp aₙnin
    let ⟨aₙninΓₗₜₚᵢ, aₙnin₀⟩ := List.not_mem_append'.mp aₙninΓₗₜₚᵢ₀
    let ⟨aₙneaᵢ, aₙninΓₗₜₚ⟩ := List.ne_and_not_mem_of_not_mem_cons aₙninΓₗₜₚᵢ
    let aₙninΓ := List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons
      <| List.not_mem_of_not_mem_cons <| aₙninΓₗₜₚ
    let aₙninΓᵢ := List.not_mem_cons_of_ne_of_not_mem aₙneaᵢ aₙninΓ
    let Γₗₜₚᵢₙwe := Γwe.typeExt aₗninΓ .label |>.typeExt aₜninΓ κ'e |>.typeExt aₚninΓ κ'e.row
      |>.typeExt aᵢninΓₗₜₚ κ'e.row |>.typeExt aₙninΓₗₜₚᵢ κ'e.row
    let Γᵢₙwe := Γwe.typeExt aᵢninΓ κ'e.row |>.typeExt aₙninΓᵢ κ'e.row
    .ind_evidence Γwe.soundness
      (Bᵣke aₗ aₗnin₀ aₜ aₜnin₀ aₚ aₚnin₀ aᵢ aᵢnin₀ aₙ aₙnin₀ |>.soundness Γₗₜₚᵢₙwe .constr)
      (Bₗke aᵢ aᵢnin₁ aₙ aₙnin₁ |>.soundness Γᵢₙwe .constr)
  | .qual (.mono (.split «λτ» ρ₀ ρ₁ ρ₂)), σke =>
    let .split concatke := σke
    concatke.soundness Γwe κe
termination_by Γ.sizeOf' + σ.sizeOf'
decreasing_by
  all_goals simp_arith [List.mapMem]
  · case _ ξ _ τ _ _ _ _ _ _ =>
    apply Nat.le_trans <| Nat.le_add_left (τ i).sizeOf' (ξ i).sizeOf'
    apply List.le_sum_of_mem
    rw [List.map_singleton_flatten, List.mapMem_eq_map, List.map_map]
    exact Std.Range.mem_map_of_mem imem
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _

theorem TypeEnvironment.WellFormednessAndElaboration.soundness (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) : [[⊢ Δ]] :=
  match Γwe with
  | .empty => .empty
  | .typeExt Γ'we anin κe => Γ'we.soundness.typeVarExt <| Γ'we.TypeVarNotInDom_preservation anin
  | .termExt Γ'we xnin σke =>
    Γ'we.soundness.termVarExt (Γ'we.TermVarNotInDom_preservation xnin) (σke.soundness Γ'we .star)
  | .constrExt Γ'we xnin ψke =>
    Γ'we.soundness.termVarExt (Γ'we.TermVarNotInDom_preservation xnin) (ψke.soundness Γ'we .constr)
termination_by Γ.sizeOf'

end

end TabularTypeInterpreter
