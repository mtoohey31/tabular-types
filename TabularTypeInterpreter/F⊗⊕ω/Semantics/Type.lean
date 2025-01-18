import Lott.Data.Range
import Lott.DSL.Elab.JudgementComprehension
import Lott.DSL.Elab.UniversalJudgement
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment.Basic

namespace TabularTypeInterpreter.«F⊗⊕ω»

def Type.fv : «Type» → List TypeVarId
  | var (.free a) => [a]
  | var _ => []
  | lam _ A => A.fv
  | app A B => A.fv ++ B.fv
  | «forall» _ A => A.fv
  | arr A B => A.fv ++ B.fv
  | list As => As.mapMem (fun A _ => A.fv) |>.flatten
  | listApp A B => A.fv ++ B.fv
  | prod A => A.fv
  | sum A => A.fv

judgement_syntax Δ " ⊢ " A " : " K : Kinding

judgement Kinding :=

a : K ∈ Δ
───────── var
Δ ⊢ a : K

∀ a ∉ I, Δ, a : K₁ ⊢ A^a : K₂
───────────────────────────── lam (I : List TypeVarId)
Δ ⊢ λ a : K₁. A : K₁ ↦ K₂

Δ ⊢ A : K₁ ↦ K₂
Δ ⊢ B : K₁
─────────────── app
Δ ⊢ A B : K₂

∀ a ∉ I, Δ, a : K₁ ⊢ A^a : K₂
───────────────────────────── scheme (I : List TypeVarId)
Δ ⊢ ∀ a : K₁. A : K₂

Δ ⊢ A : *
Δ ⊢ B : *
───────────── arr
Δ ⊢ A → B : *

</ Δ ⊢ A@i : K // i ∈ [:n] />
───────────────────────────────── list
Δ ⊢ {</ A@i // i ∈ [:n] />} : L K

Δ ⊢ A : K₁ ↦ K
Δ ⊢ B : L K₁
──────────────── listApp
Δ ⊢ A ⟦B⟧ : L K₂

Δ ⊢ A : L *
─────────── prod
Δ ⊢ ⊗ A : *

Δ ⊢ A : L *
─────────── sum
Δ ⊢ ⊕ A : *

judgement_syntax Δ " ⊢ " A " ≡ " B : TypeEquivalence

judgement TypeEquivalence :=

───────── refl
Δ ⊢ A ≡ A

Δ ⊢ B : K
───────────────────────── lamAppL
Δ ⊢ (λ a : K. A) B ≡ A^^B

Δ ⊢ B : K
───────────────────────── lamAppR
Δ ⊢ A^^B ≡ (λ a : K. A) B

</ Δ ⊢ B@i : K // i ∈ [:n] />
─────────────────────────────────────────────────────────────────────── lamListAppL
Δ ⊢ (λ a : K. A) ⟦{</ B@i // i ∈ [:n] />}⟧ ≡ {</ A^^B@i // i ∈ [:n] />}

</ Δ ⊢ B@i : K // i ∈ [:n] />
─────────────────────────────────────────────────────────────────────── lamListAppR
Δ ⊢ {</ A^^B@i // i ∈ [:n] />} ≡ (λ a : K. A) ⟦{</ B@i // i ∈ [:n] />}⟧

∀ a ∉ I, Δ, a : K ⊢ A^a ≡ B^a
───────────────────────────── lam (I : List TypeVarId)
Δ ⊢ λ a : K. A ≡ λ a : K. B

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────── app
Δ ⊢ A₁ B₁ ≡ A₂ B₂

∀ a ∉ I, Δ, a : K ⊢ A^a ≡ B^a
───────────────────────────── scheme (I : List TypeVarId)
Δ ⊢ ∀ a : K. A ≡ ∀ a : K. B

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────────── arr
Δ ⊢ A₁ → B₁ ≡ A₂ → B₂

</ Δ ⊢ A@i ≡ B@i // i ∈ [:n] />
───────────────────────────────────────────────────── list
Δ ⊢ {</ A@i // i ∈ [:n] />} ≡ {</ B@i // i ∈ [:n] />}

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────────── listApp
Δ ⊢ A₁ ⟦B₁⟧ ≡ A₂ ⟦B₂⟧

Δ ⊢ A ≡ B
───────────── prod
Δ ⊢ ⊗ A ≡ ⊗ B

Δ ⊢ A ≡ B
───────────── sum
Δ ⊢ ⊕ A ≡ ⊕ B

judgement_syntax Δ " ⊢ " A " ≢ " B : TypeInequivalence

def TypeInequivalence Δ A B := ¬[[Δ ⊢ A ≡ B]]

end TabularTypeInterpreter.«F⊗⊕ω»
