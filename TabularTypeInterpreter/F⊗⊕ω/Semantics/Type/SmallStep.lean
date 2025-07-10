import Lott.Elab.ImpliesJudgement
import Lott.Elab.NotJudgement
import TabularTypeInterpreter.Data.List
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax A " = " B : Type.Eq

def Type.Eq := _root_.Eq (α := «Type»)

judgement_syntax A " ≠ " B : Type.Ne

def Type.Ne := _root_.Ne (α := «Type»)

judgement_syntax "value " A : Type.IsValue

judgement Type.IsValue where

─────── var {a : TypeVarId}
value a

∀ a ∉ I, value A^a
∀ A', A = A' a$0 ⇒ ¬lc_ A'
────────────────────────── lam (I : List TypeVarId)
value λ a : K. A

∀ a ∉ I, value A^a
────────────────── «forall» (I : List TypeVarId)
value ∀ a : K. A

value A
value B
─────────── arr
value A → B

</ value A@i // i in [:n] />
────────────────────────────── list
value {</ A@i // i in [:n] />}

value A
───────── prod
value ⊗ A

value A
───────── sum
value ⊕ A

value A
───────── varApp {a : TypeVarId}
value a A

value A₀ A₁
value B
─────────────── appApp
value (A₀ A₁) B

∀ K, A ≠ λ a : K. a$0
value A
───────────────────── listAppVar {a : TypeVarId}
value A ⟦a⟧

∀ K, A ≠ λ a : K. a$0
value A
value B₀ B₁
───────────────────── listAppApp
value A ⟦B₀ B₁⟧

judgement_syntax Δ " ⊢ " A " -> " B : SmallStep

judgement SmallStep where

Δ ⊢ A : K₁ ↦ K₂
∀ a ∉ I, value A a
──────────────────────── eta (I : List TypeVarId)
Δ ⊢ λ a : K₁. A a$0 -> A

Δ ⊢ λ a : K₁. A : K₁ ↦ K₂
Δ ⊢ B : K₁
value λ a : K₁. A
value B
─────────────────────────── lamApp
Δ ⊢ (λ a : K₁. A) B -> A^^B/a

∀ K, A ≠ λ a : K. a$0
Δ ⊢ A : K₁ ↦ K₂
value A
</ value B@i // i in [:n] />
────────────────────────────────────────────────────────────── listAppList
Δ ⊢ A ⟦{</ B@i // i in [:n] />}⟧ -> {</ A B@i // i in [:n] />}

Δ ⊢ A : L K
value A
─────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ -> A

∀ K', A₀ ≠ λ a : K'. a$0
Δ ⊢ A₁ : K₁ ↦ K₂
value A₀
value A₁ ⟦B⟧
────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦A₁ ⟦B⟧⟧ -> (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧

∀ a ∉ I, Δ, a : K ⊢ A^a -> A'^a
─────────────────────────────── lam (I : List TypeVarId)
Δ ⊢ λ a : K. A -> λ a : K. A'

Δ ⊢ A -> A'
─────────────── appl
Δ ⊢ A B -> A' B

value A
Δ ⊢ B -> B'
─────────────── appr
Δ ⊢ A B -> A B'

∀ a ∉ I, Δ, a : K ⊢ A^a -> A'^a
─────────────────────────────── «forall» (I : List TypeVarId)
Δ ⊢ ∀ a : K. A -> ∀ a : K. A'

Δ ⊢ A -> A'
─────────────────── arrl
Δ ⊢ A → B -> A' → B

value A
Δ ⊢ B -> B'
─────────────────── arrr
Δ ⊢ A → B -> A → B'

</ value A₀@i // i in [:m] />
Δ ⊢ A₁ -> A₁'
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────── list
Δ ⊢ {</ A₀@i // i in [:m] />, A₁, </ A₂@j // j in [:n] />} -> {</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] />}

Δ ⊢ A -> A'
─────────────────── listAppl
Δ ⊢ A ⟦B⟧ -> A' ⟦B⟧

value A
Δ ⊢ B -> B'
─────────────────── listAppr
Δ ⊢ A ⟦B⟧ -> A ⟦B'⟧

Δ ⊢ A -> A'
─────────────── prod
Δ ⊢ ⊗ A -> ⊗ A'

Δ ⊢ A -> A'
─────────────── sum
Δ ⊢ ⊕ A -> ⊕ A'

judgement_syntax Δ " ⊢ " A " ->* " B : MultiSmallStep

judgement MultiSmallStep where

─────────── refl
Δ ⊢ A ->* A

Δ ⊢ A₀ -> A₁
Δ ⊢ A₁ ->* A₂
───────────── step
Δ ⊢ A₀ ->* A₂

judgement_syntax Δ " ⊢ " A " <->* " B : EqSmallStep

judgement EqSmallStep where

──────────── refl
Δ ⊢ A <->* A

Δ ⊢ A -> B
──────────── step
Δ ⊢ A <->* B

Δ ⊢ B <->* A
──────────── symm
Δ ⊢ A <->* B

Δ ⊢ A₀ <->* A₁
Δ ⊢ A₁ <->* A₂
────────────── trans
Δ ⊢ A₀ <->* A₂

end TabularTypeInterpreter.«F⊗⊕ω»
