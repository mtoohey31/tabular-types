import Lott.Data.Range
import Lott.Elab.JudgementComprehension
import Lott.Elab.UniversalJudgement
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment.Basic
import TabularTypeInterpreter.RuleSets

namespace TabularTypeInterpreter.«F⊗⊕ω»

termonly
def Type.TypeVar_multi_open (A : «Type») (a : Nat → TypeVarId) : Nat → «Type»
  | 0 => A
  | n + 1 => A.TypeVar_open (a n) n |>.TypeVar_multi_open a n

termonly
def Type.Type_multi_open (A : «Type») (B : Nat → «Type») : Nat → «Type»
  | 0 => A
  | n + 1 => A.Type_open (B n) n |>.Type_multi_open B n

judgement_syntax Δ " ⊢ " A " : " K : Kinding

judgement Kinding where

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

∀ a ∉ I, Δ, a : K ⊢ A^a : *
─────────────────────────── scheme (I : List TypeVarId)
Δ ⊢ ∀ a : K. A : *

Δ ⊢ A : *
Δ ⊢ B : *
───────────── arr
Δ ⊢ A → B : *

</ Δ ⊢ A@i : K // i in [:n] notex />
──────────────────────────────────────── list
Δ ⊢ {</ A@i // i in [:n] notex />} : L K

Δ ⊢ A : K₁ ↦ K₂
Δ ⊢ B : L K₁
──────────────── listApp
Δ ⊢ A ⟦B⟧ : L K₂

Δ ⊢ A : L *
─────────── prod
Δ ⊢ ⊗ A : *

Δ ⊢ A : L *
─────────── sum
Δ ⊢ ⊕ A : *

namespace Kinding

@[app_unexpander Kinding]
def delabK: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let colon := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ":") }
    `([ $Δ $vdash $A $colon $B ])
  | _ => throw ()

end Kinding

judgement_syntax "lc_" T : TypeVarLC (tex := s!"\\lottkw\{lc}\\lottsym\{(}{T}\\lottsym\{)}")

termonly
@[simp]
def TypeVarLC (T: «Type») := T.TypeVarLocallyClosed 0

judgement_syntax "body " T : TypeVarBody

termonly
@[simp]
def TypeVarBody (T: «Type») := T.TypeVarLocallyClosed 1

judgement_syntax Δ " ⊢ " A " ≡ " B : TypeEquivalence

judgement TypeEquivalence where

───────── refl
Δ ⊢ A ≡ A

lc_ A
────────────────────── eta
Δ ⊢ λ a : K. A a$0 ≡ A

Δ ⊢ B: K
─────────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡ A^^B/a

notex lc_ A   -- NOTE this is for preserve_lc when n = 0
───────────────────────────────────────────────────────────────── listAppList
Δ ⊢ A ⟦{ </ B@i // i in [:n] notex /> }⟧ ≡ { </ A B@i // i in [:n] notex /> }

Δ ⊢ A: L K
────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ ≡ A

notex lc_ A₀
Δ ⊢ A₁ : K₁ ↦ K₂
───────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦A₁ ⟦B⟧⟧ ≡ (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧

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

</ Δ ⊢ A@i ≡ B@i // i in [:n] notex />
─────────────────────────────────────────────────────────────────── list
Δ ⊢ {</ A@i // i in [:n] notex />} ≡ {</ B@i // i in [:n] notex />}

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

Δ ⊢ A ≡ B
───────── symm
Δ ⊢ B ≡ A

Δ ⊢ A ≡ B
Δ ⊢ B ≡ C
───────── trans
Δ ⊢ A ≡ C

judgement_syntax Δ " ⊢ " A " ≢ " B : TypeInequivalence

judgement TypeInequivalence := fun Δ A B => ¬[[Δ ⊢ A ≡ B]]

@[app_unexpander TypeEquivalence]
def TypeEquivalence.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

judgement_syntax Δ " ⊢ " A " ≡ᵢ " B : TypeEquivalenceI

judgement TypeEquivalenceI where

────────── refl
Δ ⊢ A ≡ᵢ A

lc_ A
─────────────────────── eta
Δ ⊢ λ a : K. A a$0 ≡ᵢ A

Δ ⊢ B: K
─────────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡ᵢ A^^B/a

notex lc_ A   -- NOTE this is for preserve_lc when n = 0
───────────────────────────────────────────────────────────────── listAppList
Δ ⊢ A ⟦{ </ B@i // i in [:n] notex /> }⟧ ≡ᵢ { </ A B@i // i in [:n] notex /> }

Δ ⊢ A: L K
────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ ≡ᵢ A

notex lc_ A₀
Δ ⊢ A₁ : K₁ ↦ K₂
────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦A₁ ⟦B⟧⟧ ≡ᵢ (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧

∀ a ∉ I, Δ, a : K ⊢ A^a ≡ᵢ B^a
───────────────────────────── lam (I : List TypeVarId)
Δ ⊢ λ a : K. A ≡ᵢ λ a : K. B

Δ ⊢ A₁ ≡ᵢ A₂
Δ ⊢ B₁ ≡ᵢ B₂
───────────────── app
Δ ⊢ A₁ B₁ ≡ᵢ A₂ B₂

∀ a ∉ I, Δ, a : K ⊢ A^a ≡ᵢ B^a
───────────────────────────── scheme (I : List TypeVarId)
Δ ⊢ ∀ a : K. A ≡ᵢ ∀ a : K. B

Δ ⊢ A₁ ≡ᵢ A₂
Δ ⊢ B₁ ≡ᵢ B₂
───────────────────── arr
Δ ⊢ A₁ → B₁ ≡ᵢ A₂ → B₂

</ Δ ⊢ A@i ≡ᵢ B@i // i in [:n] notex />
─────────────────────────────────────────────────────── list
Δ ⊢ {</ A@i // i in [:n] notex />} ≡ᵢ {</ B@i // i in [:n] notex />}

Δ ⊢ A₁ ≡ᵢ A₂
Δ ⊢ B₁ ≡ᵢ B₂
───────────────────── listApp
Δ ⊢ A₁ ⟦B₁⟧ ≡ᵢ A₂ ⟦B₂⟧

Δ ⊢ A ≡ᵢ B
───────────── prod
Δ ⊢ ⊗ A ≡ᵢ ⊗ B

Δ ⊢ A ≡ᵢ B
───────────── sum
Δ ⊢ ⊕ A ≡ᵢ ⊕ B

termonly
@[app_unexpander TypeEquivalenceI]
def TypeEquivalenceI.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡ᵢ") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

judgement_syntax Δ " ⊢ " A " ≡ₛ " B : TypeEquivalenceS

judgement TypeEquivalenceS where

Δ ⊢ A ≡ᵢ B
────────── base
Δ ⊢ A ≡ₛ B

Δ ⊢ A ≡ᵢ B
────────── symm
Δ ⊢ B ≡ₛ A

Δ ⊢ A ≡ₛ B
Δ ⊢ B ≡ₛ C
────────── trans
Δ ⊢ A ≡ₛ C

termonly
@[app_unexpander TypeEquivalenceS]
def TypeEquivalenceS.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡ₛ") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

end TabularTypeInterpreter.«F⊗⊕ω»
