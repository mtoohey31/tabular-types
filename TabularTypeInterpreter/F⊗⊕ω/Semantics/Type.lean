import Lott.Data.Range
import Lott.Elab.JudgementComprehension
import Lott.Elab.UniversalJudgement
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment.Basic
import TabularTypeInterpreter.RuleSets

namespace TabularTypeInterpreter.«F⊗⊕ω»

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

</ Δ ⊢ A@i : K // i in [:n] />
────────────────────────────────── list
Δ ⊢ {</ A@i // i in [:n] />} : L K

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

judgement_syntax "lc_" T : TypeVarLC

@[simp]
def TypeVarLC (T: «Type») := T.TypeVarLocallyClosed 0

judgement_syntax "body" T : TypeVarBody

@[simp]
def TypeVarBody (T: «Type») := T.TypeVarLocallyClosed 1

judgement_syntax Δ " ⊢ " A " ≡ " B : TypeEquivalence

judgement TypeEquivalence :=

───────── refl
Δ ⊢ A ≡ A

Δ ⊢ B: K
───────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡ A^^B

lc_ A   -- NOTE this is for preserve_lc when n = 0
───────────────────────────────────────────────────────────────── lamListApp
Δ ⊢ A ⟦{ </ B@i // i in [:n] /> }⟧ ≡ { </ A B@i // i in [:n] /> }

lc_ A -- FIXME replace with kinding (kinding implies lc)
────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ ≡ A

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

</ Δ ⊢ A@i ≡ B@i // i in [:n] />
─────────────────────────────────────────────────────── list
Δ ⊢ {</ A@i // i in [:n] />} ≡ {</ B@i // i in [:n] />}

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────────── listApp
Δ ⊢ A₁ ⟦B₁⟧ ≡ A₂ ⟦B₂⟧

lc_ A₀
───────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦(λ a : K. A₁) ⟦B⟧⟧ ≡ (λ a : K. A₀ A₁) ⟦B⟧

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

@[app_unexpander TypeEquivalence]
def TypeEquivalence.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

judgement_syntax Δ " ⊢ " A " ≡ᵢ " B : TypeEquivalenceI

judgement TypeEquivalenceI :=

────────── refl
Δ ⊢ A ≡ᵢ A

Δ ⊢ B: K
───────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡ᵢ A^^B

lc_ A   -- NOTE this is for preserve_lc when n = 0
───────────────────────────────────────────────────────────────── lamListApp
Δ ⊢ A ⟦{ </ B@i // i in [:n] /> }⟧ ≡ᵢ { </ A B@i // i in [:n] /> }

lc_ A -- FIXME replace with kinding (kinding implies lc)
────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ ≡ᵢ A

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

</ Δ ⊢ A@i ≡ᵢ B@i // i in [:n] />
─────────────────────────────────────────────────────── list
Δ ⊢ {</ A@i // i in [:n] />} ≡ᵢ {</ B@i // i in [:n] />}

Δ ⊢ A₁ ≡ᵢ A₂
Δ ⊢ B₁ ≡ᵢ B₂
───────────────────── listApp
Δ ⊢ A₁ ⟦B₁⟧ ≡ᵢ A₂ ⟦B₂⟧

lc_ A₀
───────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦(λ a : K. A₁) ⟦B⟧⟧ ≡ᵢ (λ a : K. A₀ A₁) ⟦B⟧

Δ ⊢ A ≡ᵢ B
───────────── prod
Δ ⊢ ⊗ A ≡ᵢ ⊗ B

Δ ⊢ A ≡ᵢ B
───────────── sum
Δ ⊢ ⊕ A ≡ᵢ ⊕ B

@[app_unexpander TypeEquivalenceI]
def TypeEquivalenceI.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡ᵢ") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

judgement_syntax Δ " ⊢ " A " ≡ₛ " B : TypeEquivalenceS

judgement TypeEquivalenceS :=

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

@[app_unexpander TypeEquivalenceS]
def TypeEquivalenceS.delab: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡ₛ") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

judgement_syntax Δ " ⊢ " A " ≡> " B : ParallelReduction

judgement ParallelReduction :=

───────── refl
Δ ⊢ A ≡> A

Δ ⊢ B : K
∀ a ∉ (I: List _), Δ, a : K ⊢ A^a ≡> A'^a
Δ ⊢ B ≡> B'
────────────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡> A'^^B'

Δ ⊢ A ≡> A'
</ Δ ⊢ B@i ≡> B'@i // i in [:n] />
lc_ A   -- NOTE this is for preserve_lc when n = 0
──────────────────────────────────────────────────────────────────────────────── lamListApp
Δ ⊢ A ⟦{ </ B@i // i in [:n] /> }⟧ ≡> { </ A' B'@i // i in [:n] /> }

Δ ⊢ A ≡> A'
──────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ ≡> A'

∀ a ∉ (I : List _), Δ, a : K ⊢ A^a ≡> B^a
─────────────────────────── lam
Δ ⊢ λ a : K. A ≡> λ a : K. B

Δ ⊢ A₁ ≡> A₂
Δ ⊢ B₁ ≡> B₂
───────────────── app
Δ ⊢ A₁ B₁ ≡> A₂ B₂

∀ a ∉ (I: List _), Δ, a : K ⊢ A^a ≡> B^a
─────────────────────────── scheme
Δ ⊢ ∀ a : K. A ≡> ∀ a : K. B

Δ ⊢ A₁ ≡> A₂
Δ ⊢ B₁ ≡> B₂
───────────────────── arr
Δ ⊢ A₁ → B₁ ≡> A₂ → B₂

</ Δ ⊢ A@i ≡> B@i // i in [:n] />
──────────────────────────────────────────────────────────────────────────────── list
Δ ⊢ { </ A@i // i in [:n] /> } ≡> { </ B@i // i in [:n] /> }

Δ ⊢ A₁ ≡> A₂
Δ ⊢ B₁ ≡> B₂
───────────────────── listApp
Δ ⊢ A₁ ⟦B₁⟧ ≡> A₂ ⟦B₂⟧

lc_ A₀
Δ ⊢ A₀ ≡> A₀'
∀ a ∉ (I: List _), Δ, a : K ⊢ A₁^a ≡> A₁'^a
Δ ⊢ B ≡> B'
───────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦(λ a : K. A₁) ⟦B⟧⟧ ≡> (λ a : K. A₀' A₁') ⟦B'⟧

Δ ⊢ A ≡> B
───────────── prod
Δ ⊢ ⊗ A ≡> ⊗ B

Δ ⊢ A ≡> B
───────────── sum
Δ ⊢ ⊕ A ≡> ⊕ B

@[app_unexpander ParallelReduction]
def ParallelReduction.delabPRed: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡>") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

judgement_syntax Δ " ⊢ " A " ≡>* " B : MultiParallelReduction

judgement MultiParallelReduction :=

───────── refl
Δ ⊢ A ≡>* A

Δ ⊢ A ≡> A'
Δ ⊢ A' ≡>* A''
────────────── step
Δ ⊢ A ≡>* A''

@[app_unexpander MultiParallelReduction]
def MultiParallelReduction.delabMPRed: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡>*") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

def ParallelReduction.Multi_of (red: [[ Δ ⊢ A ≡> B ]]): [[ Δ ⊢ A ≡>* B ]] := .step red .refl

judgement_syntax Δ " ⊢ " A " <≡>* " B : EqParallelReduction

judgement EqParallelReduction :=

──────────── refl
Δ ⊢ A <≡>* A

Δ ⊢ A ≡> B
──────────── step
Δ ⊢ A <≡>* B

Δ ⊢ B <≡>* A
──────────── sym
Δ ⊢ A <≡>* B

Δ ⊢ A <≡>* A'
Δ ⊢ A' <≡>* A''
─────────────── trans
Δ ⊢ A <≡>* A''

@[app_unexpander EqParallelReduction]
def EqParallelReduction.delabMPRed: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "<≡>*") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

def ParallelReduction.Equiv_of (red: [[ Δ ⊢ A ≡> B ]]): [[ Δ ⊢ A <≡>* B ]] := .step red

def MultiParallelReduction.Equiv_of (red: [[ Δ ⊢ A ≡>* B ]]): [[ Δ ⊢ A <≡>* B ]] := by
  induction red with
  | refl => exact .refl
  | step base _ ih => exact base.Equiv_of |>.trans ih

attribute [aesop unsafe simp constructors (rule_sets := [pred])] ParallelReduction MultiParallelReduction EqParallelReduction

end TabularTypeInterpreter.«F⊗⊕ω»
