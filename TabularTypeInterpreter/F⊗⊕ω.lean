import Lott
import Lott.DSL.Elab.Nat

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal Kind, K :=
  | "*"         : star
  | K₁ " ↦ " K₂ : arr
  | "L " K      : list

metavar TypeVar, a

nonterminal Type', A, B :=
  | a                      : var
  | "λ " a " : " K ". " A  : lam
  | A B                    : app
  | "∀ " a " : " K ". " A  : forall'
  | A " → " B              : arr
  | "{" sepBy(A, ", ") "}" : list
  | A " ⟦" B "⟧"           : listApp
  | "⊗ " A                 : prod
  | "⊕ " A                 : sum
  | "(" A ")"              : paren (desugar := return A)

metavar TermVar, x

nonterminal Term, E, F :=
  | x                                : var
  | "λ " x " : " A ". " E            : lam
  | E F                              : app
  | "Λ " a " : " K ". " E            : typeLam
  | E " [" A "]"                     : typeApp
  | "(" sepBy(E, ", ") ")"           : prodIntro
  | "π " n E                         : prodElim
  | "ι " n E                         : sumIntro
  | "case " E "{" sepBy(F, ", ") "}" : sumElim

nonterminal Environemnt, Δ :=
  | "ε"              : empty
  | Δ ", " x " : " A : termExt
  | Δ ", " a " : " K : typeExt

judgement_syntax a " ≠ " a' : TypeVarNe

def TypeVarNe := Ne (α := TypeVar)

judgement_syntax a " : " K " ∈ " Δ : TypeVarInEnvironment

judgement TypeVarInEnvironment :=

──────────────── head
a : K ∈ Δ, a : K

a : K ∈ Δ
──────────────── termVarExt
a : K ∈ Δ, x : A

a : K ∈ Δ
a ≠ a'
────────────────── typeVarExt
a : K ∈ Δ, a' : K'

judgement_syntax Δ " ⊢ " A " : " K : Kinding

judgement Kinding :=

a : K ∈ Δ
───────── var
Δ ⊢ a : K

Δ, a : K₁ ⊢ A : K₂
───────────────────────── lam
Δ ⊢ λ a : K₁. A : K₁ ↦ K₂

Δ ⊢ A : K₁ ↦ K₂
Δ ⊢ B : K₁
─────────────── app
Δ ⊢ A B : K₂

Δ, a : K₁ ⊢ A : K₂
──────────────────── scheme
Δ ⊢ ∀ a : K₁. A : K₂

Δ ⊢ A : *
Δ ⊢ B : *
───────────── arr
Δ ⊢ A → B : *

</ Δ ⊢ As@i : K // i ∈ [0:As.length]ᶠ />
────────────────────────────────────────────── list
Δ ⊢ { </ As@i // i ∈ [0:As.length]ᶠ /> } : L K

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

end TabularTypeInterpreter.«F⊗⊕ω»
