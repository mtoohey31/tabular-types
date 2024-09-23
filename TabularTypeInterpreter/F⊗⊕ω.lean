import Lott
import Lott.Data.Range
import Lott.DSL.Elab.JudgementComprehension
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
  -- TODO: Replace this with a custom elaboration to a substitution function.
  | A " [" a " ↦ " B "]"   : subst

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
  | "⦅" E "⦆"                        : paren (desugar := return E)
  -- TODO: Replace these with custom elaborations to a substitution functions.
  | E " [" a " ↦ " B "]"             : tySubst
  | E " [" x " ↦ " F "]"             : tmSubst

nonterminal Environment, Δ :=
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

</ Δ ⊢ A@i : K // i ∈ [:n] />
─────────────────────────────────── list
Δ ⊢ { </ A@i // i ∈ [:n] /> } : L K

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

judgement_syntax x " ≠ " x' : TermVarNe

def TermVarNe := Ne (α := TermVar)

judgement_syntax x " : " A " ∈ " Δ : TermVarInEnvironment

judgement TermVarInEnvironment :=

──────────────── head
x : A ∈ Δ, x : A

x : A ∈ Δ
x ≠ x'
───────────────── termVarExt
x : A ∈ Δ, x' : B

x : A ∈ Δ
──────────────── typeVarExt
x : A ∈ Δ, a : K

judgement_syntax Δ " ⊢ " A " ≡ " B : TypeEquivalence

judgement TypeEquivalence :=

───────── refl
Δ ⊢ A ≡ A

Δ ⊢ A ≡ B
───────── symm
Δ ⊢ B ≡ A

Δ ⊢ B : K
────────────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡ A [a ↦ B]

</ Δ ⊢ B@i : K // i ∈ [:n] />
──────────────────────────────────────────────────────────────────────────────── lamListApp
Δ ⊢ (λ a : K. A) ⟦{ </ B@i // i ∈ [:n] /> }⟧ ≡ { </ A [a ↦ B@i] // i ∈ [:n] /> }

Δ, a : K ⊢ A ≡ B
─────────────────────────── lam
Δ ⊢ λ a : K. A ≡ λ a : K. B

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────── app
Δ ⊢ A₁ B₁ ≡ A₂ B₂

Δ, a : K ⊢ A ≡ B
─────────────────────────── scheme
Δ ⊢ ∀ a : K. A ≡ ∀ a : K. B

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────────── arr
Δ ⊢ A₁ → B₁ ≡ A₂ → B₂

</ Δ ⊢ A@i ≡ B@i // i ∈ [:n] />
───────────────────────────────────────────────────────── list
Δ ⊢ { </ A@i // i ∈ [:n] /> } ≡ { </ B@i // i ∈ [:n] /> }

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

───────────── never
Δ ⊢ ⊕ { } ≡ A

judgement_syntax n " ∈ " "[" n_start ":" n_stop "]" : NatInRange

def NatInRange (n start stop : Nat) := n ∈ [start:stop]

judgement_syntax Δ " ⊢ " E " : " A : Typing

judgement Typing :=

x : A ∈ Δ
───────── var
Δ ⊢ x : A

Δ, x : A ⊢ E : B
────────────────────── lam
Δ ⊢ λ x : A. E : A → B

Δ ⊢ E : A → B
Δ ⊢ F : A
─────────────── app
Δ ⊢ E F : A → B

Δ, a : K ⊢ E : A
─────────────────────────── typeAbs
Δ ⊢ Λ a : K. E : ∀ a : K. A

Δ ⊢ E : ∀ a : K. A
Δ ⊢ B : K
───────────────────── typeApp
Δ ⊢ E [B] : A [a ↦ B]

</ Δ ⊢ E@i : A@i // i ∈ [:n] />
─────────────────────────────────────────────────────────── prodIntro
Δ ⊢ ( </ E@i // i ∈ [:n] /> ) : ⊗ { </ A@i // i ∈ [:n] /> }

Δ ⊢ E : ⊗ { </ A@i // i ∈ [:n'] /> }
n ∈ [0:n']
──────────────────────────────────── prodElim
Δ ⊢ π n E : A@n

n ∈ [0:n']
Δ ⊢ E : A@n
──────────────────────────────────────── sumIntro
Δ ⊢ ι n E : ⊕ { </ A@i // i ∈ [:n'] /> }

Δ ⊢ E : ⊕ { </ A@i // i ∈ [:n] /> }
</ Δ ⊢ F@i : A@i → B // i ∈ [:n] />
──────────────────────────────────────── sumElim
Δ ⊢ case E { </ F@i // i ∈ [:n] /> } : B

Δ ⊢ E : A
Δ ⊢ A ≡ B
───────── equiv
Δ ⊢ E : B

nonterminal (parent := Term) Value, V :=
  | "λ " x " : " A ". " E  : lam
  | "Λ " a " : " K ". " E  : typeLam
  | "(" sepBy(V, ", ") ")" : prodIntro
  | "ι " n V               : sumIntro

judgement_syntax E " -> " F : OperationalSemantics

judgement OperationalSemantics :=

E -> E'
─────────── appL
E F -> E' F

F -> F'
─────────── appR
V F -> V F'

─────────────────────────── lamApp
⦅λ x : A. E⦆ V -> E [x ↦ V]

E -> E'
─────────────── typeApp
E [A] -> E' [A]

───────────────────────────── typeAbsApp
⦅Λ a : K. E⦆ [A] -> E [a ↦ A]

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────── prodIntro
( </ V@i // i ∈ [:n] />, E, </ F@j // j ∈ [:m] /> ) -> ( </ V@i // i ∈ [:n] />, E', </ F@j // j ∈ [:m] /> )

n ∈ [0:n']
───────────────────────────────────── prodElimIntro
π n ( </ V@i // i ∈ [:n'] /> ) -> V@n

E -> E'
─────────────── sumIntro
ι n E -> ι n E'

E -> E'
───────────────────────────────────────────────────────────────────── sumElimL
case E { </ F@i // i ∈ [:n] /> } -> case E' { </ F@i // i ∈ [:n] /> }

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sumElimR
case V { </ V'@i // i ∈ [:n] />, E, </ F@j // j ∈ [:m] /> } -> case V { </ V'@i // i ∈ [:n] />, E', </ F@j // j ∈ [:m] /> }

n ∈ [0:n']
──────────────────────────────────────────── sumElimIntro
case V { </ V'@i // i ∈ [:n'] /> } -> V'@n V

theorem progress : [[ε ⊢ E : A]] → [[E -> E']] ∨ E.isValue := sorry

theorem preservation : [[ε ⊢ E : A]] → [[E -> E']] → [[ε ⊢ E' : A]] := sorry

end TabularTypeInterpreter.«F⊗⊕ω»
