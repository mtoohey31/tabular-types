import Lott
import Lott.Data.List
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
  | "λ " a " : " K ". " A  : lam (bind a in A)
  | A B                    : app
  | "∀ " a " : " K ". " A  : forall' (bind a in A)
  | A " → " B              : arr
  | "{" sepBy(A, ", ") "}" : list
  | A " ⟦" B "⟧"           : listApp
  | "⊗ " A                 : prod
  | "⊕ " A                 : sum
  | "(" A ")"              : paren (desugar := return A)

metavar TermVar, x

nonterminal Term, E, F :=
  | x                                : var
  | "λ " x " : " A ". " E            : lam (bind x in E)
  | E F                              : app
  | "Λ " a " : " K ". " E            : typeLam (bind a in E)
  | E " [" A "]"                     : typeApp
  | "(" sepBy(E, ", ") ")"           : prodIntro
  | "π " n E                         : prodElim
  | "ι " n E                         : sumIntro
  | "case " E "{" sepBy(F, ", ") "}" : sumElim
  | "⦅" E "⦆"                        : paren (desugar := return E)

nosubst
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

Δ ⊢ B : K
────────────────────────────── lamAppL
Δ ⊢ (λ a : K. A) B ≡ A [B / a]

Δ ⊢ B : K
────────────────────────────── lamAppR
Δ ⊢ A [B / a] ≡ (λ a : K. A) B

</ Δ ⊢ B@i : K // i ∈ [:n] />
──────────────────────────────────────────────────────────────────────────────── lamListAppL
Δ ⊢ (λ a : K. A) ⟦{ </ B@i // i ∈ [:n] /> }⟧ ≡ { </ A [B@i / a] // i ∈ [:n] /> }

</ Δ ⊢ B@i : K // i ∈ [:n] />
──────────────────────────────────────────────────────────────────────────────── lamListAppR
Δ ⊢ { </ A [B@i / a] // i ∈ [:n] /> } ≡ (λ a : K. A) ⟦{ </ B@i // i ∈ [:n] /> }⟧

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

private
def TypeEquivalence.symm : [[Δ ⊢ A ≡ B]] → [[Δ ⊢ B ≡ A]]
  | .refl => .refl
  | .lamAppL h => .lamAppR h
  | .lamAppR h => .lamAppL h
  | .lamListAppL h => .lamListAppR h
  | .lamListAppR h => .lamListAppL h
  | .lam h => .lam h.symm
  | .app h₁ h₂ => .app h₁.symm h₂.symm
  | .scheme h => .scheme h.symm
  | .arr h₁ h₂ => .arr h₁.symm h₂.symm
  | .list h => .list (fun i mem => (h i mem).symm)
  | .listApp h₁ h₂ => .listApp h₁.symm h₂.symm
  | .prod h => .prod h.symm
  | .sum h => .sum h.symm

judgement_syntax Δ " ⊢ " A " ≢ " B : TypeInequivalence

def TypeInequivalence Δ A B := ¬[[Δ ⊢ A ≡ B]]

namespace TypeInequivalence

private
def symm : [[Δ ⊢ A ≢ B]] → [[Δ ⊢ B ≢ A]] := (· ·.symm)

private
theorem arr_forall : [[Δ ⊢ A → B ≢ ∀ a : K. A']] := fun equ => by
  generalize A₁eq : [[(A → B)]] = A₁, A₂eq : [[∀ a : K. A']] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem arr_prod : [[Δ ⊢ A → B ≢ ⊗ A']] := fun equ => by
  generalize A₁eq : [[(A → B)]] = A₁, A₂eq : [[⊗ A']] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem arr_sum : [[Δ ⊢ A → B ≢ ⊕ A']] := fun equ => by
  generalize A₁eq : [[(A → B)]] = A₁, A₂eq : [[⊕ A']] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem forall_prod : [[Δ ⊢ ∀ a : K. A ≢ ⊗ B]] := fun equ => by
  generalize A₁eq : [[∀ a : K. A]] = A₁, A₂eq : [[⊗ B]] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem forall_sum : [[Δ ⊢ ∀ a : K. A ≢ ⊕ B]] := fun equ => by
  generalize A₁eq : [[∀ a : K. A]] = A₁, A₂eq : [[⊕ B]] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

private
theorem prod_sum : [[Δ ⊢ ⊗ A ≢ ⊕ B]] := fun equ => by
  generalize A₁eq : [[⊗ A]] = A₁, A₂eq : [[⊕ B]] = A₂ at equ
  induction equ <;> ((try contradiction); try cases A₁eq; contradiction)

end TypeInequivalence

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
─────────────────────────── typeLam
Δ ⊢ Λ a : K. E : ∀ a : K. A

Δ ⊢ E : ∀ a : K. A
Δ ⊢ B : K
───────────────────── typeApp
Δ ⊢ E [B] : A [B / a]

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
⦅λ x : A. E⦆ V -> E [V / x]

E -> E'
─────────────── typeApp
E [A] -> E' [A]

───────────────────────────── typeLamApp
⦅Λ a : K. E⦆ [A] -> E [A / a]

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────── prodIntro
( </ V@i // i ∈ [:n] />, E, </ F@j // j ∈ [:m] /> ) -> ( </ V@i // i ∈ [:n] />, E', </ F@j // j ∈ [:m] /> )

E -> E'
───────────────────────────────────── prodElim
π n E -> π n E'

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

private
theorem Value.eq_lam_of_ty_arr (VtyAarrB : [[ε ⊢ V : A → B]])
  : ∃ x A' E, V.1 = [[λ x : A'. E]] := sorry

private
theorem Value.eq_typeApp_of_ty_forall (Vty : [[ε ⊢ V : ∀ a : K. A]])
  : ∃ a K E, V.1 = [[Λ a : K. E]] := sorry

private
theorem Value.eq_prodIntro_of_ty_prod (Vty : [[ε ⊢ V : ⊗ { </ A@i // i ∈ [0:n] /> }]])
  : ∃ V' : Nat → Value, V.1 = [[( </ V'@i // i ∈ [0:n] /> )]] := sorry

private
theorem Value.eq_sumIntro_of_ty_sum (Vty : [[ε ⊢ V : ⊕ { </ A@i // i ∈ [0:n'] /> }]])
  : ∃ n ∈ [0:n'], ∃ E, V.1 = [[ι n E]] := sorry

open Std

private
theorem _root_.Membership.mem.inc {r : Range} (h : i ∈ r) : i ∈ { r with stop := r.stop + 1 } :=
  ⟨h.lower, Nat.lt_add_right _ h.upper⟩

private
instance : Inhabited Value where
  default := ⟨.prodIntro [], .prodIntro fun _ mem => by cases mem⟩

private
theorem progress.fold {E : Nat → Term} (EtyA : ∀ i ∈ [0:n], [[ε ⊢ E@i : A@i]])
  (h : ∀ i ∈ [0:n], (∃ E', [[E@i -> E']]) ∨ (E i).IsValue) :
  (∃ i ∈ [0:n], (∀ j ∈ [0:i], (E j).IsValue) ∧ ∃ E', [[E@i -> E']]) ∨
    (∀ i ∈ [0:n], (E i).IsValue) := by
  induction n
  · case zero =>
    right
    intro _ ⟨_, lt_zero⟩
    contradiction
  · case succ j ih' => match ih' (fun j mem => EtyA j mem.inc) (fun j mem => h j mem.inc) with
    | .inl ⟨i, mem, ⟨E'', toE''⟩⟩ => exact .inl ⟨i, mem.inc, ⟨E'', toE''⟩⟩
    | .inr IsValue =>
      have jmem : j ∈ [0:j + 1] := ⟨Nat.zero_le _, Nat.lt_succ_self _⟩
      match h j jmem with
      | .inl ⟨E'', toE''⟩ => exact .inl ⟨j, jmem, ⟨IsValue, ⟨E'', toE''⟩⟩⟩
      | .inr jIsValue =>
        right
        intro i mem
        by_cases i = j
        · case pos h =>
          rw [h]
          exact jIsValue
        · case neg h =>
          exact IsValue i ⟨Nat.zero_le _, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ mem.upper) h⟩

private
theorem progress.sandwich {f : Nat → α} (h : i < n) : (List.map (fun j => [f j]) [0:n]).join =
  (List.map (fun j => [f j]) [0:i]).join ++
    f i :: (List.map (fun j => [f (j + (i + 1))]) [(i + 1) - (i + 1):n - (i + 1)]).join := by
  simp only [List.map_singleton_join]
  congr
  rw [← List.singleton_append, Range.map_shift (Nat.le_refl _)]
  have : [f i] = List.map (fun j => f j) [i:i + 1] := by
    rw [Range.toList, if_neg Nat.one_ne_zero, if_pos (Nat.lt_succ_self _), Range.toList,
        if_neg Nat.one_ne_zero, if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map, List.map]
  rw [this]
  rw [Range.map_append (Nat.le_succ _) (Nat.succ_le_of_lt h),
      Range.map_append (Nat.zero_le _) (Nat.le_of_lt h)]

theorem progress (EtyA : [[ε ⊢ E : A]]) : (∃ E', [[E -> E']]) ∨ E.IsValue := by
  generalize Δeq : Environment.empty = Δ at EtyA
  induction EtyA <;> cases Δeq
  · case var xinε => cases xinε
  · case lam => exact .inr .lam
  · case app E' A' B F E'tyA'arrB _ ih₁ ih₂ => match ih₁ rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .appL E'toE''
    | .inr E'IsValue => match ih₂ rfl with
      | .inl ⟨F', FtoF'⟩ => exact .inl <| .intro _ <| .appR (V := ⟨E', E'IsValue⟩) FtoF'
      | .inr FIsValue =>
        let VE' : Value := ⟨E', E'IsValue⟩
        have : E' = VE'.1 := rfl
        have ⟨_, _, _, VE'eq⟩ := VE'.eq_lam_of_ty_arr E'tyA'arrB
        rw [this, VE'eq]
        exact .inl <| .intro _ <| .lamApp (V := ⟨F, FIsValue⟩)
  · case typeLam => exact .inr .typeLam
  · case typeApp E' a K _ A' E'ty _ ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .typeApp E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, _, _, Veq⟩ := V.eq_typeApp_of_ty_forall E'ty
      rw [this, Veq]
      exact .inl <| .intro _ <| .typeLamApp
  · case prodIntro n E' A E'ty ih => match progress.fold E'ty (fun i mem => ih i mem rfl) with
    | .inl ⟨i, ⟨_, iltn⟩, IsValue, E'', toE''⟩ =>
      let V j : Value := if h' : j < i then ⟨E' j, IsValue j ⟨Nat.zero_le _, h'⟩⟩ else default
      dsimp only [Coe.coe]
      rw [progress.sandwich iltn, Range.map_eq_of_eq_of_mem (fun j jmem => by
          show [E' j] = [(V j).val]
          dsimp only [V]
          rw [dif_pos jmem.upper]
      ), Nat.sub_self]
      exact .inl <| .intro _ <| .prodIntro toE''
    | .inr IsValue =>
      exact .inr <| .prodIntro fun E Emem => by
        rw [List.map_singleton_join] at Emem
        have ⟨i, imem, Eeq⟩ := Range.mem_of_mem_map Emem
        rw [Eeq]
        exact IsValue i imem
  · case prodElim E' n _ i mem E'ty ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .prodElim E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, Veq⟩ := V.eq_prodIntro_of_ty_prod E'ty
      rw [this, Veq]
      exact .inl <| .intro _ <| .prodElimIntro mem
  · case sumIntro ih => match ih rfl with
    | .inl ⟨E', toE'⟩ => exact .inl <| .intro _ <| .sumIntro toE'
    | .inr E'IsValue => exact .inr <| .sumIntro E'IsValue
  · case sumElim E' n As F _ E'ty Fty ih₁ ih₂ => match ih₁ rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .sumElimL E'toE''
    | .inr E'IsValue =>
      let VE' : Value := ⟨E', E'IsValue⟩
      have ⟨_, mem, _⟩ := VE'.eq_sumIntro_of_ty_sum E'ty
      match progress.fold Fty (fun i mem => ih₂ i mem rfl) with
      | .inl ⟨j, ⟨_, jltn⟩, IsValue, F', toF'⟩ =>
        let VF k : Value := if h' : k < j then ⟨F k, IsValue k ⟨Nat.zero_le _, h'⟩⟩ else default
        dsimp only [Coe.coe]
        rw [progress.sandwich jltn, Range.map_eq_of_eq_of_mem (fun j jmem => by
          show [F j] = [(VF j).val]
          dsimp only [VF]
          rw [dif_pos jmem.upper]
        ), Nat.sub_self]
        exact .inl <| .intro _ <| .sumElimR (V := VE') toF'
      | .inr FIsValue =>
        let VF j : Value := if h : j < n then ⟨F j, FIsValue j ⟨Nat.zero_le _, h⟩⟩ else default
        rw [List.map_singleton_join, Range.map_eq_of_eq_of_mem' (fun i mem => by
          show F i = (VF i).val
          dsimp only [VF]
          rw [dif_pos mem.upper]
        ), ← List.map_singleton_join]
        exact .inl <| .intro _ <| .sumElimIntro (V := VE') mem
  · case equiv ih => exact ih rfl

theorem preservation : [[ε ⊢ E : A]] → [[E -> E']] → [[ε ⊢ E' : A]] := sorry

end TabularTypeInterpreter.«F⊗⊕ω»
