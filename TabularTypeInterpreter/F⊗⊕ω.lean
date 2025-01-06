import Lott
import Lott.Data.List
import Lott.Data.Range
import Lott.DSL.Elab.JudgementComprehension
import Lott.DSL.Elab.UniversalJudgement
import Lott.DSL.Elab.Nat

namespace TabularTypeInterpreter.«F⊗⊕ω»

nonterminal Kind, K :=
  | "*"         : star
  | K₁ " ↦ " K₂ : arr
  | "L " K      : list
  | "(" K ")"   : paren (desugar := return K)

locally_nameless
metavar TypeVar, a

nonterminal «Type», A, B :=
  | a                      : var
  | "λ " a " : " K ". " A  : lam (bind a in A)
  | A B                    : app
  | "∀ " a " : " K ". " A  : «forall» (bind a in A)
  | A " → " B              : arr
  | "{" sepBy(A, ", ") "}" : list
  | A " ⟦" B "⟧"           : listApp
  | "⊗ " A                 : prod
  | "⊕ " A                 : sum
  | "(" A ")"              : paren (desugar := return A)

namespace «Type»

def fv : «Type» → List TypeVarId
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

@[simp]
theorem TypeVar_open_sizeOf (A : «Type») : sizeOf (A.TypeVar_open a n) = sizeOf A := by
  match A with
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h' =>
      dsimp only [sizeOf]
      rw [← h', _sizeOf_1, _sizeOf_1]
      dsimp only [sizeOf]
      rw [default.sizeOf, default.sizeOf]
    · case isFalse => rfl
  | var (.free _) =>
    rw [TypeVar_open]
    split <;> rfl
  | lam _ A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
  | app A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _),
        rev (B.TypeVar_open _ _), rev A', rev B, A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | «forall» _ A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
  | arr A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _),
        rev (B.TypeVar_open _ _), rev A', rev B, A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | list A's =>
    match A's with
    | [] =>
      rw [TypeVar_open]
      show sizeOf (list []) = _
      dsimp only [sizeOf]
    | A' :: A's' =>
      rw [TypeVar_open]
      show sizeOf (list (_ :: _)) = _
      dsimp only [sizeOf]
      rw [_sizeOf_1, _sizeOf_1]
      simp only
      rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_2, ← _sizeOf_2, rev (A'.TypeVar_open _ _), rev A',
          A'.TypeVar_open_sizeOf]
      have h := (list A's').TypeVar_open_sizeOf (a := a) (n := n)
      dsimp only [sizeOf] at h
      rw [TypeVar_open, _sizeOf_1, _sizeOf_1] at h
      simp only at h
      rw [← _sizeOf_2, ← _sizeOf_2, Nat.add_comm, Nat.add_comm (m := _sizeOf_2 A's')] at h
      rw [Nat.add_one_inj.mp h]
  | listApp A' B =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _),
        rev (B.TypeVar_open _ _), rev A', rev B, A'.TypeVar_open_sizeOf, B.TypeVar_open_sizeOf]
  | prod A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
  | sum A' =>
    dsimp only [sizeOf]
    rw [TypeVar_open, _sizeOf_1, _sizeOf_1]
    simp only
    rw [← _sizeOf_1, ← _sizeOf_1, rev (A'.TypeVar_open _ _), rev A', A'.TypeVar_open_sizeOf]
where
  rev : ∀ a : «Type», a._sizeOf_1 = sizeOf a := fun _ => by dsimp only [sizeOf]

namespace TypeVarLocallyClosed

theorem weaken {A : «Type»} : A.TypeVarLocallyClosed m → A.TypeVarLocallyClosed (m + n)
  | var_free => var_free
  | var_bound h => var_bound <| Nat.lt_add_right _ h
  | lam A'lc => by
    have := A'lc.weaken (n := n)
    rw [Nat.add_assoc, Nat.add_comm (n := 1), ← Nat.add_assoc] at this
    exact this.lam
  | app A'lc Blc => app A'lc.weaken Blc.weaken
  | «forall» A'lc => by
    have := A'lc.weaken (n := n)
    rw [Nat.add_assoc, Nat.add_comm (n := 1), ← Nat.add_assoc] at this
    exact this.forall
  | arr A'lc Blc => arr A'lc.weaken Blc.weaken
  | list A'lc => list (A'lc · · |>.weaken)
  | listApp A'lc Blc => listApp A'lc.weaken Blc.weaken
  | prod A'lc => prod A'lc.weaken
  | sum A'lc => sum A'lc.weaken

theorem TypeVar_open_drop {A : «Type»} (h : m < n)
  (Aoplc : (A.TypeVar_open a m).TypeVarLocallyClosed n) : A.TypeVarLocallyClosed n := by
  match A with
  | .var _ =>
    rw [TypeVar_open] at Aoplc
    split at Aoplc
    · case isTrue h' =>
      rw [← h']
      exact var_bound h
    · case isFalse h' => exact Aoplc
  | .lam .. =>
    rw [TypeVar_open] at Aoplc
    let .lam A'oplc := Aoplc
    exact lam <| A'oplc.TypeVar_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .app A' B =>
    rw [TypeVar_open] at Aoplc
    let .app A'oplc Boplc := Aoplc
    exact app (A'oplc.TypeVar_open_drop h) (Boplc.TypeVar_open_drop h)
  | .forall .. =>
    rw [TypeVar_open] at Aoplc
    let .forall A'oplc := Aoplc
    exact «forall» <| A'oplc.TypeVar_open_drop <| Nat.add_lt_add_iff_right.mpr h
  | .arr .. =>
    rw [TypeVar_open] at Aoplc
    let .arr A'oplc Boplc := Aoplc
    exact arr (A'oplc.TypeVar_open_drop h) (Boplc.TypeVar_open_drop h)
  | .list A's =>
    rw [TypeVar_open] at Aoplc
    match h' : A's with
    | [] => exact .list fun _ => (nomatch ·)
    | A' :: A's' =>
      apply list
      intro A'' A''in
      let .list A'oplc := Aoplc
      match A''in with
      | .head _ => exact A'oplc (A''.TypeVar_open _ _) (.head _) |>.TypeVar_open_drop h
      | .tail _ A''inA's' =>
        have := list <| fun A''' A'''in => A'oplc A''' <| .tail _ A'''in
        rw [← TypeVar_open] at this
        let .list A's'lc := this.TypeVar_open_drop h
        exact A's'lc A'' A''inA's'
  | .listApp A' B =>
    rw [TypeVar_open] at Aoplc
    let .listApp A'oplc Boplc := Aoplc
    exact listApp (A'oplc.TypeVar_open_drop h) (Boplc.TypeVar_open_drop h)
  | .prod A' =>
    rw [TypeVar_open] at Aoplc
    let .prod A'oplc := Aoplc
    exact prod <| A'oplc.TypeVar_open_drop h
  | .sum A' =>
    rw [TypeVar_open] at Aoplc
    let .sum A'oplc := Aoplc
    exact sum <| A'oplc.TypeVar_open_drop h
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  · apply Nat.le_of_lt
    apply List.sizeOf_lt_of_mem
    have : A's = A' :: A's' := by assumption
    cases this
    exact A''in
  · have : A's = A' :: A's' := by assumption
    cases this
    simp_arith

theorem TypeVar_open_eq {A : «Type»} (Alc : A.TypeVarLocallyClosed n) : A.TypeVar_open a n = A := by
  match A with
  | var (.free _) => rw [TypeVar_open, if_neg (nomatch ·)]
  | var (.bound _) =>
    rw [TypeVar_open]
    split
    · case isTrue h =>
      cases h
      let .var_bound nltn := Alc
      nomatch Nat.ne_of_lt nltn
    · case isFalse => rfl
  | .lam .. => let .lam A'lc := Alc; rw [TypeVar_open, A'lc.TypeVar_open_eq]
  | .app .. =>
    let .app A'lc Blc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq, Blc.TypeVar_open_eq]
  | .forall .. =>
    let .forall A'lc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq]
  | .arr .. =>
    let .arr A'lc Blc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq, Blc.TypeVar_open_eq]
  | .list A's =>
    match h : A's with
    | [] => rw [TypeVar_open]; rfl
    | A' :: A's' =>
      let .list A'slc := Alc
      rw [TypeVar_open]
      apply (Type.list.injEq _ _).mpr
      show (_ :: _) = _
      apply (List.cons.injEq _ _ _ _).mpr
      constructor
      · exact A'slc A' (.head _) |>.TypeVar_open_eq
      · have := TypeVar_open_eq (A := .list A's') (a := a) (n := n) <| .list ?h
        rw [TypeVar_open] at this
        apply Type.list.inj this
        intro A'' A''in
        exact A'slc A'' <| .tail _ A''in
  | .listApp .. =>
    let .listApp A'lc Blc := Alc
    rw [TypeVar_open, A'lc.TypeVar_open_eq, Blc.TypeVar_open_eq]
  | .prod .. => let .prod A'lc := Alc; rw [TypeVar_open, A'lc.TypeVar_open_eq]
  | .sum .. => let .sum A'lc := Alc; rw [TypeVar_open, A'lc.TypeVar_open_eq]

end TypeVarLocallyClosed

end «Type»

locally_nameless
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

private
def Environment.appendExpr : Lean.Expr :=
  .const `TabularTypeInterpreter.«F⊗⊕ω».Environment.append []

private
def Environment.TypeVar_substExpr : Lean.Expr :=
  .const `TabularTypeInterpreter.«F⊗⊕ω».Environment.TypeVar_subst []

nosubst
nonterminal Environment, Δ :=
  | "ε"                  : empty
  | Δ ", " a " : " K     : typeExt (id a)
  | Δ ", " x " : " A     : termExt (id x)
  | "(" Δ ")"            : paren (desugar := return Δ)
  | Δ ", " Δ'            : append (elab := return Lean.mkApp2 Environment.appendExpr Δ Δ')
  | Δ " [" A " / " a "]" : subst (id a) (elab := return Lean.mkApp3 Environment.TypeVar_substExpr Δ a A)

namespace Environment

def append (Δ : Environment) : Environment → Environment
  | empty => Δ
  | typeExt Δ' a K => Δ.append Δ' |>.typeExt a K
  | termExt Δ' x A => Δ.append Δ' |>.termExt x A

theorem append_empty (Δ : Environment) : Δ.append empty = Δ := rfl

theorem empty_append (Δ : Environment) : append empty Δ = Δ := by
  match Δ with
  | empty => rfl
  | typeExt Δ' .. | termExt Δ' .. => rw [append, Δ'.empty_append]

def TypeVar_subst (Δ : Environment) (a : TypeVarId) (A : «Type») := match Δ with
  | empty => empty
  | typeExt Δ' a' K => Δ'.TypeVar_subst a A |>.typeExt a' K
  | termExt Δ' x A' => Δ'.TypeVar_subst a A |>.termExt x <| A'.TypeVar_subst a A

end Environment

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

def TypeVarNe := Ne (α := TypeVarId)

judgement_syntax a " : " K " ∈ " Δ : TypeVarInEnvironment (id a)

judgement TypeVarInEnvironment :=

──────────────── head
a : K ∈ Δ, a : K

a : K ∈ Δ
a ≠ a'
────────────────── typeVarExt
a : K ∈ Δ, a' : K'

a : K ∈ Δ
──────────────── termVarExt
a : K ∈ Δ, x : A

judgement_syntax Δ " ⊢ " A " : " K : Kinding

judgement Kinding :=

a : K ∈ Δ
───────── var
Δ ⊢ a : K

∀ a ∉ (I : List _), Δ, a : K₁ ⊢ A^a : K₂
──────────────────────────────────────── lam
Δ ⊢ λ a : K₁. A : K₁ ↦ K₂

Δ ⊢ A : K₁ ↦ K₂
Δ ⊢ B : K₁
─────────────── app
Δ ⊢ A B : K₂

∀ a ∉ (I : List _), Δ, a : K₁ ⊢ A^a : K₂
──────────────────────────────────────── scheme
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

namespace Kinding

theorem TypeVarLocallyClosed_of : [[Δ ⊢ A : K]] → A.TypeVarLocallyClosed 0 := fun Aki =>
  match A, Aki with
  | _, var .. => .var_free
  | .lam K A', .lam A'opki (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'opki a anin |>.TypeVarLocallyClosed_of
    exact .lam <| this.weaken.TypeVar_open_drop <| Nat.lt_succ_self _
  | .app A' B, .app A'opki Bopki =>
    .app A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .forall K A', .scheme A'opki (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'opki a anin |>.TypeVarLocallyClosed_of
    exact .forall <| this.weaken.TypeVar_open_drop <| Nat.lt_succ_self _
  | .arr A' B, .arr A'opki Bopki =>
    .arr A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .list A', Aki =>
    let .list A'opki (A := A'') := Aki
    .list fun A''' A'''in => by
      rw [List.map_singleton_flatten] at A'''in
      let ⟨i, mem, A'''eq⟩ := Std.Range.mem_of_mem_map A'''in
      cases A'''eq
      exact A'opki i mem |>.TypeVarLocallyClosed_of
  | .listApp A' B, .listApp A'opki Bopki =>
    .listApp A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .prod A', .prod A'opki => .prod A'opki.TypeVarLocallyClosed_of
  | .sum A', .sum A'opki => .sum A'opki.TypeVarLocallyClosed_of
termination_by sizeOf A
decreasing_by
  all_goals (simp; try simp_arith)
  rw [List.map_singleton_flatten]
  apply Nat.le_of_lt
  exact List.sizeOf_lt_of_mem A'''in

theorem Type_open_preservation {A : «Type»}
  (Aki : Kinding [[(Δ, a : K, Δ')]] (A.TypeVar_open a n) K') (aninftvA : ¬A.InFreeTypeVars a)
  (Bki : [[Δ ⊢ B : K]]) : Kinding [[(Δ, (Δ' [B / a]))]] (A.Type_open B n) K' := sorry

end Kinding

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

def TermVarNe := Ne (α := TermVarId)

judgement_syntax x " : " A " ∈ " Δ : TermVarInEnvironment (id x)

judgement TermVarInEnvironment :=

──────────────── head
x : A ∈ Δ, x : A

x : A ∈ Δ
──────────────── typeVarExt
x : A ∈ Δ, a : K

x : A ∈ Δ
x ≠ x'
───────────────── termVarExt
x : A ∈ Δ, x' : B

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
─────────────────────────────────────────────────────────────────────────── lamListAppL
Δ ⊢ (λ a : K. A) ⟦{ </ B@i // i ∈ [:n] /> }⟧ ≡ { </ A^^B@i // i ∈ [:n] /> }

</ Δ ⊢ B@i : K // i ∈ [:n] />
─────────────────────────────────────────────────────────────────────────── lamListAppR
Δ ⊢ { </ A^^B@i // i ∈ [:n] /> } ≡ (λ a : K. A) ⟦{ </ B@i // i ∈ [:n] /> }⟧

∀ a ∉ (I : List _), Δ, a : K ⊢ A^a ≡ B^a
──────────────────────────────────────── lam
Δ ⊢ λ a : K. A ≡ λ a : K. B

Δ ⊢ A₁ ≡ A₂
Δ ⊢ B₁ ≡ B₂
───────────────── app
Δ ⊢ A₁ B₁ ≡ A₂ B₂

∀ a ∉ (I : List _), Δ, a : K ⊢ A^a ≡ B^a
──────────────────────────────────────── scheme
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
  | .lam h => .lam fun a mem => (h a mem).symm
  | .app h₁ h₂ => .app h₁.symm h₂.symm
  | .scheme h => .scheme fun a mem => (h a mem).symm
  | .arr h₁ h₂ => .arr h₁.symm h₂.symm
  | .list h => .list fun i mem => (h i mem).symm
  | .listApp h₁ h₂ => .listApp h₁.symm h₂.symm
  | .prod h => .prod h.symm
  | .sum h => .sum h.symm

private
def TypeEquivalence.trans : [[Δ ⊢ A₀ ≡ A₁]] → [[Δ ⊢ A₁ ≡ A₂]] → [[Δ ⊢ A₀ ≡ A₂]] := sorry

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

judgement_syntax a " ∈ " "dom" "(" Δ ")" : TypeVarInEnvironmentDomain (id a)

judgement TypeVarInEnvironmentDomain :=

───────────────── head
a ∈ dom(Δ, a : K)

a ∈ dom(Δ)
a ≠ a'
────────────────── typeVarExt
a ∈ dom(Δ, a' : K)

a ∈ dom(Δ)
───────────────── termVarExt
a ∈ dom(Δ, x : A)

judgement_syntax a " ∉ " "dom" "(" Δ ")" : TypeVarNotInEnvironmentDomain (id a)

def TypeVarNotInEnvironmentDomain a Δ := ¬[[a ∈ dom(Δ)]]

judgement_syntax x " ∈ " "dom" "(" Δ ")" : TermVarInEnvironmentDomain (id x)

judgement TermVarInEnvironmentDomain :=

───────────────── head
x ∈ dom(Δ, x : A)

x ∈ dom(Δ)
───────────────── typeVarExt
x ∈ dom(Δ, a : K)

x ∈ dom(Δ)
x ≠ x'
────────────────── termVarExt
x ∈ dom(Δ, x' : A)

judgement_syntax x " ∉ " "dom" "(" Δ ")" : TermVarNotInEnvironmentDomain (id x)

def TermVarNotInEnvironmentDomain x Δ := ¬[[x ∈ dom(Δ)]]

judgement_syntax "⊢ " Δ : EnvironmentWellFormedness

judgement EnvironmentWellFormedness :=

─── empty
⊢ ε

⊢ Δ
a ∉ dom(Δ)
────────── typeVarExt
⊢ Δ, a : K

⊢ Δ
x ∉ dom(Δ)
Δ ⊢ A : *
────────── termVarExt
⊢ Δ, x : A

theorem Kinding.weakening : [[Δ ⊢ A : K]] → [[⊢ Δ', Δ, Δ'']] → [[Δ', Δ, Δ'' ⊢ A : K]] := sorry

judgement_syntax n " ∈ " "[" n_start ":" n_stop "]" : NatInRange

def NatInRange (n start stop : Nat) := n ∈ [start:stop]

judgement_syntax Δ " ⊢ " E " : " A : Typing

judgement Typing :=

⊢ Δ
x : A ∈ Δ
───────── var
Δ ⊢ x : A

∀ x ∉ (I : List _), Δ, x : A ⊢ E^a : B
────────────────────────────────────── lam
Δ ⊢ λ x : A. E : A → B

Δ ⊢ E : A → B
Δ ⊢ F : A
─────────────── app
Δ ⊢ E F : A → B

∀ a ∉ (I : List _), Δ, a : K ⊢ E^a : A^a
──────────────────────────────────────── typeLam
Δ ⊢ Λ a : K. E : ∀ a : K. A

Δ ⊢ E : ∀ a : K. A
Δ ⊢ B : K
────────────────── typeApp
Δ ⊢ E [B] : A^^B

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
  | "λ " x " : " A ". " E  : lam (bind x in E)
  | "Λ " a " : " K ". " E  : typeLam (bind a in E)
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

────────────────────── lamApp
⦅λ x : A. E⦆ V -> E^^V

E -> E'
─────────────── typeApp
E [A] -> E' [A]

──────────────────────── typeLamApp
⦅Λ a : K. E⦆ [A] -> E^^A

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
────────────────────────────────────────────────────── sumElimIntro
case ι n V { </ V'@i // i ∈ [:n'] /> } -> V'@n ⦅ι n V⦆

private
theorem Value.eq_lam_of_ty_arr (VtyAarrB : [[ε ⊢ V : A → B]])
  : ∃ A' E, V.1 = [[λ x : A'. E]] := sorry

private
theorem Value.eq_typeApp_of_ty_forall (Vty : [[ε ⊢ V : ∀ a : K. A]])
  : ∃ K E, V.1 = [[Λ a : K. E]] := sorry

private
theorem Value.eq_prodIntro_of_ty_prod (Vty : [[ε ⊢ V : ⊗ { </ A@i // i ∈ [0:n] /> }]])
  : ∃ V' : Nat → Value, V.1 = [[( </ V'@i // i ∈ [0:n] /> )]] := sorry

private
theorem Value.eq_sumIntro_of_ty_sum (Vty : [[ε ⊢ V : ⊕ { </ A@i // i ∈ [0:n'] /> }]])
  : ∃ n ∈ [0:n'], ∃ V', V.1 = [[ι n V']] := sorry

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
theorem progress.sandwich {f : Nat → α} (h : i < n) : (List.map (fun j => [f j]) [0:n]).flatten =
  (List.map (fun j => [f j]) [0:i]).flatten ++
    f i :: (List.map (fun j => [f (j + (i + 1))]) [(i + 1) - (i + 1):n - (i + 1)]).flatten := by
  simp only [List.map_singleton_flatten]
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
        have ⟨_, _, VE'eq⟩ := VE'.eq_lam_of_ty_arr E'tyA'arrB
        rw [this, VE'eq]
        exact .inl <| .intro _ <| .lamApp (V := ⟨F, FIsValue⟩)
  · case typeLam => exact .inr .typeLam
  · case typeApp E' K _ _ E'ty _ ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .typeApp E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, _, Veq⟩ := V.eq_typeApp_of_ty_forall E'ty
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
        rw [List.map_singleton_flatten] at Emem
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
      have ⟨n', mem, VE'', VE'_eq⟩ := VE'.eq_sumIntro_of_ty_sum E'ty
      cases VE'_eq
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
        rw [List.map_singleton_flatten, Range.map_eq_of_eq_of_mem' (fun i mem => by
          show F i = (VF i).val
          dsimp only [VF]
          rw [dif_pos mem.upper]
        ), ← List.map_singleton_flatten]
        exact .inl <| .intro _ <| .sumElimIntro mem
  · case equiv ih => exact ih rfl

theorem preservation : [[ε ⊢ E : A]] → [[E -> E']] → [[ε ⊢ E' : A]] := sorry

inductive Term.EvalError where
  | free (x : TermVar)
  | nonLamApp
  | nonTypeLamTypeApp
  | nonProdIntroProdElim
  | invalidProdIdx (n l : Nat)
  | nonSumIntroSumElim
  | nonLamSumElim

partial
def Term.eval (E : Term) : Except EvalError Value := do match E with
  | .var x => throw <| .free x
  | .lam A E => return ⟨.lam A E, .lam⟩
  | .app E F =>
    let ⟨.lam _ E', _⟩ ← eval E | throw <| .nonLamApp
    let F' ← eval F
    eval <| E'.Term_open F
  | .typeLam K E => return ⟨.typeLam K E, .typeLam⟩
  | .typeApp E A =>
    let ⟨.typeLam _ E', _⟩ ← eval E | throw <| .nonLamApp
    eval <| E'.Type_open A
  | .prodIntro Es =>
    let Vs ← Es.mapM eval
    return ⟨
      .prodIntro <| Vs.map (·.val),
      .prodIntro fun E mem => by
        let ⟨⟨_, EIsValue⟩, Vmem, .refl _⟩ := List.mem_map.mp mem
        exact EIsValue
    ⟩
  | .prodElim n E =>
    let ⟨.prodIntro Vs, VsAreValues⟩ ← eval E | throw .nonProdIntroProdElim
    let VsAreValues := match VsAreValues with | .prodIntro h => h
    if h : n < Vs.length then
      let V := Vs.get ⟨n, h⟩
      return ⟨V, VsAreValues V <| Vs.get_mem n h⟩
    else
      throw <| .invalidProdIdx n Vs.length
  | .sumIntro n E =>
    let V ← eval E
    return ⟨.sumIntro n V.val, .sumIntro V.property⟩
  | .sumElim E Fs =>
    let ⟨.sumIntro n VE, VEIsValue⟩ ← eval E | throw .nonSumIntroSumElim
    let VFs ← Fs.mapM eval
    let some ⟨.lam _ F', _⟩ := VFs.get? n | throw .nonLamSumElim
    eval <| F'.Term_open VE

end TabularTypeInterpreter.«F⊗⊕ω»
