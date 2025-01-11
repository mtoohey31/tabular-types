import Lott
import Lott.Data.List
import Lott.Data.Range
import Lott.DSL.Elab.JudgementComprehension
import Lott.DSL.Elab.UniversalJudgement
import Lott.DSL.Elab.Nat
import Mathlib.Tactic
import TabularTypeInterpreter.List
import TabularTypeInterpreter.Tactic

namespace TabularTypeInterpreter.«F⊗⊕ω»

open TabularTypeInterpreter.Tactic

nonterminal Kind, K :=
  | "*"         : star
  | K₁ " ↦ " K₂ : arr
  | "L " K      : list
  | "(" K ")"   : paren (desugar := return K)

locally_nameless
metavar TypeVar, a

nonterminal «Type», A, B, C, T :=
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

@[app_unexpander Type.TypeVar_open]
def delabTVOpen: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a)
  | `($(_) $T $a 0) =>
    `( $T^$a )
  | `($(_) $T $a $n) =>
    `( $T^$a @ $n )
  | _ => throw ()

@[app_unexpander Type.Type_open]
def delabTOpen: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a)
  | `($(_) $T $a 0) =>
    `( $T^^$a )
  | `($(_) $T $a $n) =>
    `( $T^^$a @ $n )
  | _ => throw ()

@[app_unexpander Type.TypeVar_subst]
def delabTVSubst: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a $A) =>
    let info := Lean.SourceInfo.none
    let mapsto := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "↦") }
    `( $T[$a $mapsto $A])
  | _ => throw ()

attribute [aesop norm] «Type».Type_open «Type».TypeVar_open
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

@[app_unexpander Environment.empty]
def delabEempty : Lean.PrettyPrinter.Unexpander
  | `($(_)) =>
    let info := Lean.SourceInfo.none
    let eps := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "ε") }
    `( $eps )

@[app_unexpander Environment.typeExt, app_unexpander Environment.termExt]
def delabETypeExt : Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $a $K) =>
    let info := Lean.SourceInfo.none
    let comma := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ",") }
    let colon := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ":") }
    `( $Δ $comma $a $colon $K )
  | _ => throw ()
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

def typeVarDom : Environment → List TypeVarId
  | .empty => []
  | .typeExt Γ a _ => a :: Γ.typeVarDom
  | .termExt Γ .. => Γ.typeVarDom

def termVarDom : Environment → List TermVarId
  | .empty => []
  | .typeExt Γ .. => Γ.termVarDom
  | .termExt Γ x _ => x :: Γ.termVarDom

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

</ Δ ⊢ A@i : K // i in [:n] />
─────────────────────────────────── list
Δ ⊢ { </ A@i // i in [:n] /> } : L K

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

@[app_unexpander Kinding]
def delabK: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let colon := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ":") }
    `([ $Δ $vdash $A $colon $B ])
  | _ => throw ()

judgement_syntax a " ∈ " "dom" "(" Δ ")" : Environment.InTypeVarInDom (id a)

def Environment.InTypeVarInDom a (Δ : Environment) := a ∈ Δ.typeVarDom

judgement_syntax a " ∉ " "dom" "(" Δ ")" : Environment.NotInTypeVarInDom (id a)

def Environment.NotInTypeVarInDom a Δ := ¬[[a ∈ dom(Δ)]]

judgement_syntax x " ∈ " "dom" "(" Δ ")" : Environment.InTermVarInDom (id x)

def Environment.InTermVarInDom x (Δ : Environment) := x ∈ Δ.termVarDom

judgement_syntax x " ∉ " "dom" "(" Δ ")" : Environment.NotInTermVarInDom (id x)

def Environment.NotInTermVarInDom x Δ := ¬[[x ∈ dom(Δ)]]

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
  (Aki : Kinding [[(Δ, a : K, Δ')]] (A.TypeVar_open a n) K') (aninfvA : a ∉ A.fv)
  (Bki : [[Δ ⊢ B : K]]) : Kinding [[(Δ, (Δ' [B / a]))]] (A.Type_open B n) K' := sorry

-- theorem weakening1 : [[Δ, Δ'' ⊢ A : K]] → [[⊢ Δ, Δ', Δ'']] → [[Δ, Δ', Δ'' ⊢ A : K]] := sorry

-- theorem weakening2 : [[Δ ⊢ A : K]] → [[⊢ Δ, Δ']] → [[Δ, Δ' ⊢ A : K]] := sorry

theorem weakening : [[Δ ⊢ A : K]] → [[⊢ Δ', Δ, Δ'']] → [[Δ', Δ, Δ'' ⊢ A : K]] := sorry

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

-- TODO define TypeEq as sym trans closure of ParallelReduction

-- NOTE whatever definition we use, we want to be able to prove the following:
-- theorem eq_iff_pred : [[ Δ ⊢ A ≡ B ]] ↔ ( [[ Δ ⊢ A ≡>* B ]] ∨ [[ Δ ⊢ B ≡>* A ]])

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

</ Δ ⊢ B@i : K // i in [:n] />
─────────────────────────────────────────────────────────────────────────── lamListAppL
Δ ⊢ (λ a : K. A) ⟦{ </ B@i // i in [:n] /> }⟧ ≡ { </ A^^B@i // i in [:n] /> }

</ Δ ⊢ B@i : K // i in [:n] />
─────────────────────────────────────────────────────────────────────────── lamListAppR
Δ ⊢ { </ A^^B@i // i in [:n] /> } ≡ (λ a : K. A) ⟦{ </ B@i // i in [:n] /> }⟧

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

</ Δ ⊢ A@i ≡ B@i // i in [:n] />
───────────────────────────────────────────────────────── list
Δ ⊢ { </ A@i // i in [:n] /> } ≡ { </ B@i // i in [:n] /> }

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

judgement_syntax Δ " ⊢ " A " ≡> " B : ParallelReduction

judgement ParallelReduction :=

───────── refl
Δ ⊢ A ≡> A

Δ ⊢ B : K
∀ a ∉ (I: List _), Δ, a : K ⊢ A^a ≡> A'^a
Δ ⊢ B ≡> B'
────────────────────────────── lamApp
Δ ⊢ (λ a : K. A) B ≡> A'^^B'

</ Δ ⊢ B : K // (B, _) in (BB's: List («Type» × «Type»)) />
∀ a ∉ (I: List _), Δ, a : K ⊢ A^a ≡> A'^a
</ Δ ⊢ B ≡> B' // (B, B') in BB's />
──────────────────────────────────────────────────────────────────────────────── lamListApp
Δ ⊢ (λ a : K. A) ⟦{ </ B // (B, _) in BB's /> }⟧ ≡> { </ A'^^B' // (_, B') in BB's /> }

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

</ Δ ⊢ A ≡> B // (A, B) in (ABs : List («Type» × «Type»)) />
──────────────────────────────────────────────────────────────────────────────── list
Δ ⊢ { </ A // (A, _) in ABs /> } ≡> { </ B // (_, B) in ABs /> }

Δ ⊢ A₁ ≡> A₂
Δ ⊢ B₁ ≡> B₂
───────────────────── listApp
Δ ⊢ A₁ ⟦B₁⟧ ≡> A₂ ⟦B₂⟧

Δ ⊢ A ≡> B
───────────── prod
Δ ⊢ ⊗ A ≡> ⊗ B

Δ ⊢ A ≡> B
───────────── sum
Δ ⊢ ⊕ A ≡> ⊕ B

judgement_syntax Δ " ⊢ " A " ≡>* " B : MultiParallelReduction

judgement MultiParallelReduction :=

───────── refl
Δ ⊢ A ≡>* A

Δ ⊢ A ≡> A'
Δ ⊢ A' ≡>* A''
────────────── step
Δ ⊢ A ≡>* A''

@[app_unexpander ParallelReduction]
def delabPRed: Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $A $B) =>
    let info := Lean.SourceInfo.none
    let vdash := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "⊢") }
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "≡>") }
    `([ $Δ $vdash $A $into $B ])
  | _ => throw ()

attribute [aesop unsafe simp constructors] ParallelReduction
attribute [aesop unsafe simp constructors] MultiParallelReduction

private
theorem pred_inv_arr: [[ Δ ⊢ (A → B) ≡>* T ]] → (∃ A' B', T = [[(A' → B')]] ∧ [[ Δ ⊢ A ≡>* A' ]] ∧ [[ Δ ⊢ B ≡>* B' ]]) :=
by
  intro mred
  generalize AarrBeq : [[(A → B)]] = AarrB at mred
  revert A B
  induction mred
  . case refl => aesop
  . case step T1 T2 T3 red mred ih =>
    intro A B AarrBeq
    subst AarrBeq
    cases red <;> aesop

private
theorem pred_inv_lam: [[ Δ ⊢ (∀ a : K. A) ≡>* T ]] → (∃ A', T = [[∀ a : K. A']] ∧ (∃I, ∀a ∉ (I: List _), [[ Δ, a : K ⊢ A^a ≡>* A'^a ]])) :=
by
  intro mred
  generalize LamAeq : [[(∀ a : K. A)]] = LamA at mred
  revert A
  induction mred
  . case refl => aesop (add unsafe tactic guessI)
  . case step T1 T2 T3 red mred ih =>
    intro A LamAeq
    subst LamAeq
    cases red <;> aesop (add unsafe tactic guessI)

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

private
theorem open_red : ∀ a ∉ (I: List _), ∀ n, ParallelReduction Δ A A' -- FIXME a not in Δ or fv(A)
  → ParallelReduction (Δ.typeExt a K) (A.TypeVar_open a n) (A'.TypeVar_open a n) := by
  revert Δ A'

  induction A using («Type».rec (motive_2 := fun l =>  ∀A ∈ l, ∀(Δ: Environment) (A': «Type»), ∀ a ∉ (I: List _), ∀n, ParallelReduction (Δ.typeExt a K) (A.TypeVar_open a n) (A'.TypeVar_open a n)))
  . case var a =>
    intro x Δ a aI n red
    cases red
    constructor
  . case lam K' A ih =>
    intro Δ A' a aI n pred
    simp [«Type».TypeVar_open]
    -- TODO do induction on pred
    cases pred
    . case refl => aesop
    . case lam I A' pred =>
      -- why too many variables provided?
      rename_i I'
      simp [«Type».TypeVar_open]
      constructor
      case I => exact I ++ I'
      case a =>
        intro a' memI2
        sorry
  all_goals sorry

-- FIXME wrong! must do freevar subst.
-- NOTE the list part of this proof is helpful though
private
theorem subst_preserve_pred : [[ Δ ⊢ A ≡> A' ]] → [[ Δ ⊢ T^^A ≡> T^^A' ]] := by
  intro red

  induction T using («Type».rec (motive_2 := fun l => ∀T ∈ l, [[Δ ⊢ T^^A ≡> T^^A']])) <;> (try aesop; done)
  . case lam k T ih =>
    simp [«Type».Type_open]
    constructor
    case I => exact []  -- FIXME not in fv(?)
    case a =>
      simp_all [«Type».TypeVar_open, «Type».Type_open]
      sorry
  case list l ih =>
    induction l <;> (try aesop; done)
    . case cons hd tl tail_ih =>
      have ih' := ih hd (by aesop)
      have tail_ih' := tail_ih (by aesop)
      have H := @ParallelReduction.list (List.zip ((hd::tl).map (fun t => «Type».Type_open t A)) ((hd::tl).map (fun t => «Type».Type_open t A'))) Δ
      simp at H
      -- FIXME definition of PRed changed. Need to update whateverL1 and whateverL2
      -- repeat rw [List.whateverL1 (by aesop), List.whateverL2 (by aesop)] at H
      repeat rw [List.whateverflat] at H
      have H' := H ih' (by aesop (add unsafe forward List.zip_member_map_same))
      simp_all
      sorry
  all_goals sorry

private
theorem fv_open_not_in : ∀{A B: «Type»}, a ∉ A.fv → a ∉ B.fv → a ∉ (A.Type_open B n).fv := by
  intro A B notInAfv notInBfv
  revert n
  induction A using «Type».rec (motive_2 := fun l => ∀A ∈ l, ∀ n, a ∉ A.fv → a ∉ B.fv → a ∉ (A.Type_open B n).fv) <;> (aesop (add norm «Type».fv))


private
theorem fv_openvar_not_in: ∀{A: «Type»}, a ∉ A.fv → a != a' → a ∉ (A.TypeVar_open a' n).fv := by
  intro A notInAfv neq
  revert n
  induction A using «Type».rec (motive_2 := fun l => ∀A ∈ l, ∀ n, a ∉ A.fv → a != a' → a ∉ (A.TypeVar_open a' n).fv) <;> (aesop (add norm «Type».fv))

private
theorem fv_not_in_openvar: ∀{A: «Type»}, a ∉ (A.TypeVar_open a' n).fv → a != a' → a ∉ A.fv := sorry
  -- intro A notInAfv neq
  -- revert n
  -- induction A using «Type».rec (motive_2 := fun l => ∀A ∈ l, ∀ n, a ∉ (A.TypeVar_open a' n).fv → a != a' → a ∉ A.fv) <;> (aesop (add norm «Type».fv))

-- TODO make fv_open rules a rule_set. Challenge: collides with Aesop.BuiltinRules.intro_not

-- NOTE definitely true, can do that after I figure out how to deal with lists
private
theorem red_no_intro_fv: [[ Δ ⊢ A ≡> B ]] → ∀a, a ∉ A.fv → a ∉ B.fv := by
  intro red
  induction red <;> (try simp_all [«Type».fv]; done)
  . case lamApp Δ B K I A A' B' kinding redA redB ihA' ihB' =>
    simp [«Type».fv]
    intros a notInAfv notInBfv
    apply fv_open_not_in
    . have ⟨a', notInI⟩ := (I ++ A'.fv).exists_fresh
      by_cases a = a'
      . case pos eq => aesop
      . case neg neq =>
        have ihA' := ihA' a' (by aesop) a (fv_openvar_not_in notInAfv (by aesop))
        exact fv_not_in_openvar ihA' (by aesop)
    . aesop
  . case lamListApp => sorry
  . case lam I Δ K A B red ih =>
    intro a notInAfv
    simp [«Type».fv] at *
    have ⟨a', notInI⟩ := (a :: I).exists_fresh
    have ih' := ih a' (by aesop) a (by apply fv_openvar_not_in <;> aesop)
    apply fv_not_in_openvar at ih'
    aesop
  . case scheme I Δ K A B red ih =>
    intro a notInAfv
    simp [«Type».fv] at *
    have ⟨a', notInI⟩ := (a :: I).exists_fresh
    have ih' := ih a' (by aesop) a (by apply fv_openvar_not_in <;> aesop)
    apply fv_not_in_openvar at ih'
    aesop
  . case list => sorry

private
theorem red_lam_inversion : ∀I: List _, [[ Δ ⊢ (λ a? : K. A) ≡> T ]] → ∃ a A', a ∉ I ∧ T = [[λ a : K. A']] ∧ [[ Δ, a : K ⊢ A^a ≡> A'^a ]] := by
  intro I red
  cases red
  . case refl =>
    have ⟨a, notInI⟩ := I.exists_fresh
    exists a, A
    aesop
  . case lam I' A' red =>
    have ⟨a, notInI⟩ := (I ++ I').exists_fresh
    exists a, A'
    constructor <;> aesop

-- TODO CRITICAL, adopted from the paper
private
theorem lam_intro_ex : ∀a, a ∉ A.fv → a ∉ Δ.typeVarDom → [[ Δ, a : K ⊢ A^a ≡> B^a ]] → [[ Δ ⊢ (λ a : K. A) ≡> (λ a : K. B) ]] := sorry

private
theorem forall_intro_ex : ∀a, a ∉ A.fv → a ∉ Δ.typeVarDom → [[ Δ, a : K ⊢ A^a ≡> B^a ]] → [[ Δ ⊢ (∀ a : K. A) ≡> (∀ a : K. B) ]] := sorry

private
theorem lam_intro_ex_k : ∀a, a ∉ A.fv → a ∉ Δ.typeVarDom → [[ Δ, a : K1 ⊢ A^a: K2 ]] → [[ Δ ⊢ (λ a : K1. A) : K1 ↦ K2 ]] := sorry

private
theorem forall_intro_ex_k : ∀a, a ∉ A.fv → a ∉ Δ.typeVarDom → [[ Δ, a : K1 ⊢ A^a: K2 ]] → [[ Δ ⊢ (∀ a : K1. A) : K2 ]] := sorry

-- NOTE correct, but might not needed
private
theorem type_exists_close_at: ∀(T: «Type»), ∃ n, T.TypeVarLocallyClosed n := sorry

-- NOTE I believe it should be correct
private
theorem pred_preserve_lc (red: [[ Δ ⊢ A ≡> B ]]): ∀n, A.TypeVarLocallyClosed n → B.TypeVarLocallyClosed n := sorry

-- NOTE correct, from the paper. But so far all usage (->) of this lemma can be replaced by TypeVarLocallyClosed_open
private
theorem lc_abs_iff_body: («Type».lam K A).TypeVarLocallyClosed n ↔ ∃(I: List _), ∀x ∉ I, (A.TypeVar_open x n).TypeVarLocallyClosed n := sorry

-- NOTE correct, from the paper
private
theorem close_open_var {T: «Type»} a (lc: T.TypeVarLocallyClosed n): (T.TypeVar_close a n).TypeVar_open a n = T := sorry

-- NOTE correct, from the paper
private
theorem open_close_var {T: «Type»} a (nfv: a ∉ T.fv): (T.TypeVar_open a n).TypeVar_close a n = T := sorry

private
theorem Var_open_noop: ∀{T: «Type»} a, a ∉ T.fv → T.TypeVar_open a n = T := sorry

add_aesop_rules safe «Type».TypeVarLocallyClosed
add_aesop_rules unsafe cases «Type».TypeVarLocallyClosed
-- NOTE there's another way to do inversion on (lam).lc, lc_abs_iff_body, which uses coquantification
-- but I'm not sure whether it's better or not

private
theorem TypeVarLocallyClosed_close : ∀{T: «Type»} n a, T.TypeVarLocallyClosed n → (T.TypeVar_close a n).TypeVarLocallyClosed (n + 1) := by
  intro T
  induction T using «Type».rec (motive_2 := fun l => ∀T ∈ l, ∀a n, T.TypeVarLocallyClosed n → (T.TypeVar_close a n).TypeVarLocallyClosed (n + 1)) <;> (try aesop (add norm «Type».TypeVar_close); done)
  . case var x =>
    simp [«Type».TypeVar_close]
    intro n fid lc
    by_cases (TypeVar.free fid = x)
    . case pos eq => aesop
    . case neg neq =>
      simp [*]
      apply Type.TypeVarLocallyClosed.weaken
      assumption


private
theorem TypeVarLocallyClosed_open : ∀{T: «Type»} n a, T.TypeVarLocallyClosed (n + 1) → (T.TypeVar_open a n).TypeVarLocallyClosed n := by
  intro T
  induction T using «Type».rec (motive_2 := fun l => ∀T ∈ l, ∀a n, T.TypeVarLocallyClosed (n + 1) → (T.TypeVar_open a n).TypeVarLocallyClosed n) <;> (try aesop (add norm «Type».TypeVar_open); done)
  . case var x =>
    simp [«Type».TypeVar_open]
    intro a n lc
    cases x
    . case free fid => aesop
    . case bound bid =>
      simp
      by_cases (a = bid)
      . case pos eq =>
        aesop
      . case neg neq =>
        simp [*]
        cases lc
        case var_bound h =>
        constructor
        cases h <;> aesop


private
theorem TypeVarLocallyClosed_openT : ∀{T A: «Type»} n, T.TypeVarLocallyClosed (n + 1) → A.TypeVarLocallyClosed n → (T.Type_open A n).TypeVarLocallyClosed n := sorry

private theorem open_rec_lc {T: «Type»} (lc: T.TypeVarLocallyClosed n) (h: m >= n): T.Type_open B m = T := by
  induction lc generalizing m <;> simp_all [Type.Type_open]
  . case var_bound m' n' h' =>
    intro contra
    simp_all [Nat.not_lt_of_ge]

private
theorem subst_open {A B T: «Type»} (lcT: T.TypeVarLocallyClosed n) : (A.TypeVar_subst a T).Type_open (B.TypeVar_subst a T) n = (A.Type_open B n).TypeVar_subst a T := by
  induction A using «Type».rec (motive_2 := fun l => ∀A ∈ l, ∀B T n, T.TypeVarLocallyClosed n → (A.TypeVar_subst a T).Type_open (B.TypeVar_subst a T) n = (A.Type_open B n).TypeVar_subst a T) generalizing B T n <;>
    aesop (add norm «Type».TypeVar_subst) (add norm «Type».Type_open) (add safe open_rec_lc) (add safe Type.TypeVarLocallyClosed.weaken)

-- NOTE Proof in the paper is wrong. subst_intro doesn't require lc B, while subst_open does.
private
theorem subst_intro {A: «Type»} (nfv: a ∉ A.fv): (A.TypeVar_open a n).TypeVar_subst a B = A.Type_open B n := by
  induction A using «Type».rec (motive_2 := fun l => ∀A ∈ l, ∀B n, a ∉ A.fv → (A.TypeVar_open a n).TypeVar_subst a B = A.Type_open B n) generalizing B n <;>
    aesop (add norm Type.TypeVar_subst) (add norm Type.TypeVar_open) (add norm Type.Type_open) (add norm Type.fv)

private
theorem subst_lc {A B: «Type»} (lcA: A.TypeVarLocallyClosed n) (lcB: B.TypeVarLocallyClosed n): (A.TypeVar_subst a B).TypeVarLocallyClosed n := by
  induction lcA <;> aesop (add norm Type.TypeVar_subst) (add norm Type.TypeVarLocallyClosed.weaken)

private
theorem subst_open_var {T A: «Type»} (neq: x ≠ y) (lc: A.TypeVarLocallyClosed n): (T.TypeVar_open y n).TypeVar_subst x A = (T.TypeVar_subst x A).TypeVar_open y n := sorry

private
theorem subst_close_var {T A: «Type»} (neq: x ≠ y) (fresh: y ∉ A.fv): (T.TypeVar_close y n).TypeVar_subst x A = (T.TypeVar_subst x A).TypeVar_close y n := sorry

private
theorem subst_fresh {A T : «Type»} (fresh: a ∉ A.fv) : a ∉ (T.TypeVar_subst a A |>.fv) := sorry

private
theorem kinding_subst' (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kA: [[ Δ ⊢ A: K ]]) (kT: [[ Δ, a: K, Δ' ⊢ T: K' ]]): Kinding (Δ.append Δ') (T.TypeVar_subst a A) K' := by
  generalize Δ'eq: (Δ.typeExt a K).append Δ' = Δ_ at kT
  induction kT generalizing Δ Δ' a A K <;> simp_all [«Type».TypeVar_subst]
  . case var a' K' Δ_ kIn =>
    subst Δ_
    -- FIXME need to prove TypeVarInEnvironment_exchange (env)
    -- by_cases (a = a')
    -- . case pos eq =>
    --   simp_all
    --   cases kIn
    --   . assumption
    --   . simp_all [TypeVarNe]
    -- . case neg neq =>
    --   simp_all
    --   constructor
    --   cases kIn <;> simp_all
    sorry
  all_goals sorry

private
theorem kinding_subst (wf: [[ ⊢ Δ, a: K ]]) (kA: [[ Δ ⊢ A: K ]]) (kT: [[ Δ, a: K ⊢ T: K' ]]): Kinding Δ (T.TypeVar_subst a A) K' :=
 by apply kinding_subst' (Δ' := Environment.empty) <;> assumption

-- FIXME critical, trivial
private
theorem pred_subst_same' {A B T: «Type»} (red: [[ Δ ⊢ A ≡> B ]]) (nfvT: a ∉ T.fv): ParallelReduction Δ (T.TypeVar_subst a A) (T.TypeVar_subst a B) := sorry

-- FIXME critical
private
theorem pred_subst_same {A B T: «Type»} (red: [[ Δ ⊢ A ≡> B ]]) (fresh: a ∉ Δ.typeVarDom ++ A.fv): ParallelReduction Δ (T.TypeVar_subst a A) (T.TypeVar_subst a B) := by
  induction T using «Type».rec (motive_2 := fun l => ∀T ∈ l, ∀(Δ: Environment) (A B: «Type») (a: TypeVarId) (red: [[ Δ ⊢ A ≡> B ]]) (fresh: a ∉ Δ.typeVarDom ++ A.fv), ParallelReduction Δ (T.TypeVar_subst a A) (T.TypeVar_subst a B)) generalizing A B a Δ <;> (try simp [«Type».TypeVar_subst]) <;> (try aesop; done)
  . case lam K T ih =>
    -- FIXME problematic
    apply (lam_intro_ex a)
    . simp_all [subst_fresh]
    . simp_all
    . sorry -- NOTE direct consequence of pred_open. Need to finish that first.
  . case «forall» K T ih =>
    -- NOTE same as lam
    apply (forall_intro_ex a)
    . simp_all [subst_fresh]
    . simp_all
    . sorry
  . case list Tl ih =>
    -- TODO list
    sorry


-- FIXME critical, trivial
-- TODO better name, also is this really needed?
private
theorem pred_subst_better_name {A B T: «Type»} (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ ⊢ T ≡> T' ]]) (nfv: a ∉ T.fv) : ParallelReduction Δ (T.TypeVar_subst a A) (T'.TypeVar_subst a B) := sorry

-- FIXME critical. from pred_subst_same: kindT is really annoying.. It stops us from using the lemma in
-- (also, might be able to conclude that Δ ⊢ T[a ↦ A]: K')
private
theorem pred_subst {A B T: «Type»} (wf: [[ ⊢ Δ, a: K ]]) (red1: [[ Δ ⊢ A ≡> B ]]) (red2: [[ Δ, a: K ⊢ T ≡> T' ]]) (kindA: [[ Δ ⊢ A: K ]]) (fresh: a ∉ Δ.typeVarDom ++ A.fv) (lc: B.TypeVarLocallyClosed): ParallelReduction Δ (T.TypeVar_subst a A) (T'.TypeVar_subst a B) := by
  generalize Δ'eq: Δ.typeExt a K = Δ' at red2
  induction red2 generalizing Δ A B
  . case refl Δ_ T_ =>
    apply pred_subst_same <;> simp_all
  . case lamApp Δ_ T2 K2 I T1 T1' T2' kindT2 redT1 redT2 ihT1 ihT2 =>
    subst Δ_
    simp [«Type».TypeVar_subst]
    rw  [<- subst_open (lcT := lc)]
    apply ParallelReduction.lamApp
    . apply kinding_subst (K := K) <;> assumption
    . sorry -- FIXME must change definition of pred_subst to make it more generic, e.g. (Δ, a : K, Δ')
    . aesop
    . sorry -- metavar I, solved in subgoal 2
  all_goals sorry

-- TODO is this lemma needed?
private
theorem TypeVarInEnvironment.det : [[ a: K ∈ Δ ]] → [[ a: K' ∈ Δ ]] → K = K' := by
  intro h
  induction h
  . case head =>
    intro k
    cases k <;> simp_all [TypeVarNe]
  . case typeVarExt =>
    intro k
    cases k <;> simp_all [TypeVarNe]
  . case termVarExt =>
    intro k
    cases k; simp_all

-- TODO is this lemma needed? probably in some env exchange lemma..
private
theorem Kinding.det : [[ Δ ⊢ A: K ]] → [[ Δ ⊢ A: K' ]] → K = K' := by
  intro k
  induction k generalizing K'
  . case var => aesop (add safe cases Kinding) (add safe TypeVarInEnvironment.det)
  . case lam I Δ K1 A K2 kindA ih =>
    intro k
    cases k
    case lam I' K2' kindA' =>
    simp
    have ⟨a, notIn⟩ := (I ++ I').exists_fresh
    apply ih a (by aesop)
    apply kindA' a (by aesop)
  . case app =>
    rename_i ihA ihB
    intro k
    cases k
    rename_i kB kA
    apply ihA at kA
    apply ihB at kB
    simp_all
  all_goals sorry -- TODO It's obviously provable, but very tedious

-- NOTE must have for conf_lamApp: needed when using pred_subst
private
theorem pred_preservation : [[ ⊢ Δ ]] → [[ Δ ⊢ A ≡> B ]] → [[ Δ ⊢ A: K ]] → [[ Δ ⊢ B: K ]] := by
  intro wf red
  induction red generalizing K
  . case refl => simp
  . case lamApp Δ B KB I A A' B' kindB redA redB ihA ihB =>
    intro k
    cases k
    case app _ _ k =>
    cases k
    case lam I' _ kindA =>
    have ⟨a, notInI⟩ := (I ++ I' ++ A'.fv ++ Δ.typeVarDom).exists_fresh
    have wf': [[ ⊢ Δ, a: KB ]] := by
      constructor
      . assumption
      . simp [Environment.NotInTypeVarInDom, Environment.InTypeVarInDom]; aesop

    have kindA' := ihA a (by aesop) wf' (kindA a (by aesop))
    have kindB' := ihB wf kindB
    rw [<- subst_intro (a:=a) (nfv := by aesop)]
    apply kinding_subst <;> assumption
  . case lamListApp => sorry
  . case lam I Δ K1 A B red ih =>
    intro k
    cases k
    case lam I' K2 kindA =>
    have ⟨a, notIn⟩ := (I ++ I' ++ Δ.typeVarDom ++ B.fv).exists_fresh
    have wf': [[ ⊢ Δ, a: K1 ]] := by
      constructor
      . assumption
      . simp [Environment.NotInTypeVarInDom, Environment.InTypeVarInDom]; aesop
    apply lam_intro_ex_k a <;> aesop
  . case app =>
    intro k
    cases k
    constructor <;> aesop
  . case scheme I Δ K1 A B red ih =>
    intro k
    cases k
    case scheme I' kindA =>
    have ⟨a, notIn⟩ := (I ++ I' ++ Δ.typeVarDom ++ B.fv).exists_fresh
    have wf': [[ ⊢ Δ, a: K1 ]] := by
      constructor
      . assumption
      . simp [Environment.NotInTypeVarInDom, Environment.InTypeVarInDom]; aesop
    apply forall_intro_ex_k a <;> aesop
  . case arr =>
    intro k
    cases k
    constructor <;> aesop
  . case list => sorry
  . case listApp => sorry
  . case prod =>
    intro k
    cases k
    constructor; aesop
  . case sum =>
    intro k
    cases k
    constructor; aesop

-- NOTE critical
-- if we need to have kindT in subst_intro, we need to add kinding for A as precondition
private
theorem pred_confluence_single : [[ ⊢ Δ ]] → [[ Δ ⊢ A ≡> B ]] -> [[ Δ ⊢ A ≡> C ]] -> A.TypeVarLocallyClosed -> ∃ T, [[ Δ ⊢ B ≡> T ]] ∧ [[ Δ ⊢ C ≡> T ]] ∧ T.TypeVarLocallyClosed := by
  intro wf red1
  revert C
  induction red1
  case lam I Δ' K A' B' red1 ih =>
    clear Δ A B
    intro C red2 lcA

    -- NOTE alternatively, lc_abs_iff_body
    cases lcA
    case lam lcA =>

    have ⟨a, C', notIn, eqC, red2'⟩ := red_lam_inversion (I ++ A'.fv ++ B'.fv ++ C.fv ++ Δ'.typeVarDom) red2
    subst C
    have freshC' : a ∉ C'.fv := by
      apply red_no_intro_fv at red2
      simp_all [«Type».fv]
    have wf' : [[ ⊢ Δ', a: K ]] := by
      constructor
      . assumption
      . simp [Environment.NotInTypeVarInDom, Environment.InTypeVarInDom]; aesop

    have ⟨T', predA, predB, lcT'⟩ := ih a (by aesop) wf' red2' (by
        -- NOTE if we used lc_abs_iff_body, this is trivial
        apply TypeVarLocallyClosed_open
        assumption
    ); clear ih

    rw [<- close_open_var (T:=T') (a:=a)] at predA predB <;> try assumption

    exists («Type».lam K (T'.TypeVar_close a))

    constructor
    . apply (lam_intro_ex a) <;> aesop
    . constructor
      . apply (lam_intro_ex a) <;> aesop
      . constructor
        apply TypeVarLocallyClosed_close
        assumption
  case lamApp Δ' B_ K I A_ A' B' k redA redB ihA ihB =>
    clear A B Δ
    rename' A_ => A, B_ => B, Δ' => Δ

    intro C redAB lcAB


    cases lcAB
    case app lcA lcB =>
    cases lcA
    case lam lcA =>
    have H : ∀a, (A.TypeVar_open a).TypeVarLocallyClosed := by simp_all [TypeVarLocallyClosed_open]
    simp_all
    cases redAB
    . case refl =>
      exists (A'.Type_open B')
      repeat' apply And.intro
      . constructor
      . apply ParallelReduction.lamApp (I:=I) <;> try simp_all
      . apply pred_preserve_lc (red := redB) at lcB
        have lcA': A'.TypeVarLocallyClosed 1 := by
          let ⟨a, notInI⟩ := (I ++ A'.fv).exists_fresh
          specialize redA a (by simp_all)
          apply TypeVarLocallyClosed_open (a:=a) at lcA
          apply pred_preserve_lc (red := redA) at lcA
          apply TypeVarLocallyClosed_close (a := a) at lcA
          rw [open_close_var (nfv := by simp_all)] at lcA
          assumption
        simp_all [TypeVarLocallyClosed_openT]
    . case lamApp I' A2 B2 redA' redB' _ =>
      have ⟨a, notInI⟩ := (I ++ I' ++ A'.fv ++ A2.fv ++ Δ.typeVarDom ++ B'.fv).exists_fresh
      have wf' : [[ ⊢ Δ, a: K ]] := by
        constructor
        . assumption
        . simp [Environment.NotInTypeVarInDom, Environment.InTypeVarInDom]; aesop
      specialize redA' a (by simp_all)
      have ⟨T1, redA'T, redA2T, lcT1⟩ := ihA a (by simp_all) wf' redA'; clear redA'
      have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'
      exists T1.TypeVar_subst a T2
      repeat' apply And.intro
      -- FIXME cooked. need to finish the definition of subst_intro first
      . rw [<- subst_intro (a := a) (nfv := by simp_all)]
        apply pred_subst <;> try assumption
        . exact pred_preservation wf redB (by assumption)
        . aesop
      . rw [<- subst_intro (a := a) (nfv := by simp_all)]
        apply pred_subst
        all_goals sorry
      . apply subst_lc <;> assumption
    . case app A2 B2 redA' redB' =>
      cases redA'
      . case refl => sorry
      . case lam I' B22 redA' =>
        -- this is morally also lamApp
        have ⟨a, notInI⟩ := (I ++ I' ++ A'.fv ++ B22.fv ++ Δ.typeVarDom).exists_fresh
        have wf' : [[ ⊢ Δ, a: K ]] := by
          constructor
          . assumption
          . simp [Environment.NotInTypeVarInDom, Environment.InTypeVarInDom]; aesop
        specialize redA' a (by simp_all)
        have ⟨T1, redA'T, redA2T, lcT1⟩ := ihA a (by simp_all) wf' redA'; clear redA'
        have ⟨T2, redB'T, redB2T, lcT2⟩ := ihB redB'
        exists T1.TypeVar_subst a T2
        repeat' apply And.intro
        -- FIXME also cooked due to subst_intro
        . rw [<- subst_intro (a := a) (nfv := by simp_all)]
          apply pred_subst
          all_goals sorry
        . sorry
        . apply subst_lc <;> assumption
  all_goals sorry


private
theorem equiv_common_reduct : [[ Δ ⊢ A ≡ B ]] → exists C, [[ Δ ⊢ A ≡>* C ]] ∧ [[ Δ ⊢ B ≡>* C ]] := by
  intros
  apply Exists.intro _
  all_goals sorry


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

</ Δ ⊢ E@i : A@i // i in [:n] />
─────────────────────────────────────────────────────────── prodIntro
Δ ⊢ ( </ E@i // i in [:n] /> ) : ⊗ { </ A@i // i in [:n] /> }

Δ ⊢ E : ⊗ { </ A@i // i in [:n'] /> }
n ∈ [0:n']
──────────────────────────────────── prodElim
Δ ⊢ π n E : A@n

n ∈ [0:n']
Δ ⊢ E : A@n
──────────────────────────────────────── sumIntro
Δ ⊢ ι n E : ⊕ { </ A@i // i in [:n'] /> }

Δ ⊢ E : ⊕ { </ A@i // i in [:n] /> }
</ Δ ⊢ F@i : A@i → B // i in [:n] />
──────────────────────────────────────── sumElim
Δ ⊢ case E { </ F@i // i in [:n] /> } : B

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
( </ V@i // i in [:n] />, E, </ F@j // j in [:m] /> ) -> ( </ V@i // i in [:n] />, E', </ F@j // j in [:m] /> )

E -> E'
───────────────────────────────────── prodElim
π n E -> π n E'

n ∈ [0:n']
───────────────────────────────────── prodElimIntro
π n ( </ V@i // i in [:n'] /> ) -> V@n

E -> E'
─────────────── sumIntro
ι n E -> ι n E'

E -> E'
───────────────────────────────────────────────────────────────────── sumElimL
case E { </ F@i // i in [:n] /> } -> case E' { </ F@i // i in [:n] /> }

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sumElimR
case V { </ V'@i // i in [:n] />, E, </ F@j // j in [:m] /> } -> case V { </ V'@i // i in [:n] />, E', </ F@j // j in [:m] /> }

n ∈ [0:n']
────────────────────────────────────────────────────── sumElimIntro
case ι n V { </ V'@i // i in [:n'] /> } -> V'@n ⦅ι n V⦆

private
theorem ty_lam_ty_eq_forall (Ety: [[Δ ⊢ Λ a : K. E: T]]) : ∃ T', [[Δ ⊢ T ≡ ∀ a : K. T']] := by
  generalize LamEeq : [[Λ a : K. E]] = LamE at Ety
  induction Ety <;> (try (aesop; done))
  . case typeLam =>
    aesop (add unsafe TypeEquivalence)
  . case equiv =>
    aesop
    exists w
    exact (a_1.symm).trans h

-- canonical form of abstractions
private
theorem Value.eq_lam_of_ty_arr (VtyAarrB : [[Δ ⊢ V : A → B]])
  : ∃ A' E, V.1 = [[λ x : A'. E]] := by
  obtain ⟨E, isV⟩ := V ; simp
  cases isV <;> simp at *
  .case typeLam K E =>
    have ⟨T, Eeq⟩ := ty_lam_ty_eq_forall VtyAarrB
    have ⟨U, mredArr, mredForall⟩ := equiv_common_reduct Eeq
    have ⟨A', E', Eeq', AarrBeq⟩ := pred_inv_lam mredForall
    have ⟨A'', E'', Eeq'', AarrBeq'⟩ := pred_inv_arr mredArr
    aesop
  .case prodIntro => sorry
  .case sumIntro => sorry

private
theorem Value.eq_typeApp_of_ty_forall (Vty : [[ε ⊢ V : ∀ a : K. A]])
  : ∃ K E, V.1 = [[Λ a : K. E]] := sorry

private
theorem Value.eq_prodIntro_of_ty_prod (Vty : [[ε ⊢ V : ⊗ { </ A@i // i in [0:n] /> }]])
  : ∃ V' : Nat → Value, V.1 = [[( </ V'@i // i in [0:n] /> )]] := sorry

private
theorem Value.eq_sumIntro_of_ty_sum (Vty : [[ε ⊢ V : ⊕ { </ A@i // i in [0:n'] /> }]])
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
        rw [progress.sandwich jltn, Range.map_eq_of_eq_of_mem (fun j jmem => by
          show [F j] = [(VF j).val]
          dsimp only [VF]
          rw [dif_pos jmem.upper]
        ), Nat.sub_self]
        exact .inl <| .intro _ <| .sumElimR (V := VE') toF'
      | .inr FIsValue =>
        let VF j : Value := if h : j < n then ⟨F j, FIsValue j ⟨Nat.zero_le _, h⟩⟩ else default
        rw [List.map_singleton_flatten, Range.map_eq_of_eq_of_mem (fun i mem => by
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
