import TabularTypeInterpreter.Semantics.Basic
import TabularTypeInterpreter.Semantics.Type.Basic
import TabularTypeInterpreter.Syntax.TypeEnvironment

namespace TabularTypeInterpreter

namespace TypeEnvironment

def multiTypeExt (Γ : TypeEnvironment) : List (TypeVarId × Kind) → TypeEnvironment
  | [] => Γ
  | (a, κ) :: aκs => Γ.typeExt a κ |>.multiTypeExt aκs

def append (Γ : TypeEnvironment) : TypeEnvironment → TypeEnvironment
  | empty => Γ
  | typeExt Γ' a κ => Γ.append Γ' |>.typeExt a κ
  | termExt Γ' x σ => Γ.append Γ' |>.termExt x σ
  | constrExt Γ' ψ x => Γ.append Γ' |>.constrExt ψ x

def TypeVar_subst (Γ : TypeEnvironment) (a : TypeVarId) (τ : Monotype) := match Γ with
  | empty => empty
  | typeExt Γ' a' κ => Γ'.TypeVar_subst a τ |>.typeExt a' κ
  | termExt Γ' x σ => Γ'.TypeVar_subst a τ |>.termExt x <| σ.TypeVar_subst a τ
  | constrExt Γ' ψ x => Γ'.TypeVar_subst a τ |>.constrExt (ψ.TypeVar_subst a τ) x

def typeVarDom : TypeEnvironment → List TypeVarId
  | empty => []
  | typeExt Γ a _ => a :: Γ.typeVarDom
  | termExt Γ .. => Γ.typeVarDom
  | constrExt Γ .. => Γ.typeVarDom

def termVarDom : TypeEnvironment → List TermVarId
  | empty => []
  | typeExt Γ .. => Γ.termVarDom
  | termExt Γ x _ => x :: Γ.termVarDom
  | constrExt Γ _ x => x :: Γ.termVarDom

@[simp]
noncomputable
def sizeOf' : TypeEnvironment → Nat
  | empty => 1
  | typeExt Γ _ _ => 1 + Γ.sizeOf'
  | termExt Γ _ σ => 1 + Γ.sizeOf' + σ.sizeOf'
  | constrExt Γ ψ _ => 3 + Γ.sizeOf' + ψ.sizeOf'

end TypeEnvironment

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

judgement_syntax x " : " σ " ∈ " Γ : TypeEnvironment.TermVarIn (id x)

judgement TypeEnvironment.TermVarIn :=

──────────────── head
x : σ ∈ Γ, x : σ

x : σ ∈ Γ
──────────────── typeExt
x : σ ∈ Γ, a : κ

x ≠ x'
x : σ ∈ Γ
────────────────── termExt
x : σ ∈ Γ, x' : σ'

x ≠ x'
x : σ ∈ Γ
───────────────── constrExt
x : σ ∈ Γ, ψ ⇝ x'

judgement_syntax ψ " ⇝ " «F⊗⊕ω».x " ∈ " Γ : TypeEnvironment.ConstrIn (id x)

judgement TypeEnvironment.ConstrIn :=

──────────────── head
ψ ⇝ x ∈ Γ, ψ ⇝ x

ψ ⇝ x ∈ Γ
──────────────── typeExt
ψ ⇝ x ∈ Γ, a : κ

x ≠ x'
ψ ⇝ x ∈ Γ
───────────────── termExt
ψ ⇝ x ∈ Γ, x' : σ

x ≠ x'
ψ ⇝ x ∈ Γ
────────────────── constrExt
ψ ⇝ x ∈ Γ, ψ' ⇝ x'

judgement_syntax a " ∉ " "dom" "(" Γ ")" : TypeEnvironment.TypeVarNotInDom (id a)

def TypeEnvironment.TypeVarNotInDom a (Γ : TypeEnvironment) := a ∉ Γ.typeVarDom

instance : Coe TermVarId «F⊗⊕ω».TermVarId where coe x := x

judgement_syntax x " ∉ " "dom'" "(" Γ ")" : TypeEnvironment.TermVarNotInDom (id x)

def TypeEnvironment.TermVarNotInDom x (Γ : TypeEnvironment) := x ∉ Γ.termVarDom

end TabularTypeInterpreter
