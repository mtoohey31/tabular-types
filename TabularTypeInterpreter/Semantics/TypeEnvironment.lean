import TabularTypeInterpreter.Semantics.Basic
import TabularTypeInterpreter.Semantics.Type.Basic
import TabularTypeInterpreter.Syntax.TypeEnvironment

namespace TabularTypeInterpreter

namespace TypeEnvironment

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

judgement_syntax a " ∉ " "dom" "(" Γ ")" : TypeEnvironment.TypeVarNotInDom (id a)

def TypeEnvironment.TypeVarNotInDom a (Γ : TypeEnvironment) := a ∉ Γ.typeVarDom

instance : Coe TermVarId «F⊗⊕ω».TermVarId where coe x := x

judgement_syntax x " ∉ " "dom'" "(" Γ ")" : TypeEnvironment.TermVarNotInDom (id x)

def TypeEnvironment.TermVarNotInDom x (Γ : TypeEnvironment) := x ∉ Γ.termVarDom

end TabularTypeInterpreter
