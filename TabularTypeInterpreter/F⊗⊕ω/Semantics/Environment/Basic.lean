import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Environment

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace Environment

def append (Δ : Environment) : Environment → Environment
  | empty => Δ
  | typeExt Δ' a K => Δ.append Δ' |>.typeExt a K
  | termExt Δ' x A => Δ.append Δ' |>.termExt x A

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

judgement_syntax a " ∈ " "dom" "(" Δ ")" : Environment.InTypeVarInDom (id a)

def Environment.InTypeVarInDom a (Δ : Environment) := a ∈ Δ.typeVarDom

judgement_syntax a " ∉ " "dom" "(" Δ ")" : Environment.NotInTypeVarInDom (id a)

def Environment.NotInTypeVarInDom a Δ := ¬[[a ∈ dom(Δ)]]

judgement_syntax x " ∈ " "dom" "(" Δ ")" : Environment.InTermVarInDom (id x)

def Environment.InTermVarInDom x (Δ : Environment) := x ∈ Δ.termVarDom

judgement_syntax x " ∉ " "dom" "(" Δ ")" : Environment.NotInTermVarInDom (id x)

def Environment.NotInTermVarInDom x Δ := ¬[[x ∈ dom(Δ)]]

end TabularTypeInterpreter.«F⊗⊕ω»
