import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Environment

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace Environment

termonly
def append (Δ : Environment) : Environment → Environment
  | empty => Δ
  | typeExt Δ' a K => Δ.append Δ' |>.typeExt a K
  | termExt Δ' x A => Δ.append Δ' |>.termExt x A

termonly
def TypeVar_subst (Δ : Environment) (a : TypeVarId) (A : «Type») := match Δ with
  | empty => empty
  | typeExt Δ' a' K => Δ'.TypeVar_subst a A |>.typeExt a' K
  | termExt Δ' x A' => Δ'.TypeVar_subst a A |>.termExt x <| A'.TypeVar_subst a A

termonly
def typeVarDom : Environment → List TypeVarId
  | .empty => []
  | .typeExt Γ a _ => a :: Γ.typeVarDom
  | .termExt Γ .. => Γ.typeVarDom

termonly
def termVarDom : Environment → List TermVarId
  | .empty => []
  | .typeExt Γ .. => Γ.termVarDom
  | .termExt Γ x _ => x :: Γ.termVarDom

termonly
@[app_unexpander append]
def delabEnvAppend : Lean.PrettyPrinter.Unexpander
  | `($(_) $Δ $Δ') =>
    let info := Lean.SourceInfo.none
    let comma := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ",") }
    `($Δ $comma $Δ')
  | _ => throw ()

termonly
attribute [app_unexpander TypeVar_subst] Type.delabTVSubst

end Environment

judgement_syntax a " : " K " ∈ " Δ : TypeVarInEnvironment (id a)

judgement TypeVarInEnvironment where

──────────────── head
a : K ∈ Δ, a : K

a : K ∈ Δ
a ≠ a'
────────────────── typeVarExt
a : K ∈ Δ, a' : K'

a : K ∈ Δ
──────────────── termVarExt
a : K ∈ Δ, x : A

@[app_unexpander TypeVarInEnvironment]
def TypeVarInEnvironment.delabTypeVarInEnv: Lean.PrettyPrinter.Unexpander
  | `($(_) $x $A $Δ) =>
    let info := Lean.SourceInfo.none
    let colon := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ":") }
    let in_ := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "∈") }
    `([ $x $colon $A $in_ $Δ ])
  | _ => throw ()

judgement_syntax x " : " A " ∈ " Δ : TermVarInEnvironment (id x)

judgement TermVarInEnvironment where

──────────────── head
x : A ∈ Δ, x : A

x : A ∈ Δ
──────────────── typeVarExt
x : A ∈ Δ, a : K

x : A ∈ Δ
x ≠ x'
───────────────── termVarExt
x : A ∈ Δ, x' : B

attribute [app_unexpander TermVarInEnvironment] TypeVarInEnvironment.delabTypeVarInEnv

judgement_syntax a " ∈ " "dom" "(" Δ ")" : Environment.TypeVarInDom (id a)

judgement Environment.TypeVarInDom := fun a (Δ : Environment) => a ∈ Δ.typeVarDom

judgement_syntax a " ∉ " "dom" "(" Δ ")" : Environment.TypeVarNotInDom (id a)

judgement Environment.TypeVarNotInDom := fun a Δ => ¬[[a ∈ dom(Δ)]]

judgement_syntax x " ∈ " "dom" "(" Δ ")" : Environment.TermVarInDom (id x)

judgement Environment.TermVarInDom := fun x (Δ : Environment) => x ∈ Δ.termVarDom

judgement_syntax x " ∉ " "dom" "(" Δ ")" : Environment.TermVarNotInDom (id x)

judgement Environment.TermVarNotInDom := fun x Δ => ¬[[x ∈ dom(Δ)]]

namespace Environment

@[app_unexpander TypeVarInDom, app_unexpander TermVarInDom]
def delabTVarInDom: Lean.PrettyPrinter.Unexpander
  | `($(_) $x $Δ) =>
    let info := Lean.SourceInfo.none
    let in_ := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "∈") }
    let domL := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "dom(") }
    let R := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ")") }
    `([ $x $in_ $domL $Δ $R ])
  | _ => throw ()

@[app_unexpander TypeVarNotInDom, app_unexpander TermVarNotInDom]
def delabTVarNotInDom: Lean.PrettyPrinter.Unexpander
  | `($(_) $x $Δ) =>
    let info := Lean.SourceInfo.none
    let notIn := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "∉") }
    let domL := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "dom(") }
    let R := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info ")") }
    `([ $x $notIn $domL $Δ $R ])
  | _ => throw ()

end Environment

end TabularTypeInterpreter.«F⊗⊕ω»
