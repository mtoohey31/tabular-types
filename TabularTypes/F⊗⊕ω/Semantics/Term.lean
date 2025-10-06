import TabularTypes.«F⊗⊕ω».Semantics.Environment
import TabularTypes.«F⊗⊕ω».Semantics.Type
import TabularTypes.«F⊗⊕ω».Syntax.Value

namespace TabularTypes.«F⊗⊕ω»

namespace Term

termonly
def multi_app (Es : List Term) (F : Term) : Term := match Es with
  | [] => F
  | E :: Es' => multi_app Es' <| E.app F

termonly
def TypeVar_multi_open (E : Term) (a : Nat → TypeVarId) : Nat → Term
  | 0 => E
  | n + 1 => E.TypeVar_open (a n) n |>.TypeVar_multi_open a n

termonly
def TermVar_multi_open (E : Term) (x : Nat → TermVarId) : Nat → Term
  | 0 => E
  | n + 1 => E.TermVar_open (x n) n |>.TermVar_multi_open x n

termonly
def Type_multi_open (E : Term) (A : Nat → «Type») : Nat → Term
  | 0 => E
  | n + 1 => E.Type_open (A n) n |>.Type_multi_open A n

termonly
def Term_multi_open (E : Term) (F : Nat → Term) : Nat → Term
  | 0 => E
  | n + 1 => E.Term_open (F n) n |>.Term_multi_open F n

end Term

judgement_syntax Δ " ⊢ " E " : " A : Typing

judgement Typing where

⊢ Δ
x : A ∈ Δ
───────── var
Δ ⊢ x : A

∀ x ∉ I, Δ, x : A ⊢ E^x : B
─────────────────────────── lam (I : List TermVarId)
Δ ⊢ λ x : A. E : A → B

Δ ⊢ E : A → B
Δ ⊢ F : A
───────────── app
Δ ⊢ E F : B

∀ a ∉ I, Δ, a : K ⊢ E^a : A^a
───────────────────────────── typeLam (I : List TypeVarId)
Δ ⊢ Λ a : K. E : ∀ a : K. A

Δ ⊢ E : ∀ a : K. A
Δ ⊢ B : K
────────────────── typeApp
Δ ⊢ E [B] : A^^B/a

⊢ Δ
</ Δ ⊢ E@i : A@i // i in [:n] notex />
notex n ≠ 0 ∨ b
──────────────────────────────────────────────────────────────────────────────────── prodIntro
Δ ⊢ (</ E@i // i in [:n] notex />) : ⊗ {</ A@i // i in [:n] notex /> </ : * // b />}

Δ ⊢ E : ⊗ {</ A@i // i in [:n] /> </ : * // b />}
j ∈ [:n]
───────────────────────────────────────────────── prodElim
Δ ⊢ π j E : A@j

j ∈ [:n]
Δ ⊢ E : A@j
</ Δ ⊢ A@i : * // i in [:n] />
notex n ≠ 0 ∨ b
───────────────────────────────────────────────────── sumIntro
Δ ⊢ ι j E : ⊕ {</ A@i // i in [:n] /> </ : * // b />}

Δ ⊢ E : ⊕ {</ A@i // i in [:n] notex /> </ : * // b />}
</ Δ ⊢ F@i : A@i → B // i in [:n] notex />
Δ ⊢ B : *
─────────────────────────────────────────────────────── sumElim
Δ ⊢ case E {</ F@i // i in [:n] notex />} : B

Δ ⊢ E : A
Δ ⊢ A ≡ B
───────── equiv
Δ ⊢ E : B

termonly
attribute [app_unexpander Typing] Kinding.delabK

judgement_syntax E " -> " F : OperationalSemantics (tex := s!"{E} \\, \\lottsym\{⟶} \\, {F}")

judgement OperationalSemantics where

E -> E'
─────────── appL
E F -> E' F

F -> F'
─────────── appR
V F -> V F'

──────────────────────── lamApp
⦅λ x : A. E⦆ V -> E^^V/x

E -> E'
─────────────── typeApp
E [A] -> E' [A]

────────────────────────── typeLamApp
⦅Λ a : K. E⦆ [A] -> E^^A/a

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── prodIntro
(</ V@i // i in [:n] notex />, E, </ F@j // j in [:m] notex />) -> (</ V@i // i in [:n] notex />, E', </ F@j // j in [:m] notex />)

E -> E'
───────────────────────────────────── prodElim
π i E -> π i E'

j ∈ [:n]
─────────────────────────────────── prodElimIntro
π j (</ V@i // i in [:n] />) -> V@j

E -> E'
─────────────── sumIntro
ι i E -> ι i E'

E -> E'
─────────────────────────────────────────────────────────────────────────────── sumElimL
case E {</ F@i // i in [:n] notex />} -> case E' {</ F@i // i in [:n] notex />}

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sumElimR
case V {</ V'@i // i in [:n] notex />, E, </ F@j // j in [:m] notex />} -> case V {</ V'@i // i in [:n] notex />, E', </ F@j // j in [:m] notex />}

j ∈ [:n]
────────────────────────────────────────────── sumElimIntro
case ι j V {</ V'@i // i in [:n] />} -> V'@j V

namespace OperationalSemantics

@[app_unexpander OperationalSemantics]
def delabOpSem: Lean.PrettyPrinter.Unexpander
  | `($(_) $A $B) =>
    let info := Lean.SourceInfo.none
    let into := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "->") }
    `([ $A $into $B ])
  | _ => throw ()

end OperationalSemantics

end TabularTypes.«F⊗⊕ω»
