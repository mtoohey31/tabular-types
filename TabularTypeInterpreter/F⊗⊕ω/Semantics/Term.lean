import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Value

namespace TabularTypeInterpreter.«F⊗⊕ω»

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
───────────────────────────────────────────────────────────────────── prodIntro
Δ ⊢ (</ E@i // i in [:n] notex />) : ⊗ {</ A@i // i in [:n] notex />}

Δ ⊢ E : ⊗ {</ A@i // i in [:n] />}
i ∈ [:n]
────────────────────────────────── prodElim
Δ ⊢ π i E : A@i

j ∈ [:n]
Δ ⊢ E : A@j
</ Δ ⊢ A@i : * // i in [:n] />
────────────────────────────────────── sumIntro
Δ ⊢ ι j E : ⊕ {</ A@i // i in [:n] />}

Δ ⊢ E : ⊕ {</ A@i // i in [:n] notex />}
</ Δ ⊢ F@i : A@i → B // i in [:n] notex />
Δ ⊢ B : *
───────────────────────────────────────────── sumElim
Δ ⊢ case E {</ F@i // i in [:n] notex />} : B

Δ ⊢ E : A
Δ ⊢ A ≡ B
───────── equiv
Δ ⊢ E : B

termonly
attribute [app_unexpander Typing] Kinding.delabK

judgement_syntax E " -> " F : OperationalSemantics (tex := s!"{E} \\, \\lottsym\{→} \\, {F}")

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
π j (</ V@i // i in [:n] />) -> V@n

E -> E'
─────────────── sumIntro
ι i E -> ι i E'

E -> E'
─────────────────────────────────────────────────────────────────────────────── sumElimL
case E {</ F@i // i in [:n] notex />} -> case E' {</ F@i // i in [:n] notex />}

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sumElimR
case V {</ V'@i // i in [:n] notex />, E, </ F@j // j in [:m] notex />} -> case V {</ V'@i // i in [:n] notex />, E', </ F@j // j in [:m] notex />}

j ∈ [0:n]
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

end TabularTypeInterpreter.«F⊗⊕ω»
