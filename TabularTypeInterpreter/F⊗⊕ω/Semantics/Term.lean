import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Value

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax Δ " ⊢ " E " : " A : Typing

judgement Typing :=

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
Δ ⊢ E [B] : A^^B

⊢ Δ
</ Δ ⊢ E@i : A@i // i in [:n] />
───────────────────────────────────────────────────────── prodIntro
Δ ⊢ (</ E@i // i in [:n] />) : ⊗ {</ A@i // i in [:n] />}

Δ ⊢ E : ⊗ {</ A@i // i in [:n'] />}
n ∈ [0:n']
─────────────────────────────────── prodElim
Δ ⊢ π n E : A@n

n ∈ [0:n']
Δ ⊢ E : A@n
</ Δ ⊢ A@i : * // i in [:n'] />
─────────────────────────────────────── sumIntro
Δ ⊢ ι n E : ⊕ {</ A@i // i in [:n'] />}

Δ ⊢ E : ⊕ {</ A@i // i in [:n] />}
</ Δ ⊢ F@i : A@i → B // i in [:n] />
Δ ⊢ B : *
─────────────────────────────────────── sumElim
Δ ⊢ case E {</ F@i // i in [:n] />} : B

Δ ⊢ E : A
Δ ⊢ A ≡ B
───────── equiv
Δ ⊢ E : B

attribute [app_unexpander Typing] Kinding.delabK

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
(</ V@i // i in [:n] />, E, </ F@j // j in [:m] />) -> (</ V@i // i in [:n] />, E', </ F@j // j in [:m] />)

E -> E'
───────────────────────────────────── prodElim
π n E -> π n E'

n ∈ [0:n']
──────────────────────────────────── prodElimIntro
π n (</ V@i // i in [:n'] />) -> V@n

E -> E'
─────────────── sumIntro
ι n E -> ι n E'

E -> E'
─────────────────────────────────────────────────────────────────── sumElimL
case E {</ F@i // i in [:n] />} -> case E' {</ F@i // i in [:n] />}

E -> E'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── sumElimR
case V {</ V'@i // i in [:n] />, E, </ F@j // j in [:m] />} -> case V {</ V'@i // i in [:n] />, E', </ F@j // j in [:m] />}

n ∈ [0:n']
───────────────────────────────────────────────────── sumElimIntro
case ι n V {</ V'@i // i in [:n'] />} -> V'@n ⦅ι n V⦆

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
