import Lott.Elab.Bool
import Lott.Elab.Nat
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

instance : Coe TypeVarId «F⊗⊕ω».TypeVarId where coe a := a

instance : Coe TypeVarId «F⊗⊕ω».TypeVar where coe a := .free a

instance : Coe TermVarId «F⊗⊕ω».TermVarId where coe x := x

instance : Coe TermVarId «F⊗⊕ω».TermVar where coe x := .free x

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

def TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

def TermVarNe := Ne (α := TermVarId)

judgement_syntax n " ≠ " n' : NatNe

abbrev NatNe := Ne (α := Nat)

judgement_syntax b : BoolId

abbrev BoolId := id (α := Bool)

end TabularTypeInterpreter
