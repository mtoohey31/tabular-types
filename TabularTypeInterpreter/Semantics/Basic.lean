import Lott.Elab.Bool
import Lott.Elab.Nat
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

termonly
instance : Coe TypeVarId «F⊗⊕ω».TypeVarId where coe a := a

termonly
instance : Coe TypeVarId «F⊗⊕ω».TypeVar where coe a := .free a

termonly
instance : Coe TermVarId «F⊗⊕ω».TermVarId where coe x := x

termonly
instance : Coe TermVarId «F⊗⊕ω».TermVar where coe x := .free x

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

judgement TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

judgement TermVarNe := Ne (α := TermVarId)

judgement_syntax n " ≠ " n' : NatNe

judgement NatNe := Ne (α := Nat)

judgement_syntax b : BoolId

judgement BoolId := id (α := Bool)

end TabularTypeInterpreter
