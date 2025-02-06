import Lott.DSL.Elab.Bool
import Lott.DSL.Elab.Nat
import TabularTypeInterpreter.Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

instance : Coe TypeVarId «F⊗⊕ω».TypeVarId where coe a := a

instance : Coe TypeVarId «F⊗⊕ω».TypeVar where coe a := .free a

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

def TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

def TermVarNe := Ne (α := TermVarId)

judgement_syntax n " ≠ " n' : NatNe

abbrev NatNe := Ne (α := Nat)

judgement_syntax b : BoolId

abbrev BoolId := id (α := Bool)

end TabularTypeInterpreter
