import TabularTypeInterpreter.Syntax.Term
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

instance : Coe TypeVarId «F⊗⊕ω».TypeVarId where coe a := a

instance : Coe TypeVarId «F⊗⊕ω».TypeVar where coe a := .free a

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

def TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

def TermVarNe := Ne (α := TermVarId)

end TabularTypeInterpreter
