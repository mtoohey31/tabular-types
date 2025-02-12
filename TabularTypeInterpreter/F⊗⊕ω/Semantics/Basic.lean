import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

def TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

def TermVarNe := Ne (α := TermVarId)

judgement_syntax n " ∈ " "[" n_start ":" n_stop "]" : NatInRange

def NatInRange (n start stop : Nat) := n ∈ [start:stop]

end TabularTypeInterpreter.«F⊗⊕ω»
