import TabularTypes.«F⊗⊕ω».Syntax.Term

namespace TabularTypes.«F⊗⊕ω»

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

judgement TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

judgement TermVarNe := Ne (α := TermVarId)

judgement_syntax n " ∈ " "[" n_start ":" n_stop "]" : NatInRange

judgement NatInRange := fun (n start stop : Nat) => n ∈ [start:stop]

judgement_syntax n " ∈ " "[" ":" n_stop "]" : NatInZeroRange

judgement NatInZeroRange := fun (n stop : Nat) => n ∈ [:stop]

end TabularTypes.«F⊗⊕ω»
