import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Kind

namespace TabularTypeInterpreter.«F⊗⊕ω»

@[simp]
theorem Kind.sizeOf_pos (K : Kind) : 0 < sizeOf K := by
  induction K <;> simp_arith

end TabularTypeInterpreter.«F⊗⊕ω»
