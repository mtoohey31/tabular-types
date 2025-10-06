import TabularTypes.«F⊗⊕ω».Syntax.Kind

namespace TabularTypes.«F⊗⊕ω»

@[simp]
theorem Kind.sizeOf_pos (K : Kind) : 0 < sizeOf K := by
  induction K <;> simp_arith

end TabularTypes.«F⊗⊕ω»
