import Lott.Data.Range
import TabularTypeInterpreter.Syntax.ClassEnvironment

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax TC " ≠ " TC' : TypeClass.Ne

def TypeClass.Ne := _root_.Ne (α := TypeClass)

judgement_syntax m " ≠ " m' : Member.Ne

def Member.Ne := _root_.Ne (α := Member)

judgement_syntax γc " ∈ " Γc : ClassEnvironment.In

judgement ClassEnvironment.In :=

─────────── head
γc ∈ Γc, γc

(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
TC ≠ TC'
m ≠ m'
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ext {TC}
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc, (</ TC'ₛ@i a' ⇝ Aₛ'@i // i in [:m] /> ⇒ TC' a' : κ') ↦ m' : σ' ⇝ A'

end TabularTypeInterpreter
