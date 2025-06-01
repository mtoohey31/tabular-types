import Lott.Data.Range
import TabularTypeInterpreter.Syntax.ClassEnvironment

namespace TabularTypeInterpreter

open «F⊗⊕ω»

namespace ClassEnvironment

variable (TC : TypeClass)

termonly
def append (Γc : ClassEnvironment) : ClassEnvironment → ClassEnvironment
  | empty => Γc
  | ext Γc' γc => Γc.append Γc' |>.ext γc

termonly
def TCDom : ClassEnvironment → List TypeClass
  | empty => []
  | ext Γc (.mk _ TC ..) => TC :: Γc.TCDom

termonly
def memberDom : ClassEnvironment → List Member
  | empty => []
  | ext Γc (.mk _ _ _ m ..) => m :: Γc.memberDom

end ClassEnvironment

judgement_syntax TC " ≠ " TC' : TypeClass.Ne

judgement TypeClass.Ne := _root_.Ne (α := TypeClass)

judgement_syntax m " ≠ " m' : Member.Ne

judgement Member.Ne := _root_.Ne (α := Member)

judgement_syntax γc " ∈ " Γc : ClassEnvironment.In

judgement ClassEnvironment.In where

─────────── head
γc ∈ Γc, γc

(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
TC ≠ TC'
m ≠ m'
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ext {TC}
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc, (</ TC'ₛ@i a' ⇝ Aₛ'@i // i in [:n'] notex /> ⇒ TC' a' : κ') ↦ m' : σ' ⇝ A'

judgement_syntax TC " : " κ " ⇝ " A " ∈ " Γc : ClassEnvironment.TCIn (tex noelab := s!"{TC} \\, \\lottsym\{:} \\, {κ} \\, \\lottsym\{∈} \\, {Γc}")

judgement ClassEnvironment.TCIn := fun TC κ A Γc =>
  ∃ TCₛ Aₛ n m σ A', A = [[⊗ {A', </ Aₛ@i // i in [:n] />}]] ∧
    [[(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A' ∈ Γc]]

judgement_syntax TC " ∉ " "dom" "(" Γc ")" : ClassEnvironment.TCNotInDom

judgement ClassEnvironment.TCNotInDom := fun TC (Γc : ClassEnvironment) => TC ∉ Γc.TCDom

judgement_syntax m " ∉ " "dom" "(" Γc ")" : ClassEnvironment.MemberNotInDom

judgement ClassEnvironment.MemberNotInDom := fun m (Γc : ClassEnvironment) => m ∉ Γc.memberDom

end TabularTypeInterpreter
