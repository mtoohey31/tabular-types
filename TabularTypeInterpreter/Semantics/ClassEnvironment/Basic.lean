import Lott.Data.Range
import TabularTypeInterpreter.Syntax.ClassEnvironment

namespace TabularTypeInterpreter

open «F⊗⊕ω»

namespace ClassEnvironment

variable (TC : TypeClass)

def append (Γc : ClassEnvironment) : ClassEnvironment → ClassEnvironment
  | empty => Γc
  | ext Γc' γc => Γc.append Γc' |>.ext γc

def TCDom : ClassEnvironment → List TypeClass
  | empty => []
  | ext Γc (.mk _ TC ..) => TC :: Γc.TCDom

def memberDom : ClassEnvironment → List Member
  | empty => []
  | ext Γc (.mk _ _ _ m ..) => m :: Γc.memberDom

end ClassEnvironment

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
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ext {TC}
(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc, (</ TC'ₛ@i a' ⇝ Aₛ'@i // i in [:n'] /> ⇒ TC' a' : κ') ↦ m' : σ' ⇝ A'

judgement_syntax TC " : " κ " ⇝ " A " ∈ " Γc : ClassEnvironment.TCIn

def ClassEnvironment.TCIn TC κ A Γc :=
  ∃ TCₛ Aₛ n m σ, [[(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc]]

judgement_syntax TC " ∉ " "dom" "(" Γc ")" : ClassEnvironment.TCNotInDom

def ClassEnvironment.TCNotInDom TC (Γc : ClassEnvironment) := TC ∉ Γc.TCDom

judgement_syntax m " ∉ " "dom" "(" Γc ")" : ClassEnvironment.MemberNotInDom

def ClassEnvironment.MemberNotInDom m (Γc : ClassEnvironment) := m ∉ Γc.memberDom

end TabularTypeInterpreter
