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
def methodDom : ClassEnvironment → List Method
  | empty => []
  | ext Γc (.mk _ _ _ m ..) => m :: Γc.methodDom

end ClassEnvironment

judgement_syntax TC " ≠ " TC' : TypeClass.Ne

judgement TypeClass.Ne := _root_.Ne (α := TypeClass)

judgement_syntax m " ≠ " m' : Method.Ne

judgement Method.Ne := _root_.Ne (α := Method)

judgement_syntax γc " ∈ " Γc : ClassEnvironment.In

judgement ClassEnvironment.In where

─────────── head
γc ∈ Γc, γc

(</ TC'@i a ⇝ A'@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc
TC ≠ TC''
m ≠ m'
───────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── ext {TC}
(</ TC'@i a ⇝ A'@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc, (</ TC'''@i a' ⇝ A'''@i // i in [:n'] notex /> ⇒ TC'' a' : κ') ↦ m' : σ' ⇝ A''

judgement_syntax TC " : " κ " ⇝ " A " ∈ " Γc : ClassEnvironment.TCIn (tex noelab := s!"{TC} \\, \\lottsym\{:} \\, {κ} \\, \\lottsym\{∈} \\, {Γc}")

judgement ClassEnvironment.TCIn := fun TC κ A Γc =>
  ∃ TC' A' n m σ A'', A = [[⊗ {A', </ A''@i // i in [:n] />}]] ∧
    [[(</ TC'@i a ⇝ A''@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A' ∈ Γc]]

judgement_syntax TC " ∉ " "dom" "(" Γc ")" : ClassEnvironment.TCNotInDom

judgement ClassEnvironment.TCNotInDom := fun TC (Γc : ClassEnvironment) => TC ∉ Γc.TCDom

judgement_syntax m " ∉ " "dom" "(" Γc ")" : ClassEnvironment.MethodNotInDom

judgement ClassEnvironment.MethodNotInDom := fun m (Γc : ClassEnvironment) => m ∉ Γc.methodDom

end TabularTypeInterpreter
