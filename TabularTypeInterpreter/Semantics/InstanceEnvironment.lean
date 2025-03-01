import TabularTypeInterpreter.Semantics.ClassEnvironment.Basic
import TabularTypeInterpreter.Syntax.InstanceEnvironment

namespace TabularTypeInterpreter

judgement_syntax Γc " ⊢ " Γᵢ : InstanceEnvironment.WellFormedness

judgement InstanceEnvironment.WellFormedness :=

─────── empty
Γc ⊢ Γᵢ

-- TODO: ext

end TabularTypeInterpreter
