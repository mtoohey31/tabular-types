import TabularTypeInterpreter.RuleSets
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace «Type»

attribute [aesop norm (rule_sets := [topen])] Type_open TypeVar_open

end «Type»

end TabularTypeInterpreter.«F⊗⊕ω»