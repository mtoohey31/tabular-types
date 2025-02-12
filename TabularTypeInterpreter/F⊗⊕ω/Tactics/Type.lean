import TabularTypeInterpreter.RuleSets
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type

namespace TabularTypeInterpreter.«F⊗⊕ω».«Type»

attribute [aesop norm (rule_sets := [topen])] Type_open TypeVar_open
attribute [aesop unsafe simp constructors (rule_sets := [pred])] ParallelReduction MultiParallelReduction

end TabularTypeInterpreter.«F⊗⊕ω».«Type»
