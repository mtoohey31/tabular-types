import Lake
open Lake DSL

require lott from "vendor/lott"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

package «tabular-type-interpreter»

@[default_target]
lean_lib TabularTypeInterpreter
