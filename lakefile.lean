import Lake
open Lake DSL

require lott from "vendor/lott"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"

package «tabular-types» where
  moreGlobalServerArgs := #[s!"-Dweak.lott.tex.output.dir={__dir__}/tex", "-DmaxHeartbeats=4000000"]

@[default_target]
lean_lib TabularTypes where
  leanOptions := #[
    ⟨`weak.lott.tex.locallyNameless, false⟩,
    ⟨`weak.lott.tex.output.sourceRelative, false⟩
  ] ++ if get_config? noterm |>.isSome then #[⟨`weak.lott.term, false⟩] else #[]
  weakLeanArgs := #[s!"-Dweak.lott.tex.output.dir={__dir__}/tex"]
