import Lake
open Lake DSL

-- TODO: Use lib leanOptions for everything instead of args once string escaping is fixed.

require lott from "vendor/lott"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"
require Parser from git "https://github.com/fgdorais/lean4-parser" @ "053703dce47f6cbe537635e5bf3e54c59bcccc78"

package «tabular-type-interpreter» where
  moreGlobalServerArgs := #[s!"-Dweak.lott.tex.output.dir={__dir__}/tex"]

-- TODO: Figure out how to enable makeDeps without breaking build.

@[default_target]
lean_lib TabularTypeInterpreter where
  leanOptions := #[
    ⟨`weak.lott.tex.locallyNameless, false⟩,
    ⟨`weak.lott.tex.output.sourceRelative, false⟩
  ] ++ if get_config? noterm |>.isSome then #[⟨`weak.lott.term, false⟩] else #[]
  weakLeanArgs := #[s!"-Dweak.lott.tex.output.dir={__dir__}/tex"]

lean_exe tti where
  root := `Main
