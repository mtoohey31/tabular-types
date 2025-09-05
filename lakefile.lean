import Lake
open Lake DSL

-- TODO: Use lib leanOptions for everything instead of args once string escaping is fixed.

require lott from "vendor/lott"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"
require parser from "vendor/lean4-parser"
require Thesis from git "https://github.com/mtoohey31/svkampen-msc-thesis" @ "main"

package «tabular-type-interpreter» where
  moreGlobalServerArgs := #[
    s!"-Dweak.lott.tex.output.dir={__dir__}/tex",
    s!"-Dweak.λ⇒ρi.corePath={__dir__}/examples/core",
    "-DmaxHeartbeats=4000000"
  ]

-- TODO: Figure out how to enable makeDeps without breaking build.

@[default_target]
lean_lib TabularTypeInterpreter where
  leanOptions := #[
    ⟨`weak.lott.tex.locallyNameless, false⟩,
    ⟨`weak.lott.tex.output.sourceRelative, false⟩
  ] ++ if get_config? noterm |>.isSome then #[⟨`weak.lott.term, false⟩] else #[]
  weakLeanArgs := #[s!"-Dweak.lott.tex.output.dir={__dir__}/tex"]

lean_exe «λ⇒ρi» where
  root := `Main
  moreLeanArgs := #[s!"-Dweak.λ⇒ρi.corePath={__dir__}/examples/core"]
