import Lott.Elab

namespace TabularTypeInterpreter

open Lean
open Lean.Elab
open Lean.Parser
open Lott

declare_syntax_cat Lott.Symbol.Permutation

run_cmd setEnv <| aliasExt.addEntry (← getEnv) { canon := `Permutation, alias := `TabularTypeInterpreter.p_, tex? := "p" }

@[Lott.Symbol.Permutation_parser]
private
def permutation.p_parser : Parser := leadingNode `Lott.Symbol.Permutation maxPrec <| identPrefix "p"

@[macro Lott.symbolEmbed]
private
def permutationImpl : Macro := fun stx => do
  let .node _ `Lott.symbolEmbed #[
    .atom _ "[[",
    .node _ `Lott.Symbol.Permutation #[p@(.ident ..)],
    .atom _ "]]"
  ] := stx | Macro.throwUnsupported
  return p

end TabularTypeInterpreter
