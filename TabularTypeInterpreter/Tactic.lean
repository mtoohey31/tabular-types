import Lean.Elab
import TabularTypeInterpreter.List
import Mathlib.Tactic

namespace TabularTypeInterpreter.Tactic

open Lean Meta MonadLCtx Elab Term in
def genI (goal: MVarId): MetaM (List Lean.Term) :=
  goal.withContext do
    -- check if goal is of form `∃?: List ?varIdTyName, _`
    let (.app (.app (.const ``Exists _) (.app (.const ``List _) (.const varIdTyName _))) _) := (<- goal.getType)
      | throwTacticEx `genI goal "goal is not of the form `∃?: List ?, _`"
    -- find all hypotheses of the form `I: List ?varIdTyName`
    let names := (<- getLCtx).foldl (fun (acc: List Name) decl => do
      if decl.isImplementationDetail then acc else
      let (.app (.const ``List _) (.const varIdTyName' _)) := decl.type | acc
      if varIdTyName' != varIdTyName then acc else
      decl.userName :: acc
    ) []
    -- generate all possible `I`s by taking all combinations of the hypotheses and connecting them with `++`
    names.combinations
      |> (List.foldlM (fun acc names => do
        return (<- names.foldlM (fun acc name => `($acc ++ $(mkIdent name))) (<- `([]))) :: acc) [])
      |> TermElabM.run'

open Lean Aesop RuleTac in
def guessI : RuleTac := fun input => (do
  let possibleI <- genI input.goal
  let apps <- possibleI.foldlM (fun acc I => do
    let singleTac := ofTacticSyntax (fun _ => `(tactic| exists $I))
    let { applications := apps } := (← withoutModifyingState $ singleTac input)
    return acc ++ apps
  ) Array.empty
  return { applications := apps }
)

end TabularTypeInterpreter.Tactic
