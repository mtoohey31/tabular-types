import Lott.Data.Range
import Lott.Elab.Nat
import TabularTypeInterpreter.Data.List
import TabularTypeInterpreter.Elab.Permutation
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Term
import TabularTypeInterpreter.Syntax.Basic
import TabularTypeInterpreter.Syntax.Type

namespace TabularTypeInterpreter

termonly
instance : Coe TypeVarId «F⊗⊕ω».TypeVarId where coe a := a

termonly
instance : Coe TypeVarId «F⊗⊕ω».TypeVar where coe a := .free a

termonly
instance : Coe TermVarId «F⊗⊕ω».TermVarId where coe x := x

termonly
instance : Coe TermVarId «F⊗⊕ω».TermVar where coe x := .free x

syntax (name := elabRelatedJudgement) "elab_related " Lott.Judgement : Lott.Judgement

@[macro Lott.judgementEmbed]
private
def elabRelatedJudgementImpl : Lean.Macro := fun stx => do
  let `([[elab_related $j:Lott.Judgement]]) := stx | Lean.Macro.throwUnsupported
  ``([[$j:Lott.Judgement]])

@[lott_tex_elab elabRelatedJudgement]
private
def elabRelatedJudgementTexElab : Lott.TexElab := fun profile ref stx => do
  let `(Lott.Judgement| elab_related $j:Lott.Judgement) := stx | Lean.Elab.throwUnsupportedSyntax
  let jTex ← Lott.texElabSymbolOrJudgement j.raw.getKind profile ref j
  return s!"\\elabrelated\{{jTex}}"

judgement_syntax a " ≠ " a' : TypeVarNe (id a, a')

judgement TypeVarNe := Ne (α := TypeVarId)

judgement_syntax x " ≠ " x' : TermVarNe (id x, x')

judgement TermVarNe := Ne (α := TermVarId)

run_cmd Lott.addNatAlias `k
run_cmd Lott.addNatAlias `l
run_cmd Lott.addNatAlias `o

instance {α β : Type} {γ : (α → β) → Prop } : CoeFun { a : α → β // γ a } (fun _ => α → β) where
  coe := Subtype.val

judgement_syntax p_ " permutes " "[" ":" n "]" : Permutes

judgement Permutes := fun p n => List.Perm p [:n].toList

end TabularTypeInterpreter

judgement_syntax TabularTypeInterpreter.p_ " inverts " TabularTypeInterpreter.p_' " on " "[" ":" n "]" : Std.Range.get!InverseOn
