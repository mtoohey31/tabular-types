import Batteries.Data.List.Basic
import Lott.Tactic.Termination
import Mathlib.Data.String.Defs
import TabularTypeInterpreter.Interpreter.«λπι»

namespace TabularTypeInterpreter

namespace Interpreter

open «λπι»

inductive Kind where
  | star
  | arr : Kind → Kind → Kind
  | label
  | comm
  | row : Kind → Kind
  | constr
deriving BEq

namespace Kind

def toString : Kind → String
  | .star => "*"
  | .arr κ₀ κ₁ => κ₀.toString ++ " ↦ " ++ κ₁.toString
  | .label => "L"
  | .comm => "U"
  | .row κ => "R " ++ κ.toString
  | .constr => "C"

instance : ToString Kind where
  toString := toString

end Kind

open Kind

inductive Comm where
  | comm
  | non
deriving BEq

instance : ToString Comm where
  toString
    | .comm => "C"
    | .non => "N"

inductive ProdOrSum where
  | prod
  | sum
deriving BEq

instance : ToString ProdOrSum where
  toString
    | .prod => "Π"
    | .sum => "Σ"

inductive Monotype where
  | var : Nat → Monotype
  | lam : Kind → Monotype → Monotype
  | app : Monotype → Monotype → Monotype
  | arr : Monotype → Monotype → Monotype
  | label : String → Monotype
  | floor : Monotype → Monotype
  | comm : Comm → Monotype
  | row : List (Monotype × Monotype) → Option Kind → Monotype
  | prodOrSum : ProdOrSum → Monotype → Monotype
  | lift : Monotype → Monotype
  | contain (ρ₀ μ ρ₁ : Monotype)
  | concat (ρ₀ μ ρ₁ ρ₂ : Monotype)
  | tc : String → Monotype
  | all : Monotype → Monotype
  | ind
  | split
  | list
  | nat
  | str
deriving BEq

namespace Monotype

def toString : Monotype → String
  | var n => s!"{n}"
  | lam κ τ => s!"(λ {κ}. {τ.toString})"
  | app ϕ τ => s!"{ϕ.toString} {τ.toString}"
  | arr τ₀ τ₁ => s!"{τ₀.toString} → {τ₁.toString}"
  | label s => s
  | floor ξ => s!"⌊{ξ.toString}⌋"
  | comm u => s!"{u}"
  | row ξτs κ? =>
    let κString := match κ? with
      | some κ => s!" : {κ}"
      | none => ""
    let ξτsString := ξτs.mapMem fun (ξ, τ) _ => s!"{ξ.toString} ▹ {τ.toString}"
    s!"⟨{ξτsString}{κString}⟩"
  | prodOrSum Ξ μ => s!"{Ξ}({μ.toString})"
  | lift ϕ => s!"Lift {ϕ.toString}"
  | contain ρ₀ μ ρ₁ => s!"{ρ₀.toString} ≲({μ.toString}) {ρ₁.toString}"
  | concat ρ₀ μ ρ₁ ρ₂ => s!"{ρ₀.toString} ⊙({μ.toString}) {ρ₁.toString} ~ {ρ₂.toString}"
  | tc s => s
  | all ϕ => s!"All {ϕ.toString}"
  | ind => "Ind"
  | split => "Split"
  | list => "List"
  | nat => "Nat"
  | str => "String"

instance : ToString Monotype where
  toString := toString

end Monotype


inductive QualifiedType where
  | mono : Monotype → QualifiedType
  | qual : Monotype → QualifiedType → QualifiedType

namespace QualifiedType

instance : Coe Monotype QualifiedType where
  coe := .mono

def toString : QualifiedType → String
  | .mono τ => τ.toString
  | .qual ψ γ => s!"{ψ} ⇒ {γ.toString}"

instance : ToString QualifiedType where
  toString := QualifiedType.toString

end QualifiedType

open QualifiedType

inductive TypeScheme where
  | qual : QualifiedType → TypeScheme
  | quant : Kind → TypeScheme → TypeScheme

namespace TypeScheme

instance : Coe QualifiedType TypeScheme where
  coe := .qual

def toString : TypeScheme → String
  | .qual γ => γ.toString
  | .quant κ σ => s!"∀ {κ}. {σ.toString}"

instance : ToString TypeScheme where
  toString := toString

end TypeScheme

open TypeScheme

inductive Term where
  | var : Nat → Term
  | member : String → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | let : TypeScheme → Term → Term → Term
  | annot : Term → TypeScheme → Term
  | label : String → Term
  | prod : List (Term × Term) → Term
  | sum : Term → Term → Term
  | unlabel : Term → Term → Term
  | prj : Term → Term
  | concat : Term → Term → Term
  | inj : Term → Term
  | elim : Term → Term → Term
  | order : Monotype → Term → Term
  | ind : Monotype → Monotype → Term → Term → Term
  | splitₚ : Monotype → Term → Term
  | splitₛ : Monotype → Term → Term → Term
  | nil : Term
  | cons : Term → Term → Term
  | fold
  | nat : Nat → Term
  | op : Op → Term → Term → Term
  | range
  | str : String → Term

namespace Term

private
def termsFromList (M : Term) : List Term × Option Term := match M with
  | cons M' N =>
    let (Ms, N'?) := termsFromList N
    (M' :: Ms, N'?)
  | nil => ([], none)
  | _ => ([], M)

mutual

partial
def tableFromTerms (Ms : List Term) : Option String := do
  let .prod MNs :: _ := Ms | none
  let header ← MNs.mapM fun | (.label s, _) => some s | _ => none
  let entries ← Ms.mapM fun
    | .prod MNs' => some <| MNs'.map fun (_, N) => N.toString true
    | _ => none
  let maxWidths := header.mapIdx fun i h => Option.get! <| List.max? <|
    (h :: entries.map (·.get! i)).flatMap (String.splitOn (sep := "\n")) |>.map String.length
  return String.join <| List.intersperse "\n" <|
    String.join (List.intersperse " │ " (header.mapIdx fun i h => h.rightpad <| maxWidths.get! i)) ::
    String.join (List.intersperse "┼" (maxWidths.map fun w => String.replicate (w + 2) '─')) ::
    List.flatten (entries.map fun row =>
      let entryLines := row.map (·.splitOn (sep := "\n"))
      let maxHeight := Option.getD (dflt := 0) <| List.max? <| entryLines.map List.length
      entryLines.map (fun lines => lines ++ List.replicate (maxHeight - lines.length) "")
        |>.transpose.map fun lines => String.join <| List.intersperse " │ "
          (lines.mapIdx (fun i l => l.rightpad <| maxWidths.get! i)))

partial
def toString (M : Term) (table := false) : String := match M with
  | var n => s!"v{n}"
  | member s => s
  | lam M' => s!"(λ. {M'.toString})"
  | app M' N => s!"{M'.toString} {N.toString}"
  | «let» σ M' N => s!"let {σ} = {M'.toString} in {N.toString}"
  | annot M' σ => s!"({M'.toString} : {σ})"
  | label s => s
  | prod M'Ns =>
    s!"\{{String.join <| List.intersperse ", " <|
            M'Ns.map fun (M', N) => s!"{M'.toString} ▹ {N.toString}"}}"
  | sum M' N => s!"[{M'.toString} ▹ {N.toString}]"
  | unlabel M' N => s!"{M'.toString}/{N.toString}"
  | prj M' => s!"prj {M'.toString}"
  | concat M' N => s!"{M'.toString} ++ {N.toString}"
  | inj M' => s!"inj {M'.toString}"
  | elim M' N => s!"{M'.toString} ▿ {N.toString}"
  | order ρ M' => s!"order {ρ} {M'.toString}"
  | ind ϕ ρ M' N => s!"ind {ϕ} {ρ} {M'.toString} {N.toString}"
  | splitₚ ϕ M' => s!"splitₚ {ϕ} {M'.toString}"
  | splitₛ ϕ M' N => s!"splitₛ {ϕ} {M'.toString} {N.toString}"
  | nil => "[]"
  | cons .. => Id.run do
    let (M's, N?) := termsFromList M
    if let some N := N? then
      return String.join (M's.map (s!"{·.toString} :: ")) ++ N.toString
    if table then
      if let some table := tableFromTerms M's then
        return table
    return s!"[{M's.map toString}]"
  | fold => "fold"
  | nat n => s!"{n}"
  | op o M' N => s!"{M'.toString} {o} {N.toString}"
  | range => "range"
  | str s => s.quote

end

instance : ToString Term where
  toString := toString

end Term

end Interpreter

end TabularTypeInterpreter
