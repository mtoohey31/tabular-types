import Batteries.Data.List.Basic
import Lott.Data.Range
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

def shift (τ : Monotype) (off := 1) (min := 0) : Monotype := match τ with
  | var n => var <| if min ≤ n then n + off else n
  | lam κ τ' => lam κ <| shift τ' off (min + 1)
  | app ϕ τ' => app (shift ϕ off min) (shift τ' off min)
  | arr τ₀ τ₁ => arr (shift τ₀ off min) (shift τ₁ off min)
  | label s => label s
  | floor ξ => floor <| shift ξ off min
  | comm u => comm u
  | row ξτ's κ? => row (ξτ's.mapMem fun (ξ, τ') _ => (shift ξ off min, shift τ' off min)) κ?
  | prodOrSum Ξ μ => prodOrSum Ξ <| shift μ off min
  | lift ϕ => lift <| shift ϕ off min
  | contain ρ₀ μ ρ₁ => contain (shift ρ₀ off min) (shift μ off min) (shift ρ₁ off min)
  | concat ρ₀ μ ρ₁ ρ₂ =>
    concat (shift ρ₀ off min) (shift μ off min) (shift ρ₁ off min) (shift ρ₂ off min)
  | tc s => tc s
  | all ϕ => all <| shift ϕ off min
  | ind => ind
  | split => split
  | list => list
  | nat => nat
  | str => str

def «open» (τ : Monotype) (τ' : Monotype) (n : Nat := 0) : Monotype := match τ with
  | var m => if m == n then τ' else var m
  | lam κ τ'' => lam κ <| τ''.open τ'.shift (n + 1)
  | app ϕ τ'' => app (ϕ.open τ' n) (τ''.open τ' n)
  | arr τ₀ τ₁ => app (τ₀.open τ' n) (τ₁.open τ' n)
  | label s => label s
  | floor ξ => floor <| ξ.open τ' n
  | comm u => comm u
  | row ξτ''s κ? => row (ξτ''s.mapMem fun (ξ, τ'') _ => (ξ.open τ' n, τ''.open τ' n)) κ?
  | prodOrSum Ξ μ => prodOrSum Ξ <| μ.open τ' n
  | lift ϕ => lift <| ϕ.open τ' n
  | contain ρ₀ μ ρ₁ => contain (ρ₀.open τ' n) (μ.open τ' n) (ρ₁.open τ' n)
  | concat ρ₀ μ ρ₁ ρ₂ => concat (ρ₀.open τ' n) (μ.open τ' n) (ρ₁.open τ' n) (ρ₂.open τ' n)
  | tc s => tc s
  | all ϕ => all <| ϕ.open τ' n
  | ind => ind
  | split => split
  | list => list
  | nat => nat
  | str => str

inductive CommutativityPartialOrdering : Monotype → Monotype → Prop where
  | non : CommutativityPartialOrdering (comm .non) μ
  | comm : CommutativityPartialOrdering μ (comm .comm)

inductive RowEquivalence : Monotype → Monotype → Monotype → Type where
  | refl : RowEquivalence ρ μ ρ
  | trans : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence ρ₁ μ ρ₂ → RowEquivalence ρ₀ μ ρ₂
  | comm : List.Perm ξτs₀ ξτs₁ → RowEquivalence (row ξτs₀ κ?) (comm .non) (row ξτs₁ κ?)
  | liftL : RowEquivalence ((lift ϕ).app (row ξτs κ?)) μ
      (row (ξτs.map fun (ξ, τ) => (ξ, ϕ.app τ)) κ?)
  | liftR : RowEquivalence (row (ξτs.map fun (ξ, τ) => (ξ, ϕ.app τ)) κ?) μ
      ((lift ϕ).app (row ξτs κ?))

namespace RowEquivalence

def symm : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence ρ₁ μ ρ₀
  | refl => refl
  | trans ρ₀₁re ρ₁₂re => trans ρ₁₂re.symm ρ₀₁re.symm
  | comm perm => comm perm.symm
  | liftL => liftR
  | liftR => liftL

def prodElab : RowEquivalence ρ₀ μ ρ₁ → Term
  | refl | liftL | liftR => .id
  | trans ρ₀₁re ρ₁₂re => .lam <| ρ₁₂re.prodElab.shift.app <| ρ₀₁re.prodElab.shift.app <| .var 0
  | comm _ (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) =>
    .lam <| .prodIntro <| ξτs₁.map fun (ξ₁, _) => .prodElim (ξτs₀.findIdx (·.fst == ξ₁)) <| .var 0

def sumElab : RowEquivalence ρ₀ μ ρ₁ → Term
  | refl | liftL | liftR => .id
  | trans ρ₀₁re ρ₁₂re => .lam <| ρ₁₂re.sumElab.shift.app <| ρ₀₁re.sumElab.shift.app <| .var 0
  | comm _ (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) => .lam <| .sumElim (.var 0) <| ξτs₀.map fun (ξ₀, _) =>
      .lam <| .sumIntro (ξτs₁.findIdx (·.fst == ξ₀)) <| .var 0

end RowEquivalence

opaque ConstraintSolution : Monotype → Type

opaque ConstraintSolution.elab : ConstraintSolution τ → Term

opaque ConstraintSolution.local : ConstraintSolution τ := sorry

end Monotype

open Monotype

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

def «open» (γ : QualifiedType) (τ : Monotype) (n : Nat := 0) : QualifiedType := match γ with
  | .mono τ' => τ'.open τ n
  | .qual ψ γ' => γ'.open τ n |>.qual <| ψ.open τ n

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

def «open» (σ : TypeScheme) (τ : Monotype) (n : Nat := 0) : TypeScheme := match σ with
  | .qual γ => γ.open τ n
  | .quant κ σ' => σ'.open τ (n + 1) |>.quant κ

inductive Subtyping : TypeScheme → TypeScheme → Type where
  | refl : Subtyping σ σ
  | trans : Subtyping σ₀ σ₁ → Subtyping σ₁ σ₂ → Subtyping σ₀ σ₂
  | arr {τ₀ τ₁ τ₂ τ₃ : Monotype} : Subtyping τ₂ τ₀ → Subtyping τ₁ τ₃ →
    Subtyping (arr τ₀ τ₁) (arr τ₂ τ₃)
  | qual {ψ₀ ψ₁ : Monotype} {γ₀ γ₁ : QualifiedType} : Subtyping ψ₁ ψ₀ → Subtyping γ₀ γ₁ →
    Subtyping (γ₀.qual ψ₀) (γ₁.qual ψ₁)
  | scheme : Subtyping σ₀ σ₁ → Subtyping (quant κ σ₀) (quant κ σ₁)
  | prodOrSum {τ₀s τ₁s : List Monotype} :
    (∀ τ₀₁ ∈ List.zip τ₀s τ₁s, let (τ₀, τ₁) := τ₀₁; Subtyping τ₀ τ₁) →
    Subtyping ((prodOrSum Ξ μ).app (row (List.zip ξs τ₀s) κ?))
      ((prodOrSum Ξ μ).app (row (List.zip ξs τ₁s) κ?))
  | prodOrSumRow : RowEquivalence ρ₀ μ ρ₁ →
    Subtyping ((prodOrSum Ξ μ).app ρ₀) ((prodOrSum Ξ μ).app ρ₁)
  | decay : CommutativityPartialOrdering μ₀ μ₁ →
    Subtyping ((prodOrSum Ξ μ₀).app ρ) ((prodOrSum Ξ μ₁).app ρ)
  | never : Subtyping ((prodOrSum .sum (comm .comm)).app (.row [] (some star))) σ
  | contain : RowEquivalence ρ₀ μ ρ₂ → RowEquivalence ρ₁ μ ρ₃ →
    Subtyping (contain ρ₀ μ ρ₁) (contain ρ₂ μ ρ₃)
  | concat : RowEquivalence ρ₀ μ ρ₃ → RowEquivalence ρ₁ μ ρ₄ → RowEquivalence ρ₂ μ ρ₅ →
    Subtyping (concat ρ₀ μ ρ₁ ρ₂) (concat ρ₃ μ ρ₄ ρ₅)
  | tc {supers : List String} : (∀ s ∈ supers, Subtyping ((tc s).app τ₀) ((tc s).app τ₁)) →
    Subtyping («open» σ τ₀) («open» σ τ₁) → Subtyping ((tc s).app τ₀) ((tc s).app τ₁)
  | allRow : RowEquivalence ρ₀ (comm .comm) ρ₁ → Subtyping ((all ϕ).app ρ₀) ((all ϕ).app ρ₁)
  | split : Subtyping (concat ((lift ϕ).app ρ₀) μ ρ₁ ρ₂) (concat ((lift ϕ).app ρ₃) μ ρ₄ ρ₅) →
    Subtyping ((((split.app ϕ).app ρ₀).app ρ₁).app ρ₂) ((((split.app ϕ).app ρ₃).app ρ₄).app ρ₅)

def Subtyping.elab : Subtyping σ₀ σ₁ → Term
  | refl
  | decay _ => .id
  | trans σ₀₁'st σ₁'₂st => .lam <| σ₁'₂st.elab.shift.app <| σ₀₁'st.elab.shift.app <| .var 0
  | arr st st'
  | qual st st' => .lam <| .lam <| st'.elab.shift 2 |>.app <| .app (.var 1) <| st.elab.shift 2 |>.app <| .var 0
  | scheme σ₀₁'st => σ₀₁'st.elab
  | prodOrSum τ₀₁sst (Ξ := Ξ) (τ₀s := τ₀s) (τ₁s := τ₁s) => match Ξ with
    | .prod => .lam <| .prodIntro <| τ₀s.zip τ₁s |>.mapMemIdx fun i _ mem =>
        τ₀₁sst _ mem |>.elab.shift.app <| .prodElim i <| .var 0
    | .sum => .lam <| .sumElim (.var 0) <| τ₀s.zip τ₁s |>.mapMemIdx fun i _ mem =>
        .lam <| .sumIntro i <| τ₀₁sst _ mem |>.elab.shift 2 |>.app <| .var 0
  | prodOrSumRow ρ₀₁re (Ξ := Ξ) => match Ξ with | .prod => ρ₀₁re.prodElab | .sum => ρ₀₁re.sumElab
  | never => .lam <| .sumElim (.var 0) []
  | contain ρ₀₂re ρ₁₃re => .lam <| contain.elab ρ₀₂re ρ₁₃re
  | concat ρ₀₃re ρ₁₄re ρ₂₅re => .lam <| .prodIntro [
      .lam <| .lam <| ρ₂₅re.prodElab.shift 3 |>.app <| Term.app (.var 2) (ρ₀₃re.symm.prodElab.shift 3 |>.app (.var 1))
        |>.app (ρ₁₄re.symm.prodElab.shift 3 |>.app (.var 0)),
      .lam <| .lam <| .lam <| (Term.var 3) |>.app (.lam (.app (.var 3) (ρ₀₃re.sumElab.shift 5 |>.app (.var 0))))
        |>.app (.lam (.app (.var 2) (ρ₁₄re.sumElab.shift 5 |>.app (.var 0)))) |>.app <|
        ρ₂₅re.symm.sumElab.shift 4 |>.app (.var 0),
      contain.elab ρ₀₃re ρ₂₅re,
      contain.elab ρ₁₄re ρ₂₅re
    ]
  | tc superst memberst (supers := supers) =>
    .lam <| .prodIntro <|
      (memberst.elab.shift.app (.prodElim 0 (.var 0))) :: supers.mapMemIdx fun i _ mem =>
        superst _ mem |>.elab.shift.app <| .prodElim (i + 1) <| .var 0
  | allRow ρ₀₁re => ρ₀₁re.prodElab
  | split concatst => concatst.elab
where
  contain.elab {μ ρ₀ ρ₁ ρ₂ ρ₃} (ρ₀₂re : RowEquivalence ρ₀ μ ρ₂) (ρ₁₃re : RowEquivalence ρ₁ μ ρ₃) :=
    Term.prodIntro [
      .lam <| ρ₀₂re.prodElab.shift 2 |>.app <| .app (.var 1) <| ρ₁₃re.symm.prodElab.shift 2 |>.app <| .var 0,
      .lam <| ρ₁₃re.sumElab.shift 2 |>.app <| .app (.var 1) <| ρ₀₂re.symm.sumElab.shift 2 |>.app <| .var 0
    ]

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

-- Existence of this Typing term doesn't actually prove the Term has this type; this is only used to
-- guide elaboration, so it is up to the function producing this to ensure it is constructed
-- correctly, since mistakes will not necessarily be caught by the type checker.
inductive Typing : Term → TypeScheme → Type where
  | var : Typing (.var n) σ
  | lam {τ₁ : Monotype} : Typing M τ₁ → Typing M.lam (arr τ₀ τ₁)
  | app {ϕ : Monotype} : Typing M (ϕ.arr τ) → Typing N ϕ → Typing (M.app N) τ
  | qualI {γ : QualifiedType} : (ConstraintSolution ψ → Typing M γ) → Typing M (γ.qual ψ)
  | qualE {γ : QualifiedType} : ConstraintSolution ψ → (Typing M (γ.qual ψ)) → Typing M γ
  | schemeI : Typing M σ → Typing M (quant κ σ)
  | schemeE : Typing M (quant κ σ) → Typing M (σ.open τ)
  | let : Typing M σ₀ → Typing N σ₁ → Typing (M.let σ₀ N) σ₁
  | annot : Typing M σ → Typing (M.annot σ) σ
  | label : Typing (label s) (floor (.label s))
  | prod : (∀ MNξτ ∈ MNs.zip ξτs, let ((_, N), _, τ) := MNξτ; Typing N τ) →
    Typing (prod MNs) (row ξτs κ?)
  | sum {τ : Monotype} : Typing N τ →
    Typing (sum M N) ((prodOrSum .sum (comm .non)).app (row [(ξ, τ)] none))
  | unlabel : Typing M ((prodOrSum Ξ μ).app (row [(ξ, τ)] none)) → Typing (unlabel M N) τ
  | prj : Typing M ((prodOrSum .prod μ).app ρ₀) → ConstraintSolution (contain ρ₁ μ ρ₀) →
    Typing (prj M) ((prodOrSum .prod μ).app ρ₁)
  | concat : Typing M ((prodOrSum .prod μ).app ρ₀) → Typing N ((prodOrSum .prod μ).app ρ₁) →
    ConstraintSolution (.concat ρ₀ μ ρ₁ ρ₂) → Typing (M.concat N) ((prodOrSum .prod μ).app ρ₂)
  | inj : Typing M ((prodOrSum .sum μ).app ρ₀) → ConstraintSolution (contain ρ₀ μ ρ₁) →
    Typing (prj M) ((prodOrSum .sum μ).app ρ₁)
  | elim : Typing M (((prodOrSum .prod μ).app ρ₀).arr τ) →
    Typing N (((prodOrSum .prod μ).app ρ₁).arr τ) → ConstraintSolution (.concat ρ₀ μ ρ₁ ρ₂) →
    Typing (M.elim N) (((prodOrSum .prod μ).app ρ₂).arr τ)
  | sub : Typing M σ₀ → Subtyping σ₀ σ₁ → Typing M σ₁
  | member : ConstraintSolution ((tc s).app τ) → Typing (member m) σ
  | order : Typing M ((prodOrSum Ξ (comm .comm)).app ρ) →
    Typing (M.order ρ) ((prodOrSum Ξ (comm .non)).app ρ)
  | ind : Typing M (quant .label (quant κ (quant κ.row (quant κ.row (quant κ.row
      (qual (.concat (.var 2) (comm .non) (row [(.var 4, .var 3)] none) (.var 1))
        (qual (.concat (.var 1) (comm .non) (.var 0) ρ)
          ((floor (.var 4)).arr ((ϕ.app (.var 2)).arr (ϕ.app (.var 1))))))))))) →
    Typing N (ϕ.app (.row [] (some κ))) → ConstraintSolution (Monotype.ind.app ρ) →
    Typing (ind ϕ ρ M N) (ϕ.app ρ)
  | splitₚ : Typing M ((prodOrSum .prod (comm .comm)).app ρ₂) →
    ConstraintSolution ((((split.app ϕ).app ρ₀).app ρ₁).app ρ₂) →
    Typing (M.splitₚ ϕ) ((prodOrSum .prod (comm .non)).app
      (row [
        (.label "match", (prodOrSum .prod (comm .comm)).app ((lift ϕ).app ρ₀)),
        (.label "rest", (prodOrSum .prod (comm .comm)).app ρ₁)
      ] none))
  | splitₛ : Typing M (((prodOrSum .sum (comm .comm)).app ((lift ϕ).app ρ₀)).arr τ) →
    Typing N (((prodOrSum .sum (comm .comm)).app ρ₁).arr τ) →
    ConstraintSolution ((((split.app ϕ).app ρ₀).app ρ₁).app ρ₂) →
    Typing (M.splitₛ ϕ N) (((prodOrSum .sum (comm .comm)).app ρ₂).arr τ)
  | nil : Typing nil (list.app τ)
  | cons {τ : Monotype} : Typing M τ → Typing N (list.app τ) → Typing (cons M N) (list.app τ)
  | fold : Typing fold (quant star (quant star (qual (mono (arr
      (arr (.var 1) (arr (.var 0) (.var 1))) (arr (.var 1) ((list.app (.var 0)).arr (.var 1))))))))
  | nat : Typing (nat n) Monotype.nat
  | op : Typing M Monotype.nat → Typing N Monotype.nat → Typing (op o M N) Monotype.nat
  | range : Typing range (Monotype.nat.arr (list.app .nat))
  | str : Typing (str s) Monotype.str

-- TODO: Figure out how to shift local constraint solutions used under lambdas.
def Typing.elab : Typing M σ → «λπι».Term
  | var (n := n) => .var n
  | lam M'ty => M'ty.elab.lam
  | app M'ty Nty => M'ty.elab.app Nty.elab
  | qualI Mty'_of_so => Mty'_of_so .local |>.elab.lam
  | qualE ψso Mty' => Mty'.elab.app ψso.elab
  | schemeI Mty' => Mty'.elab
  | schemeE Mty' => Mty'.elab
  | .let M'ty Nty => Nty.elab.lam.app M'ty.elab
  | annot M'ty => M'ty.elab
  | label => .prodIntro []
  | prod Nsty (MNs := MNs) (ξτs := ξτs) => .prodIntro <| MNs.zip ξτs |>.mapMem (Nsty · · |>.elab)
  | sum Nty => Nty.elab.sumIntro 0
  | unlabel M'ty (Ξ := Ξ) => match Ξ with
    | .prod => M'ty.elab.prodElim 0
    | .sum => M'ty.elab.sumElim [.id]
  | prj M'ty containso => containso.elab.prodElim 0 |>.app M'ty.elab
  | concat M'ty Nty concatso => concatso.elab.prodElim 0 |>.app M'ty.elab |>.app Nty.elab
  | inj M'ty containso => containso.elab.prodElim 1 |>.app M'ty.elab
  | elim M'ty Nty concatso => concatso.elab.prodElim 1 |>.app M'ty.elab |>.app Nty.elab
  | sub Mty' σ₀st => σ₀st.elab.app Mty'.elab
  | member TCτso => TCτso.elab.prodElim 0
  | order M'ty => M'ty.elab
  | ind M'ty Nty indso => indso.elab |>.app M'ty.elab |>.app Nty.elab
  | splitₚ M'ty splitso =>
    let E := M'ty.elab
    let F := splitso.elab
    .prodIntro [F.prodElim 2 |>.prodElim 0 |>.app E, F.prodElim 3 |>.prodElim 0 |>.app E]
  | splitₛ M'ty Nty splitso => splitso.elab |>.prodElim 1 |>.app M'ty.elab |>.app Nty.elab
  | nil => .nil
  | cons M'ty Nty => .cons M'ty.elab Nty.elab
  | fold => .fold
  | nat (n := n) => .nat n
  | op M'ty Nty (o := o) => .op o M'ty.elab Nty.elab
  | range => .range
  | str (s := s) => .str s

end Term

namespace «λπι»

def Value.delab (V : Value) (σ : Interpreter.TypeScheme) : Option Interpreter.Term := do
  let .qual (.mono τ) := σ | none
  let ⟨E, EIs⟩ := V
  match E with
  | .lam E' =>
    if E'Is : Is E' then
      let .arr _ τ₁ := τ | none
      let M ← delab ⟨E', E'Is⟩ τ₁
      return M.lam
    none
  | .app E' F => match E' with
    | .fold =>
      let .arr τₐ (.arr (.app .list τₑ) _) := τ | none
      let FIs := match EIs with | .fold₁ h => h
      let M ← delab ⟨F, FIs⟩ <| τₐ.arr <| τₑ.arr τₐ
      some <| .app .fold M
    | .app .fold _ => none -- Can't determine accumulator type.
  | .prodIntro Es =>
    let .app (.prodOrSum .prod _) (.row ξτ's _) := τ | none
    let EsIs := match EIs with | .prodIntro h => h
    let true := Es.length == ξτ's.length | none
    let V's : List { V' : Value // V'.val ∈ Es } := Es.mapMem fun E mem => ⟨⟨E, EsIs _ mem⟩, mem⟩
    let MNs ← V's.zip ξτ's |>.mapM fun
      | (⟨V', _⟩, .label s, τ') => do
        let N ← V'.delab τ'
        return (TabularTypeInterpreter.Interpreter.Term.label s, N)
      | _ => none
    return .prod MNs
  | .sumIntro n E' => do
    let .app (.prodOrSum .sum _) (.row ξτ's _) := τ | none
    let E'Is := match EIs with | .sumIntro h => h
    let (.label s, τ') ← ξτ's.get? n | none
    let N ← delab ⟨E', E'Is⟩ τ'
    return .sum (.label s) N
  | .nil => some .nil
  | .cons E' F => do
    let .app .list τ' := τ | none
    let ⟨E'Is, FIs⟩ : _ ∧ _ := match EIs with
      | .cons EIs FIs => ⟨EIs, FIs⟩
    let M ← delab ⟨E', E'Is⟩ τ'
    let N ← delab ⟨F, FIs⟩ <| .qual <| .mono <| .app .list τ'
    return M.cons N
  | .fold => some <| .fold
  | .nat n => some <| .nat n
  | .range => some <| .range
  | .str s => some <| .str s
termination_by sizeOf V.val

end «λπι»

end Interpreter

end TabularTypeInterpreter
