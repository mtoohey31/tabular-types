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
deriving Inhabited, BEq

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
deriving Inhabited, BEq

instance : ToString Comm where
  toString
    | .comm => "C"
    | .non => "N"

inductive ProdOrSum where
  | prod
  | sum
deriving Inhabited, BEq

instance : ToString ProdOrSum where
  toString
    | .prod => "Π"
    | .sum => "Σ"

mutual

inductive Monotype : (uvars : optParam Bool false) → Type where
  | var (index : Nat) : Monotype uvars
  -- A uvar that can only be unified with a variable.
  | varuvar (id : Nat) : Monotype true
  | uvar (id : Nat) : Monotype true
  | lam : Kind → Monotype uvars → Monotype uvars
  | app : Monotype uvars → Monotype uvars → Monotype uvars
  | arr : Monotype uvars → Monotype uvars → Monotype uvars
  | label : String → Monotype uvars
  | floor : Monotype uvars → Monotype uvars
  | comm : Comm → Monotype uvars
  | row : MonotypePairList uvars → Option Kind → Monotype uvars
  | prodOrSum : ProdOrSum → Monotype uvars → Monotype uvars
  | lift : Monotype uvars
  | contain (ρ₀ μ ρ₁ : Monotype uvars) : Monotype uvars
  | concat (ρ₀ μ ρ₁ ρ₂ : Monotype uvars) : Monotype uvars
  | tc : String → Monotype uvars
  | all : Monotype uvars
  | ind : Monotype uvars
  | split : Monotype uvars
  | list : Monotype uvars
  | nat : Monotype uvars
  | str : Monotype uvars
  | alias : String → Monotype uvars
deriving BEq

inductive MonotypePairList : (uvars : optParam Bool false) → Type where
  | nil : MonotypePairList uvars
  | cons (head₀ head₁ : Monotype uvars) (tail : MonotypePairList uvars) : MonotypePairList uvars
deriving BEq

end

mutual

@[simp]
protected noncomputable
def Monotype.sizeOf : Monotype uvars → Nat
  | .var _ | .varuvar _ | .uvar _ | .label _ | .comm _ | .lift | .tc _ | .all | .ind | .split
  | .list | .nat | .str | .alias _ => 1
  | .lam κ τ => 1 + sizeOf κ + τ.sizeOf
  | .app ϕ τ => 1 + ϕ.sizeOf + τ.sizeOf
  | .arr τ₀ τ₁ => 1 + τ₀.sizeOf + τ₁.sizeOf
  | .floor ξ => 1 + ξ.sizeOf
  | .row ξτs κ? => 1 + ξτs.sizeOf + sizeOf κ?
  | .prodOrSum _ ρ => 1 + ρ.sizeOf
  | .contain ρ₀ μ ρ₁ => 1 + ρ₀.sizeOf + μ.sizeOf + ρ₁.sizeOf
  | .concat ρ₀ μ ρ₁ ρ₂ => 1 + ρ₀.sizeOf + μ.sizeOf + ρ₁.sizeOf + ρ₂.sizeOf

@[simp]
protected noncomputable
def MonotypePairList.sizeOf : MonotypePairList uvars → Nat
  | .nil => 1
  | .cons head₀ head₁ tail => 2 + head₀.sizeOf + head₁.sizeOf + tail.sizeOf

end

noncomputable
instance (priority := high) : SizeOf (Monotype uvars) where
  sizeOf := Monotype.sizeOf

namespace MonotypePairList

instance : Inhabited (MonotypePairList uvars) where
  default := nil

def toList : MonotypePairList uvars → List (Monotype uvars × Monotype uvars)
  | nil => []
  | cons head₀ head₁ tail => (head₀, head₁) :: tail.toList

def ofList : List (Monotype uvars × Monotype uvars) → MonotypePairList uvars
  | [] => nil
  | (head₀, head₁) :: tail => cons head₀ head₁ <| .ofList tail

noncomputable
instance (priority := high) : SizeOf (MonotypePairList uvars) where
  sizeOf := MonotypePairList.sizeOf

@[simp]
theorem sizeOf_toList' : MonotypePairList.sizeOf ξτs = SizeOf.sizeOf (toList ξτs) := by
  match ξτs with
  | nil =>
    rw [toList, List.nil.sizeOf_spec]
    simp [sizeOf]
  | cons _ _ tail =>
    rw [toList, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, ← Nat.add_assoc, ← Nat.add_assoc]
    simp [SizeOf.sizeOf]
    have := tail.sizeOf_toList'
    simp [SizeOf.sizeOf] at this
    rw [this]

@[simp]
theorem sizeOf_toList : SizeOf.sizeOf ξτs = SizeOf.sizeOf (toList ξτs) := by
  rw [SizeOf.sizeOf, instSizeOf]
  simp only
  exact sizeOf_toList'

@[simp]
theorem sizeOf_ofList : SizeOf.sizeOf ξτs = SizeOf.sizeOf (ofList ξτs) := by
  match ξτs with
  | [] =>
    rw [ofList, List.nil.sizeOf_spec]
    simp [SizeOf.sizeOf]
  | _ :: tail =>
    rw [ofList, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, ← Nat.add_assoc, ← Nat.add_assoc]
    simp [SizeOf.sizeOf]
    have := sizeOf_ofList (ξτs := tail)
    simp [SizeOf.sizeOf] at this
    rw [this]

end MonotypePairList

namespace Monotype

instance : Inhabited (Monotype uvars) where
  default := var 1000000

def toString (τ : Monotype uvars) : String := match τ with
  | var n => s!"{n}"
  | varuvar n => s!"vu{n}"
  | uvar n => s!"u{n}"
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
    let ξτsString := ξτs.toList.mapMem fun (ξ, τ) _ => s!"{ξ.toString} ▹ {τ.toString}"
    s!"⟨{ξτsString}{κString}⟩"
  | prodOrSum Ξ μ => s!"{Ξ}({μ.toString})"
  | lift => "Lift"
  | contain ρ₀ μ ρ₁ => s!"{ρ₀.toString} ≲({μ.toString}) {ρ₁.toString}"
  | concat ρ₀ μ ρ₁ ρ₂ => s!"{ρ₀.toString} ⊙({μ.toString}) {ρ₁.toString} ~ {ρ₂.toString}"
  | tc s => s
  | all => "All"
  | ind => "Ind"
  | split => "Split"
  | list => "List"
  | nat => "Nat"
  | str => "String"
  | «alias» s => s
termination_by sizeOf τ
decreasing_by
  all_goals simp_arith [sizeOf]
  all_goals (
    apply Nat.le_add_right_of_le
    apply Nat.le_of_lt <| Nat.lt_of_le_of_lt (m := sizeOf (ξ, τ)) _ <| List.sizeOf_lt_of_mem ..
    · simp_arith
      simp_arith [sizeOf]
    · assumption
  )

instance : ToString (Monotype uvars) where
  toString := toString

end Monotype

inductive QualifiedType : (uvars : optParam Bool false) → Type where
  | mono : Monotype uvars → QualifiedType uvars
  | qual : Monotype uvars → QualifiedType uvars → QualifiedType uvars
deriving Inhabited, BEq

namespace QualifiedType

instance : Coe (Monotype uvars) (QualifiedType uvars) where
  coe := .mono

def toString : QualifiedType uvars → String
  | .mono τ => τ.toString
  | .qual ψ γ => s!"{ψ} ⇒ {γ.toString}"

instance : ToString (QualifiedType uvars) where
  toString := QualifiedType.toString

end QualifiedType

open QualifiedType

inductive TypeScheme : (uvars : optParam Bool false) → Type where
  | qual : QualifiedType uvars → TypeScheme uvars
  | quant : Kind → TypeScheme uvars → TypeScheme uvars
deriving Inhabited, BEq

namespace TypeScheme

instance : Coe (QualifiedType uvars) (TypeScheme uvars) where
  coe := .qual

def toString : TypeScheme uvars → String
  | .qual γ => γ.toString
  | .quant κ σ => s!"∀ {κ}. {σ.toString}"

instance : ToString (TypeScheme uvars) where
  toString := toString

end TypeScheme

open TypeScheme

mutual

inductive Term : (uvars : optParam Bool false) → Type where
  | var : Nat → Term uvars
  | member : String → Term uvars
  | lam : Term uvars → Term uvars
  | app : Term uvars → Term uvars → Term uvars
  | let : TypeScheme uvars → Term uvars → Term uvars → Term uvars
  | annot : Term uvars → TypeScheme uvars → Term uvars
  | label : String → Term uvars
  | prod : TermPairList uvars → Term uvars
  | sum : Term uvars → Term uvars → Term uvars
  | unlabel : Term uvars → Term uvars → Term uvars
  | prj : Term uvars → Term uvars
  | concat : Term uvars → Term uvars → Term uvars
  | inj : Term uvars → Term uvars
  | elim : Term uvars → Term uvars → Term uvars
  | ind : Monotype uvars → Monotype uvars → Term uvars → Term uvars → Term uvars
  | splitₚ : Monotype uvars → Term uvars → Term uvars
  | splitₛ : Monotype uvars → Term uvars → Term uvars → Term uvars
  | nil : Term uvars
  | cons : Term uvars → Term uvars → Term uvars
  | fold : Term uvars
  | nat : Nat → Term uvars
  | op : Op → Term uvars → Term uvars → Term uvars
  | range : Term uvars
  | str : String → Term uvars
  | def : String → Term uvars
deriving BEq

inductive TermPairList : (uvars : optParam Bool false) → Type where
  | nil : TermPairList uvars
  | cons (head₀ head₁ : Term uvars) (tail : TermPairList uvars) : TermPairList uvars
deriving BEq

end

mutual

@[simp]
protected noncomputable
def Term.sizeOf : Term uvars → Nat
  | .var _ | .member _ | .label _ | .nil | .fold | .nat _ | .range | .str _ | .def _ => 1
  | .lam M | .prj M | .inj M => 1 + M.sizeOf
  | .app M N | .sum M N | .unlabel M N | .concat M N | .elim M N | .cons M N | .op _ M N =>
    1 + M.sizeOf + N.sizeOf
  | .let σ M N => 1 + sizeOf σ + M.sizeOf + N.sizeOf
  | .annot M σ => 1 + M.sizeOf + sizeOf σ
  | .prod MNs => 1 + MNs.sizeOf
  | .ind ϕ ρ M N => 1 + sizeOf ϕ + sizeOf ρ + M.sizeOf + N.sizeOf
  | .splitₚ ϕ M => 1 + sizeOf ϕ + M.sizeOf
  | .splitₛ ϕ M N => 1 + sizeOf ϕ + M.sizeOf + N.sizeOf

@[simp]
protected noncomputable
def TermPairList.sizeOf : TermPairList uvars → Nat
  | .nil => 1
  | .cons head₀ head₁ tail => 2 + head₀.sizeOf + head₁.sizeOf + tail.sizeOf

end

noncomputable
instance (priority := high) : SizeOf (Term uvars) where
  sizeOf := Term.sizeOf

namespace TermPairList

instance : Inhabited (TermPairList uvars) where
  default := .nil

def toList : TermPairList uvars → List (Term uvars × Term uvars)
  | nil => []
  | cons head₀ head₁ tail => (head₀, head₁) :: tail.toList

def ofList : List (Term uvars × Term uvars) → TermPairList uvars
  | [] => nil
  | (head₀, head₁) :: tail => cons head₀ head₁ <| .ofList tail

noncomputable
instance (priority := high) : SizeOf (TermPairList uvars) where
  sizeOf := TermPairList.sizeOf

@[simp]
theorem sizeOf_toList' : TermPairList.sizeOf ξτs = SizeOf.sizeOf (toList ξτs) := by
  match ξτs with
  | nil =>
    rw [toList, List.nil.sizeOf_spec]
    simp [sizeOf]
  | cons _ _ tail =>
    rw [toList, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, ← Nat.add_assoc, ← Nat.add_assoc]
    simp [SizeOf.sizeOf]
    have := tail.sizeOf_toList'
    simp [SizeOf.sizeOf] at this
    rw [this]

@[simp]
theorem sizeOf_toList : SizeOf.sizeOf ξτs = SizeOf.sizeOf (toList ξτs) := by
  rw [SizeOf.sizeOf, instSizeOf]
  simp only
  exact sizeOf_toList'

@[simp]
theorem sizeOf_ofList : SizeOf.sizeOf ξτs = SizeOf.sizeOf (ofList ξτs) := by
  match ξτs with
  | [] =>
    rw [ofList, List.nil.sizeOf_spec]
    simp [SizeOf.sizeOf]
  | _ :: tail =>
    rw [ofList, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, ← Nat.add_assoc, ← Nat.add_assoc]
    simp [SizeOf.sizeOf]
    have := sizeOf_ofList (ξτs := tail)
    simp [SizeOf.sizeOf] at this
    rw [this]

end TermPairList

namespace Term

instance : Inhabited (Term uvars) where
  default := var 1000000

private
def termsFromList (M : Term uvars) : List (Term uvars) × Option (Term uvars) := match M with
  | cons M' N =>
    let (Ms, N'?) := termsFromList N
    (M' :: Ms, N'?)
  | nil => ([], none)
  | _ => ([], M)

mutual

partial
def tableFromTerms (Ms : List (Term uvars)) : Option String := do
  let .prod MNs :: _ := Ms | none
  let header ← MNs.toList.mapM fun | (.label s, _) => some s | _ => none
  let entries ← Ms.mapM fun
    | .prod MNs' => some <| MNs'.toList.map fun (_, N) => N.toString true
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
def toString (M : Term uvars) (table := false) : String := match M with
  | var n => s!"v{n}"
  | member s => s
  | lam M' => s!"(λ. {M'.toString})"
  | app M' N => s!"{M'.toString} {N.toString}"
  | «let» σ M' N => s!"let {σ} = {M'.toString} in {N.toString}"
  | annot M' σ => s!"({M'.toString} : {σ})"
  | label s => s
  | prod M'Ns =>
    s!"\{{String.join <| List.intersperse ", " <|
            M'Ns.toList.map fun (M', N) => s!"{M'.toString} ▹ {N.toString}"}}"
  | sum M' N => s!"[{M'.toString} ▹ {N.toString}]"
  | unlabel M' N => s!"{M'.toString}/{N.toString}"
  | prj M' => s!"prj {M'.toString}"
  | concat M' N => s!"{M'.toString} ++ {N.toString}"
  | inj M' => s!"inj {M'.toString}"
  | elim M' N => s!"{M'.toString} ▿ {N.toString}"
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
  | «def» s => s

end

instance : ToString (Term uvars) where
  toString := toString

end Term

end Interpreter

end TabularTypeInterpreter
