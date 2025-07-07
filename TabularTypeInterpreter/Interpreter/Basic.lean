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
deriving Inhabited, Hashable, BEq, DecidableEq

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
deriving Inhabited, Hashable, BEq, DecidableEq

instance : ToString Comm where
  toString
    | .comm => "C"
    | .non => "N"

inductive ProdOrSum where
  | prod
  | sum
deriving Inhabited, Hashable, BEq, DecidableEq

instance : ToString ProdOrSum where
  toString
    | .prod => "Π"
    | .sum => "Σ"

abbrev TId := Id `type

mutual

inductive Monotype where
  | var : TId → Monotype
  | uvar : Nat → Monotype
  | lam : TId → Kind → Monotype → Monotype
  | app : Monotype → Monotype → Monotype
  | arr : Monotype → Monotype → Monotype
  | label : String → Monotype
  | floor : Monotype → Monotype
  | comm : Comm → Monotype
  | row : MonotypePairList → Option Kind → Monotype
  | prodOrSum : ProdOrSum → Monotype → Monotype
  | lift : Monotype
  | contain (ρ₀ μ ρ₁ : Monotype) : Monotype
  | concat (ρ₀ μ ρ₁ ρ₂ : Monotype) : Monotype
  | tc : String → Monotype
  | all : Monotype
  | ind : Monotype
  | split : Monotype
  | list : Monotype
  | int : Monotype
  | str : Monotype
  | alias : String → Monotype
deriving Hashable, BEq, DecidableEq

inductive MonotypePairList where
  | nil : MonotypePairList
  | cons (head₀ head₁ : Monotype) (tail : MonotypePairList) : MonotypePairList
deriving Hashable, BEq, DecidableEq

end

mutual

@[simp]
protected noncomputable
def Monotype.sizeOf : Monotype → Nat
  | .var _ | .uvar _ | .label _ | .comm _ | .lift | .tc _ | .all | .ind | .split
  | .list | .int | .str | .alias _ => 1
  | .lam _ κ τ => 1 + sizeOf κ + τ.sizeOf
  | .app ϕ τ => 1 + ϕ.sizeOf + τ.sizeOf
  | .arr τ₀ τ₁ => 1 + τ₀.sizeOf + τ₁.sizeOf
  | .floor ξ => 1 + ξ.sizeOf
  | .row ξτs κ? => 1 + ξτs.sizeOf + sizeOf κ?
  | .prodOrSum _ ρ => 1 + ρ.sizeOf
  | .contain ρ₀ μ ρ₁ => 1 + ρ₀.sizeOf + μ.sizeOf + ρ₁.sizeOf
  | .concat ρ₀ μ ρ₁ ρ₂ => 1 + ρ₀.sizeOf + μ.sizeOf + ρ₁.sizeOf + ρ₂.sizeOf

@[simp]
protected noncomputable
def MonotypePairList.sizeOf : MonotypePairList → Nat
  | .nil => 1
  | .cons head₀ head₁ tail => 2 + head₀.sizeOf + head₁.sizeOf + tail.sizeOf

end

noncomputable
instance (priority := high) : SizeOf Monotype where
  sizeOf := Monotype.sizeOf

namespace MonotypePairList

instance : Inhabited MonotypePairList where
  default := nil

def toList : MonotypePairList → List (Monotype × Monotype)
  | nil => []
  | cons head₀ head₁ tail => (head₀, head₁) :: tail.toList

def ofList : List (Monotype × Monotype) → MonotypePairList
  | [] => nil
  | (head₀, head₁) :: tail => cons head₀ head₁ <| .ofList tail

noncomputable
instance (priority := high) : SizeOf MonotypePairList where
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

instance : Inhabited Monotype where
  default := var <| .mk 1000000

def toString [ToString TId] (τ : Monotype) : String := match τ with
  | var i => s!"{i}"
  | uvar n => s!"u{n}"
  | lam i κ τ => s!"(λ {i} : {κ}. {τ.toString})"
  | app ϕ τ => s!"{ϕ.toString} {τ.toString}"
  | arr τ₀ τ₁ => s!"{τ₀.toString} → {τ₁.toString}"
  | label s => s!"'{s}'"
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
  | int => "Int"
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

instance [ToString TId] : ToString Monotype where
  toString := toString

def unit : Monotype := row .nil <| some .star

def bool : Monotype := prodOrSum .sum (comm .non) |>.app <|
  row (.cons (label "false") unit (.cons (label "true") unit .nil)) none

end Monotype

inductive QualifiedType where
  | mono : Monotype → QualifiedType
  | qual : Monotype → QualifiedType → QualifiedType
deriving Inhabited, BEq, DecidableEq

namespace QualifiedType

instance : Coe Monotype QualifiedType where
  coe := .mono

def toString [ToString TId] : QualifiedType → String
  | .mono τ => τ.toString
  | .qual ψ γ => s!"{ψ} ⇒ {γ.toString}"

instance [ToString TId] : ToString QualifiedType where
  toString := QualifiedType.toString

end QualifiedType

open QualifiedType

inductive TypeScheme where
  | qual : QualifiedType → TypeScheme
  | quant : TId → Kind → TypeScheme → TypeScheme
deriving Inhabited, BEq, DecidableEq

namespace TypeScheme

instance : Coe QualifiedType TypeScheme where
  coe := .qual

def toString [ToString TId] : TypeScheme → String
  | .qual γ => γ.toString
  | .quant i κ σ => s!"∀ {i} {κ}. {σ.toString}"

instance [ToString TId] : ToString TypeScheme where
  toString := toString

end TypeScheme

open TypeScheme

abbrev MId := Id `term

mutual

inductive Term where
  | var : MId → Term
  | member : String → Term
  | lam : MId → Term → Term
  | app : Term → Term → Term
  | let : MId → Option TypeScheme → Term → Term → Term
  | annot : Term → TypeScheme → Term
  | label : String → Term
  | prod : TermPairList → Term
  | sum : Term → Term → Term
  | unlabel : Term → Term → Term
  | prj : Term → Term
  | concat : Term → Term → Term
  | inj : Term → Term
  | elim : Term → Term → Term
  | ind (ϕ ρ : Monotype) (l t rn ri rp : TId) (M N : Term) : Term
  | splitₚ : Monotype → Term → Term
  | splitₛ : Monotype → Term → Term → Term
  | nil : Term
  | cons : Term → Term → Term
  | fold : Term
  | int : Int → Term
  | op : Op → Term → Term → Term
  | range : Term
  | str : String → Term
  | throw : Term
  | def : String → Term
deriving BEq, DecidableEq

inductive TermPairList where
  | nil : TermPairList
  | cons (head₀ head₁ : Term) (tail : TermPairList) : TermPairList
deriving BEq, DecidableEq

end

mutual

@[simp]
protected noncomputable
def Term.sizeOf : Term → Nat
  | .var _ | .member _ | .label _ | .nil | .fold | .int _ | .range | .str _ | .throw | .def _ => 1
  | .lam _ M | .prj M | .inj M => 1 + M.sizeOf
  | .app M N | .sum M N | .unlabel M N | .concat M N | .elim M N | .cons M N | .op _ M N =>
    1 + M.sizeOf + N.sizeOf
  | .let _ σ? M N => 1 + sizeOf σ? + M.sizeOf + N.sizeOf
  | .annot M σ => 1 + M.sizeOf + sizeOf σ
  | .prod MNs => 1 + MNs.sizeOf
  | .ind ϕ ρ _ _ _ _ _ M N => 1 + sizeOf ϕ + sizeOf ρ + M.sizeOf + N.sizeOf
  | .splitₚ ϕ M => 1 + sizeOf ϕ + M.sizeOf
  | .splitₛ ϕ M N => 1 + sizeOf ϕ + M.sizeOf + N.sizeOf

@[simp]
protected noncomputable
def TermPairList.sizeOf : TermPairList → Nat
  | .nil => 1
  | .cons head₀ head₁ tail => 2 + head₀.sizeOf + head₁.sizeOf + tail.sizeOf

end

noncomputable
instance (priority := high) : SizeOf Term where
  sizeOf := Term.sizeOf

namespace TermPairList

instance : Inhabited TermPairList where
  default := .nil

def toList : TermPairList → List (Term × Term)
  | nil => []
  | cons head₀ head₁ tail => (head₀, head₁) :: tail.toList

def ofList : List (Term × Term) → TermPairList
  | [] => nil
  | (head₀, head₁) :: tail => cons head₀ head₁ <| .ofList tail

noncomputable
instance (priority := high) : SizeOf TermPairList where
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

@[simp]
theorem ofList_left_inv_toList : ofList (toList MNs) = MNs := by
  match MNs with
  | nil => rw [toList, ofList]
  | cons head₀ head₁ tail => rw [toList, ofList, ofList_left_inv_toList]

end TermPairList

namespace Term

instance : Inhabited Term where
  default := label "default"

private
def termsFromList (M : Term) : List Term × Option Term := match M with
  | cons M' N =>
    let (Ms, N'?) := termsFromList N
    (M' :: Ms, N'?)
  | nil => ([], none)
  | _ => ([], M)

mutual

partial
def tableFromTerms [ToString TId] [ToString MId] (Ms : List Term) : Option String := do
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
def toString [ToString TId] [ToString MId] (M : Term) (table := false) : String := match M with
  | var i => s!"{i}"
  | member s => s
  | lam i M' => s!"(λ {i}. {M'.toString})"
  | app M' N => s!"{M'.toString} {N.toString}"
  | «let» i σ? M' N =>
    if let some σ := σ? then
      s!"let {i} : {σ} = {M'.toString} in {N.toString}"
    else
      s!"let {i} = {M'.toString} in {N.toString}"
  | annot M' σ => s!"({M'.toString} : {σ})"
  | label s => s!"'{s}'"
  | prod M'Ns =>
    s!"\{{String.join <| List.intersperse ", " <|
            M'Ns.toList.map fun (M', N) => s!"{M'.toString} ▹ {N.toString}"}}"
  | sum M' N => s!"[{M'.toString} ▹ {N.toString}]"
  | unlabel M' N => s!"{M'.toString}/{N.toString}"
  | prj M' => s!"prj {M'.toString}"
  | concat M' N => s!"{M'.toString} ++ {N.toString}"
  | inj M' => s!"inj {M'.toString}"
  | elim M' N => s!"{M'.toString} ▿ {N.toString}"
  | ind ϕ ρ _ _ _ _ _ M' N => s!"ind {ϕ} {ρ} {M'.toString} {N.toString}"
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
  | int i => s!"{i}"
  | op o M' N => s!"{M'.toString} {o} {N.toString}"
  | range => "range"
  | str s => s.quote
  | throw => "throw"
  | «def» s => s

end

instance [ToString TId] [ToString MId] : ToString Term where
  toString := toString

end Term

structure ClassDeclaration where
  (TCₛs : List String) (TC : String) (a : TId) (κ : Kind) (m : String) (σ : TypeScheme)
deriving BEq
inductive ProgramEntry where
  | def (x : String) (σ? : Option TypeScheme) (M : Term)
  | typeAlias (a : String) (σ : TypeScheme)
  | class (decl : ClassDeclaration)
  | instance (as : List TId) (ψs : List Monotype) (TC : String) (τ : Monotype) (M : Term)
deriving BEq

variable {TC} in
instance [ToString TId] [ToString MId] : ToString ProgramEntry where
  toString
    | .def x σ? M => s!"def {x} {match σ? with | some σ => s!": {σ} " | none => ""}= {M}"
    | .typeAlias a σ => s!"type {a} = {σ}"
    | .class { TCₛs, TC, a, κ, m, σ } =>
      let TCₛs := if TCₛs.length == 0 then "" else
        s!"{", ".intercalate <| TCₛs.map (s!"{·} {a}")} ⇒ "
      s!"class {TCₛs}{TC} {a} : {κ} where\n  {m} : {σ}"
    | .instance _ ψs TC τ M =>
      let ψs := if ψs.length == 0 then "" else
        s!"{", ".intercalate <| ψs.map ToString.toString} ⇒ "
      s!"instance {ψs}{TC} {τ} where\n  {M}"

abbrev Program := List ProgramEntry

instance (priority := high) [ToString TId] [ToString MId] : ToString Program where
  toString pgm := "\n\n".intercalate <| pgm.map ToString.toString

end Interpreter

end TabularTypeInterpreter
