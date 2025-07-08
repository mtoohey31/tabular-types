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

inductive Monotype where
  | var : TId → Monotype
  | uvar : Nat → Monotype
  | lam : TId → Kind → Monotype → Monotype
  | app : Monotype → Monotype → Monotype
  | arr : Monotype → Monotype → Monotype
  | label : String → Monotype
  | floor : Monotype → Monotype
  | comm : Comm → Monotype
  | row : List (Monotype × Monotype) → Option Kind → Monotype
  | prodOrSum : ProdOrSum → Monotype → Monotype
  | lift (ϕ : Monotype) : Monotype
  | contain (ρ₀ μ ρ₁ : Monotype) : Monotype
  | concat (ρ₀ μ ρ₁ ρ₂ : Monotype) : Monotype
  | tc : String → Monotype
  | all (ϕ : Monotype) : Monotype
  | ind (ρ : Monotype) : Monotype
  | split (ϕ ρ₀ ρ₁ ρ₂ : Monotype) : Monotype
  | list : Monotype
  | int : Monotype
  | str : Monotype
  | alias : String → Monotype
deriving Inhabited, Hashable, BEq

namespace Monotype

private
def decidableEq (τ₀ τ₁ : Monotype) : Decidable (τ₀ = τ₁) := by
  match τ₀ with
  | var i₀ =>
    cases τ₁
    case var i₁ =>
      exact if h : i₀ = i₁ then isTrue <| var.injEq .. |>.mpr h else isFalse (h <| var.inj ·)
    all_goals exact isFalse nofun
  | uvar x₀ =>
    cases τ₁
    case uvar x₁ =>
      exact if h : x₀ = x₁ then isTrue <| uvar.injEq .. |>.mpr h else isFalse (h <| uvar.inj ·)
    all_goals exact isFalse nofun
  | lam i₀ κ₀ τ₀' =>
    cases τ₁
    case lam i₁ κ₁ τ₁' =>
      exact if hi : i₀ = i₁ then
        if hκ : κ₀ = κ₁ then
          match decidableEq τ₀' τ₁' with
          | isTrue hτ => isTrue <| lam.injEq .. |>.mpr ⟨hi, hκ, hτ⟩
          | isFalse hτ =>
            isFalse (hτ <| And.right <| And.right <| lam.inj ·)
        else
          isFalse (hκ <| And.left <| And.right <| lam.inj ·)
      else
        isFalse (hi <| And.left <| lam.inj ·)
    all_goals exact isFalse nofun
  | app τ₀' τ₀'' =>
    cases τ₁
    case app τ₁' τ₁'' =>
      exact match decidableEq τ₀' τ₁' with
        | isTrue hτ => match decidableEq τ₀'' τ₁'' with
          | isTrue hτ' => isTrue <| app.injEq .. |>.mpr ⟨hτ, hτ'⟩
          | isFalse hτ' => isFalse (hτ' <| And.right <| app.inj ·)
        | isFalse hτ => isFalse (hτ <| And.left <| app.inj ·)
    all_goals exact isFalse nofun
  | arr τ₀' τ₀'' =>
    cases τ₁
    case arr τ₁' τ₁'' =>
      exact match decidableEq τ₀' τ₁' with
        | isTrue hτ => match decidableEq τ₀'' τ₁'' with
          | isTrue hτ' => isTrue <| arr.injEq .. |>.mpr ⟨hτ, hτ'⟩
          | isFalse hτ' => isFalse (hτ' <| And.right <| arr.inj ·)
        | isFalse hτ => isFalse (hτ <| And.left <| arr.inj ·)
    all_goals exact isFalse nofun
  | label s₀ =>
    cases τ₁
    case label s₁ =>
      exact if h : s₀ = s₁ then isTrue <| label.injEq .. |>.mpr h else isFalse (h <| label.inj ·)
    all_goals exact isFalse nofun
  | floor ξ₀ =>
    cases τ₁
    case floor ξ₁ =>
      exact match decidableEq ξ₀ ξ₁ with
        | isTrue h => isTrue <| floor.injEq .. |>.mpr h
        | isFalse h => isFalse (h <| floor.inj ·)
    all_goals exact isFalse nofun
  | comm u₀ =>
    cases τ₁
    case comm u₁ =>
      exact if h : u₀ = u₁ then isTrue <| comm.injEq .. |>.mpr h else isFalse (h <| comm.inj ·)
    all_goals exact isFalse nofun
  | row ξτs₀ κ₀ =>
    cases τ₁
    case row ξτs₁ κ₁ =>
      exact match ξτs₀ with
        | [] => match ξτs₁ with
          | [] => if hκ : κ₀ = κ₁ then
              isTrue <| row.injEq .. |>.mpr ⟨rfl, hκ⟩
            else
              isFalse (hκ <| And.right <| row.inj ·)
          | (ξ₁, τ₁) :: ξτs₁' => isFalse (nomatch And.left <| row.inj ·)
        | (ξ₀, τ₀) :: ξτs₀' => match ξτs₁ with
          | [] => isFalse (nomatch And.left <| row.inj ·)
          | (ξ₁, τ₁) :: ξτs₁' => match decidableEq ξ₀ ξ₁ with
            | isTrue hξ => match decidableEq τ₀ τ₁ with
              | isTrue hτ => match decidableEq (row ξτs₀' κ₀) (row ξτs₁' κ₁) with
                | isTrue hξτs' =>
                  let ⟨hξτs', hκ⟩ := row.inj hξτs'
                  isTrue <| row.injEq .. |>.mpr ⟨
                    List.cons.injEq .. |>.mpr ⟨
                      Prod.mk.injEq .. |>.mpr ⟨hξ, hτ⟩,
                      hξτs'
                    ⟩,
                    hκ
                  ⟩
                | isFalse hξτs' => by
                  apply isFalse
                  intro eq
                  let ⟨ξτseq, κeq⟩ := row.inj eq
                  let ⟨_, ξτs'eq⟩ := List.cons.inj ξτseq
                  exact (hξτs' <| row.injEq .. |>.mpr ·) ⟨ξτs'eq, κeq⟩
              | isFalse hτ =>
                isFalse (hτ <| And.right <| Prod.mk.inj <| And.left <|
                  List.cons.inj <| And.left <| row.inj ·)
            | isFalse hξ =>
              isFalse (hξ <| And.left <| Prod.mk.inj <| And.left <|
                List.cons.inj <| And.left <| row.inj ·)
    all_goals exact isFalse nofun
  | prodOrSum Ξ₀ μ₀ =>
    cases τ₁
    case prodOrSum Ξ₁ μ₁ =>
      exact if hΞ : Ξ₀ = Ξ₁ then
          match decidableEq μ₀ μ₁ with
          | isTrue hμ => isTrue <| prodOrSum.injEq .. |>.mpr ⟨hΞ, hμ⟩
          | isFalse hμ => isFalse (hμ <| And.right <| prodOrSum.inj ·)
        else
          isFalse (hΞ <| And.left <| prodOrSum.inj ·)
    all_goals exact isFalse nofun
  | lift ϕ₀ =>
    cases τ₁
    case lift ϕ₁ =>
      exact match decidableEq ϕ₀ ϕ₁ with
        | isTrue hϕ => isTrue <| lift.injEq .. |>.mpr hϕ
        | isFalse hϕ => isFalse (hϕ <| lift.inj ·)
    all_goals exact isFalse nofun
  | contain ρ₀₀ μ₀ ρ₁₀ =>
    cases τ₁
    case contain ρ₀₁ μ₁ ρ₁₁ =>
      exact match decidableEq ρ₀₀ ρ₀₁ with
        | isTrue hρ₀ => match decidableEq μ₀ μ₁ with
          | isTrue hμ => match decidableEq ρ₁₀ ρ₁₁ with
            | isTrue hρ₁ => isTrue <| contain.injEq .. |>.mpr ⟨hρ₀, hμ, hρ₁⟩
            | isFalse hρ₁ => isFalse (hρ₁ <| And.right <| And.right <| contain.inj ·)
          | isFalse hμ => isFalse (hμ <| And.left <| And.right <| contain.inj ·)
        | isFalse hρ₀ => isFalse (hρ₀ <| And.left <| contain.inj ·)
    all_goals exact isFalse nofun
  | concat ρ₀₀ μ₀ ρ₁₀ ρ₂₀ =>
    cases τ₁
    case concat ρ₀₁ μ₁ ρ₁₁ ρ₂₁ =>
      exact match decidableEq ρ₀₀ ρ₀₁ with
        | isTrue hρ₀ => match decidableEq μ₀ μ₁ with
          | isTrue hμ => match decidableEq ρ₁₀ ρ₁₁ with
            | isTrue hρ₁ => match decidableEq ρ₂₀ ρ₂₁ with
              | isTrue hρ₂ => isTrue <| concat.injEq .. |>.mpr ⟨hρ₀, hμ, hρ₁, hρ₂⟩
              | isFalse hρ₂ => isFalse (hρ₂ <| And.right <| And.right <| And.right <| concat.inj ·)
            | isFalse hρ₁ => isFalse (hρ₁ <| And.left <| And.right <| And.right <| concat.inj ·)
          | isFalse hμ => isFalse (hμ <| And.left <| And.right <| concat.inj ·)
        | isFalse hρ₀ => isFalse (hρ₀ <| And.left <| concat.inj ·)
    all_goals exact isFalse nofun
  | tc s₀ =>
    cases τ₁
    case tc s₁ =>
      exact if h : s₀ = s₁ then isTrue <| tc.injEq .. |>.mpr h else isFalse (h <| tc.inj ·)
    all_goals exact isFalse nofun
  | all ϕ₀ =>
    cases τ₁
    case all ϕ₁ =>
      exact match decidableEq ϕ₀ ϕ₁ with
        | isTrue hϕ => isTrue <| all.injEq .. |>.mpr hϕ
        | isFalse hϕ => isFalse (hϕ <| all.inj ·)
    all_goals exact isFalse nofun
  | ind ρ₀ =>
    cases τ₁
    case ind ρ₁ =>
      exact match decidableEq ρ₀ ρ₁ with
        | isTrue hρ => isTrue <| ind.injEq .. |>.mpr hρ
        | isFalse hρ => isFalse (hρ <| ind.inj ·)
    all_goals exact isFalse nofun
  | split ϕ₀ ρ₀₀ ρ₁₀ ρ₂₀ =>
    cases τ₁
    case split ϕ₁ ρ₀₁ ρ₁₁ ρ₂₁ =>
      exact
        match decidableEq ϕ₀ ϕ₁ with
        | isTrue hϕ => match decidableEq ρ₀₀ ρ₀₁ with
          | isTrue hρ₀ => match decidableEq ρ₁₀ ρ₁₁ with
            | isTrue hρ₁ => match decidableEq ρ₂₀ ρ₂₁ with
              | isTrue hρ₂ => isTrue <| split.injEq .. |>.mpr ⟨hϕ, hρ₀, hρ₁, hρ₂⟩
              | isFalse hρ₂ => isFalse (hρ₂ <| And.right <| And.right <| And.right <| split.inj ·)
            | isFalse hρ₁ => isFalse (hρ₁ <| And.left <| And.right <| And.right <| split.inj ·)
          | isFalse hρ₀ => isFalse (hρ₀ <| And.left <| And.right <| split.inj ·)
        | isFalse hϕ => isFalse (hϕ <| And.left <| split.inj ·)
    all_goals exact isFalse nofun
  | list =>
    cases τ₁
    case list => exact isTrue rfl
    all_goals exact isFalse nofun
  | int =>
    cases τ₁
    case int => exact isTrue rfl
    all_goals exact isFalse nofun
  | str =>
    cases τ₁
    case str => exact isTrue rfl
    all_goals exact isFalse nofun
  | «alias» s₀ =>
    cases τ₁
    case «alias» s₁ =>
      exact if h : s₀ = s₁ then isTrue <| alias.injEq .. |>.mpr h else isFalse (h <| alias.inj ·)
    all_goals exact isFalse nofun

instance : DecidableEq Monotype := decidableEq

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
    let ξτsString := ξτs.mapMem fun (ξ, τ) _ => s!"{ξ.toString} ▹ {τ.toString}"
    s!"⟨{ξτsString}{κString}⟩"
  | prodOrSum Ξ μ => s!"{Ξ}({μ.toString})"
  | lift ϕ => s!"Lift {ϕ.toString}"
  | contain ρ₀ μ ρ₁ => s!"{ρ₀.toString} ≲({μ.toString}) {ρ₁.toString}"
  | concat ρ₀ μ ρ₁ ρ₂ => s!"{ρ₀.toString} ⊙({μ.toString}) {ρ₁.toString} ~ {ρ₂.toString}"
  | tc s => s
  | all ϕ => s!"All {ϕ.toString}"
  | ind ρ => s!"Ind {ρ.toString}"
  | split ϕ ρ₀ ρ₁ ρ₂ => s!"Split {ϕ.toString} {ρ₀.toString} {ρ₁.toString} {ρ₂.toString}"
  | list => "List"
  | int => "Int"
  | str => "String"
  | «alias» s => s
termination_by sizeOf τ
decreasing_by
  all_goals simp_arith
  all_goals (
    apply Nat.le_add_right_of_le
    apply Nat.le_of_lt <| Nat.lt_of_le_of_lt (m := sizeOf (ξ, τ)) _ <| List.sizeOf_lt_of_mem ..
    · simp_arith
    · assumption
  )

instance [ToString TId] : ToString Monotype where
  toString := toString

def unit : Monotype := row .nil <| some .star

def bool : Monotype := prodOrSum .sum (comm .non) |>.app <|
  row [(label "false", unit), (label "true", unit)] none

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

inductive Term where
  | var : MId → Term
  | member : String → Term
  | lam : MId → Term → Term
  | app : Term → Term → Term
  | let : MId → Option TypeScheme → Term → Term → Term
  | annot : Term → TypeScheme → Term
  | label : String → Term
  | prod : List (Term × Term) → Term
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
deriving Inhabited, BEq

namespace Term

private
def decidableEq (M₀ M₁ : Term) : Decidable (M₀ = M₁) := by
  match M₀ with
  | var i₀ =>
    cases M₁
    case var i₁ =>
      exact if h : i₀ = i₁ then isTrue <| var.injEq .. |>.mpr h else isFalse (h <| var.inj ·)
    all_goals exact isFalse nofun
  | member s₀ =>
    cases M₁
    case member i₁ =>
      exact if h : s₀ = i₁ then isTrue <| member.injEq .. |>.mpr h else isFalse (h <| member.inj ·)
    all_goals exact isFalse nofun
  | lam i₀ M₀' =>
    cases M₁
    case lam i₁ M₁' =>
      exact if hi : i₀ = i₁ then
        match decidableEq M₀' M₁' with
        | isTrue hM => isTrue <| lam.injEq .. |>.mpr ⟨hi, hM⟩
        | isFalse hM => isFalse (hM <| And.right <| lam.inj ·)
      else
        isFalse (hi <| And.left <| lam.inj ·)
    all_goals exact isFalse nofun
  | app M₀' N₀ =>
    cases M₁
    case app M₁' N₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => match decidableEq N₀ N₁ with
          | isTrue hN => isTrue <| app.injEq .. |>.mpr ⟨hM, hN⟩
          | isFalse hN => isFalse (hN <| And.right <| app.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| app.inj ·)
    all_goals exact isFalse nofun
  | .let i₀ σ₀? M₀' N₀ =>
    cases M₁
    case «let» i₁ σ₁? M₁' N₁ =>
      exact if hi : i₀ = i₁ then
          if hσ? : σ₀? = σ₁? then
            match decidableEq M₀' M₁' with
            | isTrue hM => match decidableEq N₀ N₁ with
              | isTrue hN => isTrue <| let.injEq .. |>.mpr ⟨hi, hσ?, hM, hN⟩
              | isFalse hN => isFalse (hN <| And.right <| And.right <| And.right <| let.inj ·)
            | isFalse hM => isFalse (hM <| And.left <| And.right <| And.right <| let.inj ·)
          else
            isFalse (hσ? <| And.left <| And.right <| let.inj ·)
        else
          isFalse (hi <| And.left <| let.inj ·)
    all_goals exact isFalse nofun
  | annot M₀' σ₀ =>
    cases M₁
    case annot M₁' σ₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => if hσ : σ₀ = σ₁ then
            isTrue <| annot.injEq .. |>.mpr ⟨hM, hσ⟩
          else
            isFalse (hσ <| And.right <| annot.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| annot.inj ·)
    all_goals exact isFalse nofun
  | label s₀ =>
    cases M₁
    case label s₁ =>
      exact if h : s₀ = s₁ then isTrue <| label.injEq .. |>.mpr h else isFalse (h <| label.inj ·)
    all_goals exact isFalse nofun
  | prod MNs₀ =>
    cases M₁
    case prod MNs₁ =>
      exact match MNs₀ with
        | [] => match MNs₁ with
          | [] => isTrue rfl
          | _ :: _ => isFalse (nomatch prod.inj ·)
        | (M₀', N₀) :: MNs₀' => match MNs₁ with
          | [] => isFalse (nomatch prod.inj ·)
          | (M₁', N₁) :: MNs₁' => match decidableEq M₀' M₁' with
            | isTrue hM => match decidableEq N₀ N₁ with
              | isTrue hN => match decidableEq (prod MNs₀') (prod MNs₁') with
                | isTrue hMNs' => isTrue <| prod.injEq .. |>.mpr <| List.cons.injEq .. |>.mpr ⟨
                    Prod.mk.injEq .. |>.mpr ⟨hM, hN⟩,
                    prod.inj hMNs'
                  ⟩
                | isFalse hMNs' => by
                  apply isFalse
                  intro eq
                  let ⟨_, MNs'eq⟩ := List.cons.inj <| prod.inj eq
                  exact (hMNs' <| prod.injEq .. |>.mpr ·) MNs'eq
              | isFalse hτ =>
                isFalse (hτ <| And.right <| Prod.mk.inj <| And.left <| List.cons.inj <| prod.inj ·)
            | isFalse hξ =>
              isFalse (hξ <| And.left <| Prod.mk.inj <| And.left <| List.cons.inj <| prod.inj ·)
    all_goals exact isFalse nofun
  | sum M₀' N₀ =>
    cases M₁
    case sum M₁' N₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => match decidableEq N₀ N₁ with
          | isTrue hN => isTrue <| sum.injEq .. |>.mpr ⟨hM, hN⟩
          | isFalse hN => isFalse (hN <| And.right <| sum.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| sum.inj ·)
    all_goals exact isFalse nofun
  | unlabel M₀' N₀ =>
    cases M₁
    case unlabel M₁' N₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => match decidableEq N₀ N₁ with
          | isTrue hN => isTrue <| unlabel.injEq .. |>.mpr ⟨hM, hN⟩
          | isFalse hN => isFalse (hN <| And.right <| unlabel.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| unlabel.inj ·)
    all_goals exact isFalse nofun
  | prj M₀' =>
    cases M₁
    case prj M₁' =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => isTrue <| prj.injEq .. |>.mpr hM
        | isFalse hM => isFalse (hM <| prj.inj ·)
    all_goals exact isFalse nofun
  | concat M₀' N₀ =>
    cases M₁
    case concat M₁' N₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => match decidableEq N₀ N₁ with
          | isTrue hN => isTrue <| concat.injEq .. |>.mpr ⟨hM, hN⟩
          | isFalse hN => isFalse (hN <| And.right <| concat.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| concat.inj ·)
    all_goals exact isFalse nofun
  | inj M₀' =>
    cases M₁
    case inj M₁' =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => isTrue <| inj.injEq .. |>.mpr hM
        | isFalse hM => isFalse (hM <| inj.inj ·)
    all_goals exact isFalse nofun
  | elim M₀' N₀ =>
    cases M₁
    case elim M₁' N₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => match decidableEq N₀ N₁ with
          | isTrue hN => isTrue <| elim.injEq .. |>.mpr ⟨hM, hN⟩
          | isFalse hN => isFalse (hN <| And.right <| elim.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| elim.inj ·)
    all_goals exact isFalse nofun
  | ind ϕ₀ ρ₀ l₀ t₀ rn₀ ri₀ rp₀ M₀' N₀ =>
    cases M₁
    case ind ϕ₁ ρ₁ l₁ t₁ rn₁ ri₁ rp₁ M₁' N₁ =>
      exact if hϕ : ϕ₀ = ϕ₁ then
          if hρ : ρ₀ = ρ₁ then
            if hl : l₀ = l₁ then
              if ht : t₀ = t₁ then
                if hrn : rn₀ = rn₁ then
                  if hri : ri₀ = ri₁ then
                    if hrp : rp₀ = rp₁ then
                      match decidableEq M₀' M₁' with
                      | isTrue hM => match decidableEq N₀ N₁ with
                        | isTrue hN =>
                          isTrue <| ind.injEq .. |>.mpr
                            ⟨hϕ, hρ, hl, ht, hrn, hri, hrp, hM, hN⟩
                        | isFalse hN =>
                          isFalse (hN <| And.right <| And.right <| And.right <|
                            And.right <| And.right <| And.right <| And.right <|
                            And.right <| ind.inj ·)
                      | isFalse hM =>
                        isFalse (hM <| And.left <| And.right <| And.right <|
                          And.right <| And.right <| And.right <| And.right <|
                          And.right <| ind.inj ·)
                    else
                      isFalse (hrp <| And.left <| And.right <| And.right <|
                        And.right <| And.right <| And.right <| And.right <| ind.inj ·)
                  else
                    isFalse (hri <| And.left <| And.right <| And.right <|
                      And.right <| And.right <| And.right <| ind.inj ·)
                else
                  isFalse (hrn <| And.left <| And.right <| And.right <| And.right <| And.right <| ind.inj ·)
              else
                isFalse (ht <| And.left <| And.right <| And.right <| And.right <| ind.inj ·)
            else
              isFalse (hl <| And.left <| And.right <| And.right <| ind.inj ·)
          else
            isFalse (hρ <| And.left <| And.right <| ind.inj ·)
        else
          isFalse (hϕ <| And.left <| ind.inj ·)
    all_goals exact isFalse nofun
  | splitₚ ϕ₀ M₀' =>
    cases M₁
    case splitₚ ϕ₁ M₁' =>
      exact if hϕ : ϕ₀ = ϕ₁ then
          match decidableEq M₀' M₁' with
          | isTrue hM => isTrue <| splitₚ.injEq .. |>.mpr ⟨hϕ, hM⟩
          | isFalse hM => isFalse (hM <| And.right <| splitₚ.inj ·)
        else
          isFalse (hϕ <| And.left <| splitₚ.inj ·)
    all_goals exact isFalse nofun
  | splitₛ ϕ₀ M₀' N₀ =>
    cases M₁
    case splitₛ ϕ₁ M₁' N₁ =>
      exact if hϕ : ϕ₀ = ϕ₁ then
          match decidableEq M₀' M₁' with
          | isTrue hM => match decidableEq N₀ N₁ with
            | isTrue hN => isTrue <| splitₛ.injEq .. |>.mpr ⟨hϕ, hM, hN⟩
            | isFalse hN => isFalse (hN <| And.right <| And.right <| splitₛ.inj ·)
          | isFalse hM => isFalse (hM <| And.left <| And.right <| splitₛ.inj ·)
        else
          isFalse (hϕ <| And.left <| splitₛ.inj ·)
    all_goals exact isFalse nofun
  | nil =>
    cases M₁
    case nil => exact isTrue rfl
    all_goals exact isFalse nofun
  | cons M₀' N₀ =>
    cases M₁
    case cons M₁' N₁ =>
      exact match decidableEq M₀' M₁' with
        | isTrue hM => match decidableEq N₀ N₁ with
          | isTrue hN => isTrue <| cons.injEq .. |>.mpr ⟨hM, hN⟩
          | isFalse hN => isFalse (hN <| And.right <| cons.inj ·)
        | isFalse hM => isFalse (hM <| And.left <| cons.inj ·)
    all_goals exact isFalse nofun
  | fold =>
    cases M₁
    case fold => exact isTrue rfl
    all_goals exact isFalse nofun
  | int i₀ =>
    cases M₁
    case int i₁ =>
      exact if h : i₀ = i₁ then isTrue <| int.injEq .. |>.mpr h else isFalse (h <| int.inj ·)
    all_goals exact isFalse nofun
  | op o₀ M₀' N₀ =>
    cases M₁
    case op o₁ M₁' N₁ =>
      exact if ho : o₀ = o₁ then
          match decidableEq M₀' M₁' with
          | isTrue hM => match decidableEq N₀ N₁ with
            | isTrue hN => isTrue <| op.injEq .. |>.mpr ⟨ho, hM, hN⟩
            | isFalse hN => isFalse (hN <| And.right <| And.right <| op.inj ·)
          | isFalse hM => isFalse (hM <| And.left <| And.right <| op.inj ·)
        else
          isFalse (ho <| And.left <| op.inj ·)
    all_goals exact isFalse nofun
  | range =>
    cases M₁
    case range => exact isTrue rfl
    all_goals exact isFalse nofun
  | str s₀ =>
    cases M₁
    case str s₁ =>
      exact if h : s₀ = s₁ then isTrue <| str.injEq .. |>.mpr h else isFalse (h <| str.inj ·)
    all_goals exact isFalse nofun
  | throw =>
    cases M₁
    case throw => exact isTrue rfl
    all_goals exact isFalse nofun
  | «def» s₀ =>
    cases M₁
    case «def» s₁ =>
      exact if h : s₀ = s₁ then isTrue <| def.injEq .. |>.mpr h else isFalse (h <| def.inj ·)
    all_goals exact isFalse nofun

instance : DecidableEq Term := decidableEq

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
            M'Ns.map fun (M', N) => s!"{M'.toString} ▹ {N.toString}"}}"
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
