import TabularTypeInterpreter.Interpreter.Basic
import TabularTypeInterpreter.Interpreter.Elaboration

namespace TabularTypeInterpreter.Interpreter.Inference

-- Some placeholders for now:
/-- type variables -/
abbrev TypeVar := TId
/-- term variables -/
abbrev TermVar := MId
/-- unification variables -/
abbrev UniVar := Nat

/--
The context under which the algorithm is evaluated. 
Each type, term or existential variable can have at most a single declaration in the context.
Furthermore, the context is ordered; entries earlier in the context can not refer to later entries.
-/
inductive ContextItem where
| typevar (α : TypeVar) (κ : Kind)
| termvar (χ : TermVar) (σ : TypeScheme)
| xunivar (ᾱ : UniVar) (κ : Kind)
| sunivar (ᾱ : UniVar) (τ : Monotype)
| mark (ᾱ : UniVar)
| constraint (ψ : Monotype)
deriving Inhabited

instance : ToString ContextItem where toString
| .typevar α κ => s!"{α} : {κ}"
| .termvar χ σ => s!"{χ} : {σ.toString}"
| .xunivar ᾱ κ => s!"{ᾱ} : {κ}"
| .sunivar ᾱ τ => s!"{ᾱ} = {τ.toString}"
| .mark ᾱ => s!"mark {ᾱ}"
| .constraint ψ => toString ψ

/-- Equivalence for context items is entirely determined by the variable, since each must be uniquely declared.
I believe we could derive this instance, but I want to be explicit just in case.
-/
instance : BEq ContextItem where beq
| .typevar α₀ _, .typevar α₁ _ => α₀ == α₁
| .termvar χ₀ _, .termvar χ₁ _ => χ₀ == χ₁
| .xunivar ᾱ₀ _, .xunivar ᾱ₁ _ => ᾱ₀ == ᾱ₁
| .sunivar ᾱ₀ _, .xunivar ᾱ₁ _ => ᾱ₀ == ᾱ₁
| .mark ᾱ₀, .mark ᾱ₁ => ᾱ₀ == ᾱ₁
| .constraint ψ₀, .constraint ψ₁ => sorry -- TODO
| _, _ => false

abbrev Context := List ContextItem

inductive InferError where
| panic (message : String)
deriving Inhabited
structure InferState where Γ : Context deriving Inhabited

abbrev InferM := EStateM InferError InferState
def fresh : InferM UniVar := sorry
def getType (χ : TermVar) : InferM TypeScheme := do
  let { Γ } ← get
  let σ ← (getType' Γ χ).getDM (throw $ .panic "variable not defined")
  return σ
  where getType' (Γ : Context) (χ : TermVar) : Option TypeScheme :=
    match Γ with
    | .nil => .none
    | .cons (.termvar χ' σ) Γ' => if χ == χ' then .some σ else getType' Γ' χ
    | .cons _ Γ' => getType' Γ' χ

def push (item : ContextItem) : InferM Unit := do
  let { Γ } <- get
  set ({ Γ := item::Γ } : InferState)
/-- split the context into (before, after) based on the item's position. -/
def split (item : ContextItem) : InferM (Context × Context) := do
  let { Γ } ← get
  let index ← Γ.idxOf? item |>.getDM (throw $ .panic s!"I was trying to find {item} in the context but it wasn't there; I could have sworn I put it there though!")
  if let (after, _::before) := Γ.splitAt index then
    return (before, after)
  else panic! "malfunction in core `List.idxOf`"
def before (item : ContextItem) : InferM Unit := do
  let (before, _after) ← split item
  set ({ Γ := before } : InferState)
def withItem (item : ContextItem) (m : InferM a) : InferM a := do
  push item
  let x ← m
  before item
  return x

def kind (σ : TypeScheme) (κ : Kind) : InferM Unit := do 
  let { Γ .. } <- get
  match σ with
  | .qual $ .mono $ .var α₀ =>
    if Γ.any (match · with | .typevar α _ => α == α₀ | _ => false) then return
    else throw $ .panic "TODO need descriptive text here"
  | _ => throw $ .panic "TODO unimplemented variant"

def wellFormedContext : InferM Unit := sorry

def subtype (σ₀ σ₁ : TypeScheme) : InferM (σ₀.Subtyping σ₁) := sorry
def instantiateLeft (ᾱ : UniVar) (σ : TypeScheme) : InferM Unit := sorry
def instantiateRight (σ : TypeScheme) (ᾱ : UniVar) : InferM Unit := sorry
def constraint (ψ : Monotype) : InferM (ψ.ConstraintSolution) := do
  kind ψ .constr
  sorry

mutual
partial def check (e : Term) (σ : TypeScheme) : InferM (e.Typing σ) := do
  match σ with
  | .quant α κ σ =>
    let t ← withItem (.typevar α κ) do check e σ
    return t.schemeI
  -- TODO: I am deeply inconfident in this rule.
  | .qual $ .qual ψ γ =>
    kind ψ .constr
    let t ← withItem (.constraint ψ) do check e γ
    return .qualI (fun _ => t)
  | σ =>
    let ⟨σ', t⟩ ← infer e
    -- TODO: σ' and σ should have their bodies solved before subtyping begins
    let s ← subtype σ' σ
    return t.sub s

partial def infer (e : Term) : InferM ((σ : TypeScheme) × e.Typing σ) := do
  match e with
  | .var χ =>
    let { Γ } ← get
    let σ ← getType χ
    return ⟨σ, .var⟩
  | .annot e σ =>
    let t ← check e σ
    return ⟨σ, t.annot⟩
  | .let χ σ? e e' =>
    -- HACK: Had to duplicate code here since the b:=false and b:=true branches have special type checking requirements.
    match σ? with
    | .none => 
      let ⟨σ, t⟩ ← infer e
      let ⟨σ', t'⟩ ← withItem (.termvar χ σ) do infer e'
      return ⟨σ', t.let (b := false) t'⟩
    | .some σ => 
      let t ← check e σ
      let ⟨σ', t'⟩ ← withItem (.termvar χ σ) do infer e'
      return ⟨σ', t.let (b := true) t'⟩
  | .app e₁ e₂ => throw $ .panic "unimplemented"
  | .lam χ e =>
    let a ← fresh
    let b ← fresh
    let τa := Monotype.uvar a
    let τb := Monotype.uvar b
    push <| .xunivar a .star
    push <| .xunivar b .star
    let t ← withItem (.termvar χ τa) do check e τb
    return ⟨Monotype.arr τa τb, t.lam⟩
  | .label l => return ⟨Monotype.floor (.label l), .label⟩
  | .unlabel e₁ e₂ =>
    -- TODO: I think forcing the kind information to be none is a mistake here, but that's what the typing tree expects. I assume it's a mistake there.
    let ⟨Monotype.app (.prodOrSum Ξ μ) (.row (.cons ξ τ .nil) none), t₁⟩ ← infer e₁
      | throw $ .panic "expected a singleton product or sum"
    let t₂ ← check e₂ (ξ.floor)
    return ⟨τ, t₁.unlabel⟩
  | .prod labeledTerms => throw $ .panic "unimplemented"
  | .sum e₁ e₂ =>
    let ⟨.qual $ .mono ξ, _⟩ ← infer e₁
      | throw $ .panic "expected a monotype for the label"
    kind ξ .label
    let ⟨.qual $ .mono τ, t⟩ ← infer e₂
      | throw $ .panic "expected a monotype in the row"
    return ⟨(Monotype.prodOrSum .sum (.comm .non)).app (.row (.cons ξ τ .nil) none), t.sum⟩
  | .prj e =>
    let ⟨Monotype.app (.prodOrSum .prod μ) ρ, t⟩ ← infer e
      | throw $ .panic "projection out of non-record term"
    let rx ← fresh
    push <| .xunivar rx (.row .star)
    let c ← constraint <| .contain (.uvar rx) μ ρ
    return ⟨Monotype.app (.prodOrSum .prod μ) (.uvar rx), t.prj c⟩ 
  | .inj e =>
    let ⟨Monotype.app (.prodOrSum .sum μ) ρ, t⟩ ← infer e
      | throw $ .panic "injection of non-variant term"
    let rx ← fresh
    push <| .xunivar rx (.row .star)
    let c ← constraint <| .contain ρ μ (.uvar rx)
    return ⟨Monotype.app (.prodOrSum .sum μ) (.uvar rx), t.inj c⟩ 
  | .concat m n =>
    let ⟨Monotype.app (.prodOrSum .prod μₘ) ρₘ, tₘ⟩ ← infer m
      | throw $ .panic "concatenation of non-record term"
    let ⟨Monotype.app (.prodOrSum .prod μₙ) ρₙ, tₙ⟩ ← infer n
      | throw $ .panic "concatenation of non-record term"
    -- TODO: generate μ as a single thing by proving μₘ = μₙ
    let rx ← fresh;
    push <| .xunivar rx (.row .star)
    let c ← constraint <| .concat ρₘ μ ρₙ (.uvar rx)
    return ⟨Monotype.app (.prodOrSum .prod μ) (.uvar rx), .concat tₘ tₙ c⟩
  | .elim m n =>
    let ⟨Monotype.arr (.app (.prodOrSum .sum μₘ) ρₘ) τₘ, tₘ⟩ ← infer m
      | throw $ .panic "concatenation of non-record term"
    let ⟨Monotype.arr (.app (.prodOrSum .sum μₙ) ρₙ) τₙ, tₙ⟩ ← infer m
      | throw $ .panic "concatenation of non-record term"
    -- TODO: generate μ as a single thing by proving μₘ = μₙ; similarly τ for τₘ = τₙ
    let rx ← fresh;
    push <| .xunivar rx (.row .star)
    let c ← constraint <| (.concat ρₘ μ ρₙ (.uvar rx))
    return ⟨Monotype.arr (.app (.prodOrSum .sum μ) (.uvar rx)) τ, .elim tₘ tₙ c⟩
  | _ => throw $ .panic "unimplemented"

-- TODO: How do we produce a typing derivation for inferApp?
partial def inferApp (σ : TypeScheme) (e : Term) : InferM TypeScheme := sorry
end
