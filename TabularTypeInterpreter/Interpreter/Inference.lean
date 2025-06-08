import TabularTypeInterpreter.Interpreter.Basic
import TabularTypeInterpreter.Interpreter.Elaboration

namespace TabularTypeInterpreter.Interpreter.Inference

-- Some placeholders for now:
/-- type variables -/
abbrev TypeVar := TId
/-- term variables -/
abbrev TermVar := Nat
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
deriving Inhabited

instance : ToString ContextItem where toString
| .typevar α κ => s!"{α} : {κ}"
| .termvar χ σ => s!"{χ} : {σ.toString}"
| .xunivar ᾱ κ => s!"{ᾱ} : {κ}"
| .sunivar ᾱ τ => s!"{ᾱ} = {τ.toString}"
| .mark ᾱ => s!"mark {ᾱ}"

/-- Equivalence for context items is entirely determined by the variable, since each must be uniquely declared.
I believe we could derive this instance, but I want to be explicit just in case.
-/
instance : BEq ContextItem where beq
| .typevar α₀ _, .typevar α₁ _ => α₀ == α₁
| .termvar χ₀ _, .termvar χ₁ _ => χ₀ == χ₁
| .xunivar ᾱ₀ _, .xunivar ᾱ₁ _ => ᾱ₀ == ᾱ₁
| .sunivar ᾱ₀ _, .xunivar ᾱ₁ _ => ᾱ₀ == ᾱ₁
| .mark ᾱ₀, .mark ᾱ₁ => ᾱ₀ == ᾱ₁
| _, _ => false

abbrev Context := List ContextItem

inductive InferError where
| panic (message : String)
structure InferState where Γ : Context

abbrev InferM := EStateM InferError InferState
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



def wellFormedType (σ : TypeScheme) : InferM Unit := do 
  let { Γ .. } <- get
  match σ with
  | .qual $ .mono $ .var α₀ =>
    if Γ.any (match · with | .typevar α _ => α == α₀ | _ => false) then return
    else throw $ .panic "TODO need descriptive text here"
  | _ => throw $ .panic "TODO unimplemented variant"

def wellFormedContext : InferM Unit := sorry

def subtype (σ₀ σ₁ : TypeScheme) : InferM Unit := sorry
def instantiateLeft (ᾱ : UniVar) (σ : TypeScheme) : InferM Unit := sorry
def instantiateRight (σ : TypeScheme) (ᾱ : UniVar) : InferM Unit := sorry

def check (e : Term) (σ : TypeScheme) : InferM (e.Typing σ) := do
  match σ with
  | .quant α κ σbody =>
    let decl : ContextItem := (.typevar α κ)
    push decl
    let t ← check e σbody
    let (before, _after) ← split decl
    set ({ Γ := before } : InferState)
    return t.schemeI
  | _ => throw $ .panic "TODO"
def infer (e : Term) : InferM ((σ : TypeScheme) × e.Typing σ) := sorry
-- TODO: How do we produce a typing derivation for inferApp?
def inferApp (σ : TypeScheme) (e : Term) : InferM TypeScheme := sorry



