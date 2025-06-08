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

inductive ContextItem where
| typevar (α : TypeVar) (κ : Kind)
| termvar (χ : TermVar) (σ : TypeScheme)
| xunivar (ᾱ : UniVar) (κ : Kind)
| sunivar (ᾱ : UniVar) (τ : Monotype)
| mark (ᾱ : UniVar)
deriving Inhabited

abbrev Context := List ContextItem

inductive InferError where
| panic (message : String)
structure InferState where Γ : Context

abbrev InferM := EStateM InferError InferState

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

def check (e : Term) (σ : TypeScheme) : InferM (e.Typing σ) := sorry
def infer (e : Term) : InferM ((σ : TypeScheme) × e.Typing σ) := sorry
-- TODO: How do we produce a typing derivation for inferApp?
def inferApp (σ : TypeScheme) (e : Term) : InferM TypeScheme := sorry



