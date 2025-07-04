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

/-- helper abbreviation -/
abbrev Set := Std.HashSet

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
| fail (message : String)
deriving Inhabited
structure InferState where
  Γ : Context
  gen : StdGen
deriving Inhabited

abbrev InferM := EStateM InferError InferState
def push (item : ContextItem) : InferM Unit := do
  let state@{ Γ .. } <- get
  set { state with Γ := item::Γ }
def fresh : InferM UniVar := do
  let state@{ gen .. } ← get
  let (n, gen) := RandomGen.next gen
  set { state with gen }
  return n
def freshType (κ : Kind): InferM Monotype := do
  let x ← fresh
  push $ .xunivar x κ
  return .uvar x
def getType (χ : TermVar) : InferM TypeScheme := do
  let { Γ .. } ← get
  let σ ← (getType' Γ χ).getDM (throw $ .panic "variable not defined")
  return σ
  where getType' (Γ : Context) (χ : TermVar) : Option TypeScheme :=
    match Γ with
    | .nil => .none
    | .cons (.termvar χ' σ) Γ' => if χ == χ' then .some σ else getType' Γ' χ
    | .cons _ Γ' => getType' Γ' χ

/-- split the context into (before, after) based on the item's position. -/
def split (item : ContextItem) : InferM (Context × Context) := do
  let { Γ .. } ← get
  let index ← Γ.idxOf? item |>.getDM (throw $ .panic s!"I was trying to find {item} in the context but it wasn't there; I could have sworn I put it there though!")
  if let (after, _::before) := Γ.splitAt index then
    return (before, after)
  else panic! "malfunction in core `List.idxOf`"
def before (item : ContextItem) : InferM Unit := do
  let state ← get
  let (before, _after) ← split item
  set { state with Γ := before }
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
  | _ => sorry

namespace rowSolver
inductive Row where
| literal : MonotypePairList → Row
| var : TypeVar → Row
| uvar : UniVar → Row
deriving Inhabited, BEq, DecidableEq, Hashable
structure RowData where
/-- The `All` constraints attached to this row. -/
all : Set Monotype
deriving Inhabited
namespace Row
  /-- Convert a row monotype into a node. Assumes ρ has kind `(.row .star)`. -/
  def fromMonotype (ρ : Monotype) : Row :=
    match ρ with
    | .row pairList _ => .literal pairList
    | .var α => .var α
    | .uvar x => .uvar x
    | _ => panic! "invalid row found in context"
end Row
inductive EdgeComm where
| literal : Comm → EdgeComm
| var : TypeVar → EdgeComm
| uvar : UniVar → EdgeComm
deriving Inhabited, BEq, Hashable, DecidableEq
namespace EdgeComm
  /-- Convert a commutativity monotype into an EdgeComm. Assumes μ has kind `.comm`. -/
  def fromMonotype (μ : Monotype) : EdgeComm :=
    match μ with
    | .comm c => .literal c
    | .var α => .var α
    | .uvar x => .uvar x
    | _ => panic! "invalid commutativity found in context"
end EdgeComm

inductive Edge where
| concat (leftChild : Row) (μ : EdgeComm) (rightChild : Row) (parent : Row)
| contain (child : Row) (μ : EdgeComm) (parent : Row)
deriving Inhabited, BEq, Hashable
structure RowGraph where
  rows : Std.HashMap Row RowData
  edges : Set Edge
deriving Inhabited
namespace RowGraph
  def empty : RowGraph := { rows := Std.HashMap.empty, edges := Std.HashSet.empty }
  /-- get the set of direct parents for the given node -/
  def parents (node : Row) (comm : EdgeComm) : ReaderM RowGraph (Set Row) := do
    let graph ← read
    return graph.edges.fold (fun acc val => match val with
    -- TODO: μ can be a subtype of comm, or maybe the other way around
      | .concat l μ r p => if (μ == comm) && (l == node || r == node) then acc.insert p else acc
      | .contain c μ p => if (μ == comm) && c == node then acc.insert p else acc
    ) Std.HashSet.empty
  /-- get the set of direct children for the given node -/
  def getChildren (row : Row) : ReaderM RowGraph (Set Row) := do
    let graph ← read
    return graph.edges.fold (fun acc val => match val with
    -- TODO: μ can be a subtype of comm, or maybe the other way around
      | .concat l _ r p => if p == row then acc.insert l |>.insert r else acc
      | .contain c _ p => if p == row then acc.insert c else acc
    ) Std.HashSet.empty
  /-- get all leaf nodes that share the given row as a common root. -/
  def getLeaves (row : Row) : ReaderM RowGraph (Set Row) := do
    let children ← getChildren row
    if children.isEmpty then return Std.HashSet.empty.insert row
    children.foldM (fun acc row => acc.union <$> getChildren row) Std.HashSet.empty
  /--
  Check if `edge₁` is associate to `edge₂`, i.e.
  `edge₁` is `lₐ o r ~ p`
  `edge₂` is `l o rₐ ~ p`
  and there exists some row `a` such that
  `lₐ` decomposes as `l o a ~ lₐ` and
  `rₐ` decomposes as `a o r ~ rₐ`.
  Essentially giving `(l o a) o r = l o (a o r)`
  -/
  def isAssociate (edge₁ : Edge) (edge₂ : Edge) : ReaderM RowGraph Bool := do
    let graph ← read;
    let Edge.concat lₐ μ r p := edge₁
      | panic! "Associativity requires concatenations"
    let Edge.concat l μ' rₐ p' := edge₂
      | panic! "Associativity requires concatenations"
    if μ != μ' || p != p' then return false
    let possibleIntermediates := graph.edges.toList.filterMap (
      match · with
      | .concat l' μ' a lₐ' => .someIf a (l' == l && μ' == μ && lₐ' == lₐ)
      | _ => .none
    );
    return graph.edges.toList.any (
      match · with
      | .concat a μ' r' rₐ' => possibleIntermediates.contains a && μ' == μ && r' == r && rₐ' == rₐ
      | _ => false
    );
  partial def generate (Γ : Context): RowGraph :=
    match Γ with
    | [] => RowGraph.empty
    | .constraint (.contain c μ p) :: Γ =>
      let graph := generate Γ
      let (c, μ, p) := (Row.fromMonotype c, EdgeComm.fromMonotype μ, Row.fromMonotype p)
      let rows := (
        let emptyData : RowData := { all := Std.HashSet.empty }
        graph.rows.insert c emptyData |>.insert p emptyData
      );
      let edges := graph.edges.insert (.contain c μ p)
      { graph with rows, edges }
    | .constraint (.concat l μ r p) :: Γ =>
      let graph := generate Γ
      let (l, μ, r, p) := (Row.fromMonotype l, EdgeComm.fromMonotype μ, Row.fromMonotype r, Row.fromMonotype p)
      let rows := (
        let emptyData : RowData := { all := Std.HashSet.empty }
        graph.rows.insert l emptyData |>.insert r emptyData |>.insert p emptyData
      )
      let edges := graph.edges.insert (.concat l μ r p)
      { graph with rows, edges }
    | .constraint (Monotype.app (.app .all ϕ) ρ) :: Γ =>
      let graph := generate Γ
      let p := Row.fromMonotype ρ
      let leaves : Set Row := getLeaves p |>.run graph
      let rows := leaves.fold (fun rows leaf => rows.alter leaf (fun data? => data?.map (fun data => { data with all := data.all.insert ϕ }))) graph.rows
      -- TODO: propogate the constraint to intermediate literal nodes as well.
      { graph with rows }
    | _ => sorry
  partial def contains (c : Row) (μ : EdgeComm) (p : Row) : ReaderM RowGraph Bool := do
    let graph ← read
    return (graph.rows.contains c)
    && (graph.rows.contains p)
    && (
      c == p || (← parents c μ).any (contains · μ p |>.run graph)
    )
  partial def concatenates (l : Row) (μ : EdgeComm) (r : Row) (p : Row) : ReaderM RowGraph Bool := do
    let graph ← read
    match l, μ, r with
    | .literal .nil, _, r => return r == p
    | l, _, .literal .nil => return l == p
    | l, μ, r =>
    if let .literal .comm := μ then
      if graph.edges.contains (.concat r μ l p) then
        return true
    return ← graph.edges.toList.anyM <| isAssociate <| Edge.concat l μ r p
  partial def alls (ϕ : Monotype) (p : Row) : ReaderM RowGraph Bool := do
    let leaves ← getLeaves p
    leaves.toList.allM (satisfies ϕ)
    where satisfies (ϕ : Monotype) (leaf : Row) : ReaderM RowGraph Bool := do
      let graph ← read
      if graph.rows.get? leaf |>.any (·.all.contains ϕ) then return true;
      -- The only hope now is that `leaf` is a literal and that its individual types satisfy the constraints.
      match leaf with
      | .literal _pairs => 
        -- TODO:
        --   check `ϕ` is satisfied for each type in `pairs`.
        --   this requires allowing for regular constraint checking inside the rowgraph context.
        return sorry
      |_ => return false
end RowGraph
end rowSolver

partial def subtype (σ₀ σ₁ : TypeScheme) : InferM (σ₀.Subtyping σ₁) := do
  if h : σ₀ = σ₁ then
    return by
      rewrite [h]
      exact .refl
  -- TODO: How the heck do we handle transitivity?
  else match σ₀, σ₁ with
  | Monotype.arr τ₀ τ₁, Monotype.arr τ₂ τ₃ =>
    let sₗ ← subtype τ₂ τ₀
    let sᵣ ← subtype τ₁ τ₃
    return sₗ.arr sᵣ
  | QualifiedType.qual ψ₀ γ₀, QualifiedType.qual ψ₁ γ₁ =>
    let sψ ← subtype ψ₁ ψ₀
    let sγ ← subtype γ₀ γ₁
    return sψ.qual sγ
  | .quant i₀ κ₀ σ₀, .quant i₁ κ₁ σ₁ =>
    if h : κ₀ = κ₁ then
      let s ← subtype σ₀ (σ₁.subst (.var i₀) i₁)
      return by
        rewrite [h]
        exact s.scheme
    else throw $ .panic "Subtype of non-compatible scheme quantifiers"
  | Monotype.app (.prodOrSum Ξ₀ μ₀) ρ₀, Monotype.app (.prodOrSum Ξ₁ μ₁) ρ₁ =>
    if hρ : ρ₀ = ρ₁ then
      if hΞ : Ξ₀ = Ξ₁ then
        if s : μ₀.CommutativityPartialOrdering μ₁ then
          return by
            rewrite [hρ, hΞ]
            exact .decay s
        else throw $ .fail "to show compatibility of commutativity"
      else throw $ .panic "Subtype of different row constructors."
    else throw $ .panic "Subtype of different rows."
  | Monotype.app (.prodOrSum .sum (.comm .comm)) (.row .nil (.some .star)), σ =>
    return .never
  | Monotype.app .list τ₀, Monotype.app .list τ₁ =>
    let s ← subtype τ₀ τ₁
    return s.list
  | _, _ => sorry
def instantiateLeft (ᾱ : UniVar) (σ : TypeScheme) : InferM Unit := sorry
def instantiateRight (σ : TypeScheme) (ᾱ : UniVar) : InferM Unit := sorry
def constraint (ψ : Monotype) : InferM (ψ.ConstraintSolution) := do
  kind ψ .constr
  match ψ with
  | .concat ρ₁ μ ρ₂ ρ₃ =>
    let { Γ .. } ← get
    let graph := rowSolver.RowGraph.generate Γ
    sorry
  | .contain ρ₁ μ ρ₂ =>
    let { Γ .. } ← get
    let graph := rowSolver.RowGraph.generate Γ
    sorry
  | _ => sorry

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
    let { Γ .. } ← get
    let σ ← getType χ
    return ⟨σ, .var⟩
  | .annot e σ =>
    let t ← check e σ
    return ⟨σ, t.annot⟩
  | .let χ σ? e e' =>
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
    let ⟨Monotype.app (.prodOrSum Ξ μ) (.row (.cons ξ τ .nil) _), t₁⟩ ← infer e₁
      | throw $ .panic "expected a singleton product or sum"
    let t₂ ← check e₂ (ξ.floor)
    return ⟨τ, t₁.unlabel⟩
  | .prod labelledTerms =>
    by
      rw [← TermPairList.ofList_left_inv_toList (MNs := labelledTerms)]
      exact do
      let x : (ξτs : List (Monotype × Monotype)) ×
        ∀ MNξτ ∈ labelledTerms.toList.zip ξτs, let ((_, N), _, τ) := MNξτ; N.Typing τ ← by
        induction labelledTerms.toList with
        | nil => exact return ⟨[], nofun⟩
        | cons MN tail ih =>
          exact do
          let ⟨ξτs, h⟩ ← ih
          let ⟨.qual $ .mono ξ, _⟩ ← infer MN.fst -- TODO: Check that ξ has kind label, evaluate lam apps?
            | throw $ .panic "expected a monotype for the label"
          let ⟨.qual $ .mono τ, t⟩ ← infer MN.snd
            | throw $ .panic "expected a monotype in the row"
          return by
            refine ⟨(ξ, τ) :: ξτs, ?h⟩
            intro MNξτ mem
            let ((M', N'), ξ', τ') := MNξτ
            rw [List.zip_cons_cons] at mem
            simp only
            exact if h' : MN.snd = N' ∧ τ = τ' then by
                rcases h' with ⟨rfl, rfl⟩
                exact t
              else by
                let mem' : ((M', N'), ξ', τ') ∈ tail.zip ξτs := by
                  match mem with
                  | .head _ => match Classical.not_and_iff_or_not_not.mp h' with
                    | .inl h'' => nomatch h''
                    | .inr h'' => nomatch h''
                  | .tail _ mem' => exact mem'
                exact h _ mem'
      return ⟨
        (Monotype.prodOrSum .prod (.comm .non)).app (.row (.ofList x.fst) none),
        Term.Typing.prod x.snd
      ⟩
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
    let μ ← freshType .comm
    let ρₘ ← freshType (.row .star)
    let tₘ ← check m (Monotype.prodOrSum .prod μ |>.app ρₘ)
    let ρₙ ← freshType (.row .star)
    let tₙ ← check n (Monotype.prodOrSum .prod μ |>.app ρₙ)
    let ρ ← freshType (.row .star)
    let c ← constraint <| .concat ρₘ μ ρₙ ρ
    return ⟨_, .concat tₘ tₙ c⟩
  | .elim m n =>
    let μ ← freshType .comm
    let τ ← freshType .star
    let ρₘ ← freshType (.row .star)
    let tₘ ← check m (Monotype.prodOrSum .sum μ |>.app ρₘ |>.arr τ)
    let ρₙ ← freshType (.row .star)
    let tₙ ← check n (Monotype.prodOrSum .sum μ |>.app ρₙ |>.arr τ)
    let ρ ← freshType (.row .star)
    let c ← constraint <| (.concat ρₘ μ ρₙ ρ)
    return ⟨_, tₘ.elim tₙ c⟩
  | .member _ => throw $ .panic "unimplemented"
  | .ind ϕ ρ l t rn ri rp M N => throw $ .panic "unimplemented"
  | .splitₚ ϕ e =>
    let ⟨Monotype.app (.prodOrSum .prod (.comm .comm)) ρ, t⟩ ← infer e
      | throw $ .panic "invalid splitₚ"
    let ρ₁ ← freshType (.row .star)
    let ρ₂ ← freshType (.row .star)
    let c ← constraint (Monotype.split |>.app ϕ |>.app ρ₁ |>.app ρ₂ |>.app ρ)
    return ⟨_, t.splitₚ c⟩
  | .splitₛ ϕ e₁ e₂ =>
    let τ ← freshType .star
    let ρ₁ ← freshType (.row .star)
    let t₁ ← check e₁ <| Monotype.arr (.app (.prodOrSum .sum (.comm .comm)) (.app (.app .lift ϕ) ρ₁)) τ
    let ρ₂ ← freshType (.row .star)
    let t₂ ← check e₂ <| Monotype.prodOrSum .sum (.comm .comm) |>.app ρ₂ |>.arr τ
    let ρ₃ ← freshType (.row .star)
    let c ← constraint (Monotype.split |>.app ϕ |>.app ρ₁ |>.app ρ₂ |>.app ρ₃)
    return ⟨_, t₁.splitₛ t₂ c⟩
  | .nil =>
    let τ ← freshType .star
    return ⟨_, Term.Typing.nil (τ := τ)⟩
  | .cons e₁ e₂ =>
    -- NOTE: Not sure if the order matters here, but this seems natural.
    let ⟨.qual $ .mono τ₁, t₁⟩ ← infer e₁
      | throw $ .panic "cons applied to non-monotype"
    let t₂ ← check e₂ (Monotype.list.app τ₁)
    return ⟨_, t₁.cons t₂⟩
  | .fold =>
    return ⟨_, Term.Typing.fold⟩
  | .int n =>
    return ⟨_, Term.Typing.int⟩
  | .op _ e₁ e₂ =>
    let t₁ ← check e₁ Monotype.int
    let t₂ ← check e₂ Monotype.int
    return ⟨_, t₁.op t₂⟩
  | .range =>
    return ⟨_, Term.Typing.range⟩
  | .str s =>
    return ⟨_, Term.Typing.str⟩
  | .def s =>
    let ex ← fresh
    return ⟨_, Term.Typing.def (σ := Monotype.uvar ex)⟩
  | .throw =>
    let ex ← fresh
    return ⟨_, Term.Typing.throw (σ := Monotype.uvar ex)⟩

-- TODO: How do we produce a typing derivation for inferApp?
partial def inferApp (σ : TypeScheme) (e : Term) : InferM TypeScheme := sorry
end
