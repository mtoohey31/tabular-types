import TabularTypeInterpreter.Interpreter.Basic
import TabularTypeInterpreter.Interpreter.Elaboration
import TabularTypeInterpreter.Interpreter.Resolution

namespace TabularTypeInterpreter.Interpreter.Inference

/-- helper abbreviation -/
abbrev Set := Std.HashSet

/--
The context under which the algorithm is evaluated.
Each type, term or existential variable can have at most a single declaration in the context.
Furthermore, the context is ordered; entries earlier in the context can not refer to later entries.
-/
inductive ContextItem where
  | typevar (α : TId) (κ : Kind)
  | termvar (χ : MId) (σ : TypeScheme)
  | xunivar (ᾱ : UId) (κ : Kind)
  | sunivar (ᾱ : UId) (τ : Monotype)
  | mark (ᾱ : UId)
  | constraint (ψ : Monotype)
deriving Inhabited

instance : ToString ContextItem where
  toString
    | .typevar α κ => s!"{α} : {κ}"
    | .termvar χ σ => s!"{χ} : {σ.toString}"
    | .xunivar ᾱ κ => s!"u{ᾱ} : {κ}"
    | .sunivar ᾱ τ => s!"u{ᾱ} = {τ.toString}"
    | .mark ᾱ => s!"mark u{ᾱ}"
    | .constraint ψ => toString ψ

/-- Equivalence for context items is entirely determined by the variable, since each must be uniquely declared.
I believe we could derive this instance, but I want to be explicit just in case.
-/
instance : BEq ContextItem where
  beq
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

instance : ToString InferError where
  toString
    | .panic msg => s!"panic: {msg}"
    | .fail msg => s!"fail: {msg}"

structure InferState where
  prog : Program
  nextFresh : Nat

abbrev InferM := EStateM InferError InferState

def fresh : InferM UId := do
  let { nextFresh, .. } ← getModify fun st => { st with nextFresh := st.nextFresh.succ }
  return { val := nextFresh }

def freshType (Γ : Context) (κ : Kind) : InferM (Context × Monotype) := do
  let α ← fresh
  return ((.xunivar α κ)::Γ, .uvar α)

-- TODO: Failures to find things should probably `panic!` since this should be caught by the parser.
set_option linter.deprecated false in
def getClassByName (name : String) : InferM ClassDeclaration := do
  let { prog .. } ← get
  let decl? := prog.firstM (match · with | .class decl@{TC ..} => Option.someIf decl (name == TC) | _ => Option.none)
  let .some decl := decl?
    | throw $ .panic s!"unknown typeclass `{name}`"
  return decl

def getClass (method : String) : InferM ClassDeclaration := do
  let { prog .. } ← get
  let decl? := prog.firstM (match · with | .class decl@{m ..} => Option.someIf decl (method == m) | _ => Option.none)
  let .some decl := decl?
    | throw $ .panic s!"unknown typeclass method `{method}`"
  return decl

def getTypeAlias («alias» : String) : InferM TypeScheme := do
  let { prog .. } ← get
  let decl? := prog.firstM (match · with | .typeAlias a σ => Option.someIf σ («alias» == a) | _ => Option.none)
  let .some decl := decl?
    | throw $ .panic s!"unknown type alias `{«alias»}`"
  return decl

def getKind (Γ : Context) (a : TId) : InferM Kind := do
  let κ ← (getKind' Γ a).getDM (throw $ .panic "type variable not defined")
  return κ
where
  getKind' (Γ : Context) (a : TId) : Option Kind :=
    match Γ with
    | .nil => .none
    | .cons (.typevar a' κ) Γ' => if a == a' then .some κ else getKind' Γ' a
    | .cons _ Γ' => getKind' Γ' a

def getType (Γ : Context) (χ : MId) : InferM TypeScheme := do
  let σ ← (getType' Γ χ).getDM (throw $ .panic "variable not defined")
  return σ
where
  getType' (Γ : Context) (χ : MId) : Option TypeScheme :=
    match Γ with
    | .nil => .none
    | .cons (.termvar χ' σ) Γ' => if χ == χ' then .some σ else getType' Γ' χ
    | .cons _ Γ' => getType' Γ' χ

def lookupUniVar (ᾱ : UId) : Context → Option ContextItem
  | .nil => .none
  | .cons item@(.xunivar ᾱ' _κ) Γ => if ᾱ == ᾱ' then .some item else lookupUniVar ᾱ Γ
  | .cons item@(.sunivar ᾱ' _τ) Γ => if ᾱ == ᾱ' then .some item else lookupUniVar ᾱ Γ
  | .cons _ Γ => lookupUniVar ᾱ Γ

/-- split the context into (before, after) based on the item's position. -/
def split (Γ : Context) (item : ContextItem) : InferM (Context × Context) := do
  let index ← Γ.idxOf? item |>.getDM (throw $ .panic s!"I was trying to find {item} in the context but it wasn't there; I could have sworn I put it there though!")
  if let (after, _::before) := Γ.splitAt index then
    return (before, after)
  else panic! "malfunction in core `List.idxOf`"

mutual

partial
def inferKind (Γ : Context) (σ : TypeScheme) : InferM Kind := open Monotype in do
  match σ with
  | .quant i κ₀ σ' => inferKind ((.typevar i κ₀)::Γ) σ'
  | QualifiedType.qual ψ γ =>
    checkKind Γ ψ .constr
    inferKind Γ γ
  | var i => getKind Γ i
  | uvar α =>
    let some κ? ← List.head? <$> Γ.filterMapM fun
        | .xunivar α' κ => return if α = α' then some κ else none
        | .sunivar α' τ => if α = α' then some <$> inferKind Γ τ else return none
        | _ => return none
      | throw <| .panic "couldn't find uvar in context"
    return κ?
  | lam i κ₀ τ =>
    let κ₁ ← inferKind ((.typevar i κ₀)::Γ) τ
    return κ₀.arr κ₁
  | app τ₀ τ₁ =>
    let .arr κ₀ κ₁ ← inferKind Γ τ₀ | throw <| .panic "type application of type with non-arrow kind"
    checkKind Γ τ₁ κ₀
    return κ₁
  | arr τ₀ τ₁ =>
    checkKind Γ τ₀ .star
    checkKind Γ τ₁ .star
    return .star
  | label _ => return .label
  | floor ξ =>
    checkKind Γ ξ .label
    return .star
  | comm _ => return .comm
  | row ξτs κ? =>
    let κs ← ξτs.mapMemM fun (ξ, τ) _ => do
      checkKind Γ ξ .label
      inferKind Γ τ
    if let some κ := κ? then
      for (κ', i) in κs.zipIdx do
        if κ ≠ κ' then
          throw <| .panic s!"expected all row entries to have annotation kind {κ}, but the entry at index {i} had kind {κ'}"
      return .row κ
    else
      match κs with
      | [] =>
        throw <| .panic "empty rows must have a ': κ' kind annotation"
      | κ :: κs' =>
        for (κ', i) in κs'.zipIdx do
          if κ ≠ κ' then
            throw <| .panic s!"expected all row entries to have the same kind {κ}, but the entry at index {i + 1} had kind {κ'}"
        return .row κ
  | prodOrSum _ μ =>
    checkKind Γ μ .comm
    return .arr (.row .star) .star
  | lift ϕ =>
    let .arr κ₀ κ₁ ← inferKind Γ ϕ | throw <| .panic "lift by type with non-arrow kind"
    return .arr (.row κ₀) (.row κ₁)
  | contain ρ₀ μ ρ₁ =>
    let .row κ₀ ← inferKind Γ ρ₀ | throw <| .panic "contain of type with non-row kind"
    checkKind Γ μ .comm
    let .row κ₁ ← inferKind Γ ρ₁ | throw <| .panic "contain of type with non-row kind"
    if κ₀ ≠ κ₁ then
      throw <| .panic s!"inner kind of contained row {κ₀} does not match containing row's inner kind {κ₁}"
    return .constr
  | concat ρ₀ μ ρ₁ ρ₂ =>
    let .row κ₀ ← inferKind Γ ρ₀ | throw <| .panic "contain of type with non-row kind"
    checkKind Γ μ .comm
    let .row κ₁ ← inferKind Γ ρ₁ | throw <| .panic "contain of type with non-row kind"
    let .row κ₂ ← inferKind Γ ρ₂ | throw <| .panic "contain of type with non-row kind"
    if κ₀ ≠ κ₂ then
      throw <| .panic s!"inner kind of left row {κ₀} does not match concatenated row's inner kind {κ₂}"
    if κ₁ ≠ κ₂ then
      throw <| .panic s!"inner kind of right row {κ₁} does not match concatenated row's inner kind {κ₂}"
    return .constr
  | tc s =>
    let _ ← getClassByName s
    return .constr
  | all ϕ =>
    let .arr κ₀ κ₁ ← inferKind Γ ϕ | throw <| .panic "all with type with non-arrow kind"
    if κ₁ ≠ .constr then
      throw <|
        .panic s!"expected all type function to have return type {Kind.constr}, got kind '{κ₁}'"
    return .arr (.row κ₀) .constr
  | ind ρ =>
    let .row _ ← inferKind Γ ρ | throw <| .panic "ind of non-row kind"
    return .constr
  | Monotype.split ϕ ρ₀ ρ₁ ρ₂ =>
    let .arr κ₀ κ₁ ← inferKind Γ ϕ | throw <| .panic "split by type with non-arrow kind"
    let .row κ₂ ← inferKind Γ ρ₀ | throw <| .panic "split of type with non-row kind"
    let .row κ₃ ← inferKind Γ ρ₁ | throw <| .panic "split of type with non-row kind"
    let .row κ₄ ← inferKind Γ ρ₂ | throw <| .panic "split of type with non-row kind"
    if κ₀ ≠ κ₂ then
      throw <| .panic s!"inner kind of left row {κ₂} does not match lift function's parameter kind {κ₀}"
    if κ₁ ≠ κ₃ then
      throw <| .panic s!"inner kind of right row {κ₃} does not match lift function's result kind {κ₁}"
    if κ₁ ≠ κ₄ then
      throw <| .panic s!"inner kind of concatenated row {κ₄} does not match lift function's result kind {κ₁}"
    return .constr
  | list => return .arr .star .star
  | int | str => return .star
  | «alias» a =>
    let σ' ← getTypeAlias a
    inferKind Γ σ'

partial
def checkKind (Γ : Context) (σ : TypeScheme) (κ₀ : Kind) : InferM Unit := do
  let κ₁ ← inferKind Γ σ
  if κ₀ ≠ κ₁ then
    throw <| .panic s!"expected type of kind '{κ₀}', got type of kind '{κ₁}'"

end

namespace rowSolver
structure RowData where
/-- The `All` constraints attached to this row. -/
all : Set Monotype
deriving Inhabited
inductive Edge where
| concat (ρ₁ : Monotype) (μ : Monotype) (ρ₂ : Monotype) (ρ₃ : Monotype) (solution : (Monotype.concat ρ₁ μ ρ₂ ρ₃).ConstraintSolution)
| contain (ρ₁ : Monotype) (μ : Monotype) (ρ₂ : Monotype) (solution : (Monotype.contain ρ₁ μ ρ₂).ConstraintSolution)
instance : BEq Edge where beq
| .concat ρ₁ μ ρ₂ ρ₃ _, .concat ρ₁' μ' ρ₂' ρ₃' _ => ρ₁ == ρ₁' && μ == μ' && ρ₂ == ρ₂' && ρ₃ == ρ₃'
| .contain ρ₁ μ ρ₂ _, .contain ρ₁' μ' ρ₂' _ => ρ₁ == ρ₁' && μ == μ' && ρ₂ == ρ₂'
| _, _ => false
instance : Hashable Edge where hash
| .concat ρ₁ μ ρ₂ ρ₃ _ => hash [hash ρ₁, hash μ, hash ρ₂, hash ρ₃]
| .contain ρ₁ μ ρ₂ _ => hash [hash ρ₁, hash μ, hash ρ₂]
structure RowGraph where
  rows : Std.HashMap Monotype RowData
  edges : Set Edge
deriving Inhabited
namespace RowGraph
  def empty : RowGraph := { rows := Std.HashMap.empty, edges := Std.HashSet.empty }
  /-- get the set of direct parents for the given node -/
  def parents (ρ : Monotype) (μ : Monotype) : ReaderM RowGraph (Set Monotype) := do
    let graph ← read
    return graph.edges.fold (fun acc val => match val with
    -- TODO: μ can be a subtype of comm, or maybe the other way around
      | .concat l μ' r p _ => if (μ' == μ) && (l == ρ || r == ρ) then acc.insert p else acc
      | .contain c μ' p _ => if (μ' == μ) && c == ρ then acc.insert p else acc
    ) Std.HashSet.empty
  /-- get the set of direct children for the given node -/
  def getChildren (row : Monotype) : ReaderM RowGraph (Set Monotype) := do
    let graph ← read
    return graph.edges.fold (fun acc val => match val with
    -- TODO: μ can be a subtype of comm, or maybe the other way around
      | .concat l _ r p _ => if p == row then acc.insert l |>.insert r else acc
      | .contain c _ p _ => if p == row then acc.insert c else acc
    ) Std.HashSet.empty
  /-- get all leaf nodes that share the given row as a common root. -/
  def getLeaves (ρ : Monotype) : ReaderM RowGraph (Set Monotype) := do
    let children ← getChildren ρ
    if children.isEmpty then return Std.HashSet.empty.insert ρ
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
    let Edge.concat lₐ μ r p _ := edge₁
      | panic! "Associativity requires concatenations"
    let Edge.concat l μ' rₐ p' _ := edge₂
      | panic! "Associativity requires concatenations"
    if μ != μ' || p != p' then return false
    let possibleIntermediates := graph.edges.toList.filterMap (
      match · with
      | .concat l' μ' a lₐ' _ => .someIf a (l' == l && μ' == μ && lₐ' == lₐ)
      | _ => .none
    );
    return graph.edges.toList.any (
      match · with
      | .concat a μ' r' rₐ' _ => possibleIntermediates.contains a && μ' == μ && r' == r && rₐ' == rₐ
      | _ => false
    );
  partial def generate (Γ : Context): RowGraph :=
    secondPass (firstPass RowGraph.empty Γ) Γ
  where
    firstPass (graph : RowGraph) (Γ : Context) : RowGraph :=
      match Γ with
      | .constraint (.contain c μ p) :: Γ =>
        let graph := firstPass graph Γ
        let rows := (
          let emptyData : RowData := { all := Std.HashSet.empty }
          graph.rows.insert c emptyData |>.insert p emptyData
        );
        let edges := graph.edges.insert (.contain c μ p sorry)
        { graph with rows, edges }
      | .constraint (.concat l μ r p) :: Γ =>
        let graph := firstPass graph Γ
        let rows := (
          let emptyData : RowData := { all := Std.HashSet.empty }
          graph.rows.insert l emptyData |>.insert r emptyData |>.insert p emptyData
        )
        let edges := graph.edges.insert (.concat l μ r p sorry)
        { graph with rows, edges }
      | _ => graph
    secondPass (graph : RowGraph) (Γ : Context) : RowGraph :=
      match Γ with
      | .constraint (Monotype.app (.all ϕ) ρ) :: Γ =>
        let graph := secondPass graph Γ
        let leaves : Set Monotype := getLeaves ρ |>.run graph
        let rows := leaves.fold (fun rows leaf => rows.alter leaf (fun data? => data?.map (fun data => { data with all := data.all.insert ϕ }))) graph.rows
        -- TODO: propogate the constraint to intermediate literal nodes as well.
        { graph with rows }
      | _ => graph

    partial def contains (ρ₁ : Monotype) (μ : Monotype) (ρ₂ : Monotype) : ReaderM RowGraph (Option (Monotype.contain ρ₁ μ ρ₂).ConstraintSolution) := do
      let graph ← read
      let childrenOfρ₂ : List ((child : Monotype) × (Monotype.contain child μ ρ₂).ConstraintSolution) :=
        graph.edges.toList.foldl (fun children edge =>
          match edge with
          | .concat cl μ' cr ρ s =>
            if hρ : ρ₂ = ρ then
              if hμ : μ = μ' then
                by rewrite [hρ, hμ]; exact ⟨cl, s.concatContainL⟩::⟨cr, s.concatContainR⟩::(by rewrite [hμ.symm, hρ.symm]; exact children)
              else children
            else children
          | .contain c μ' ρ s =>
            if hρ : ρ₂ = ρ then
              if hμ : μ = μ' then
                by rewrite [hρ, hμ]; exact ⟨c, s⟩::(by rewrite [hμ.symm, hρ.symm]; exact children)
              else children
            else children
        ) []
      for ⟨child, sol₂⟩ in childrenOfρ₂ do
        if let .some sol₁ ← contains ρ₁ μ child then
          return sol₁.containTrans sol₂
      return .none
  partial def concatenates (ρ₁ : Monotype) (μ : Monotype) (ρ₂ : Monotype) (ρ₃ : Monotype) : ReaderM RowGraph (Option (Monotype.concat ρ₁ μ ρ₂ ρ₃).ConstraintSolution) := do
    let graph ← read
    return sorry
    -- match l, μ, r with
    -- | .literal .nil, _, r => return r == p
    -- | l, _, .literal .nil => return l == p
    -- | l, μ, r =>
    -- if let .literal .comm := μ then
    --   if graph.edges.contains (.concat r μ l p) then
    --     return true
    -- return ← graph.edges.toList.anyM <| isAssociate <| Edge.concat l μ r p
  partial def alls (ϕ : Monotype) (p : Monotype) : ReaderM RowGraph (Option (Monotype.all ϕ |>.app ρ).ConstraintSolution) := do
    return sorry
    -- let leaves ← getLeaves p
    -- leaves.toList.allM (satisfies ϕ)
    -- where satisfies (ϕ : Monotype) (leaf : Monotype) : ReaderM RowGraph Bool := do
    --   let graph ← read
    --   if graph.rows.get? leaf |>.any (·.all.contains ϕ) then return true;
    --   -- The only hope now is that `leaf` is a literal and that its individual types satisfy the constraints.
    --   match leaf with
    --   | .literal _pairs =>
    --     -- TODO:
    --     --   check `ϕ` is satisfied for each type in `pairs`.
    --     --   this requires allowing for regular constraint checking inside the rowgraph context.
    --     return sorry
    --   |_ => return false
end RowGraph
end rowSolver

def rowEquivalence (Γ : Context) (ρ₀ μ ρ₁ : Monotype) : InferM (Context × (ρ₀.RowEquivalence μ ρ₁)) := do
  if h : ρ₀ = ρ₁ then
    return ⟨Γ, by cases h; exact .refl⟩

  match ρ₀, ρ₁ with
  | .app (.lift ϕ₀) (.row ξτs₀ κ₀?), .app (.lift ϕ₁) (.row ξτs₁ κ₁?) =>
    if h : (ξτs₀.map fun (ξ, τ) => (ξ, ϕ₀.app τ)) = ξτs₁.map fun (ξ, τ) => (ξ, ϕ₁.app τ) then
      return ⟨Γ, by
        refine .trans .liftL ?_ (ρ₁ := .row (ξτs₀.map fun (ξ, τ) => (ξ, ϕ₀.app τ)) κ₀?)
        rw [h]
        exact .liftR⟩
    else if h' : μ = .comm .comm ∧
        @List.isPerm _ instBEqOfDecidableEq (ξτs₀.map fun (ξ, τ) => (ξ, ϕ₀.app τ))
          (ξτs₁.map fun (ξ, τ) => (ξ, ϕ₁.app τ)) then
      return ⟨Γ, by
        rcases h' with ⟨rfl, perm⟩
        exact .trans .liftL <|
          .trans (.comm (List.isPerm_iff.mp perm) (κ₀? := κ₀?) (κ₁? := κ₁?)) .liftR⟩
    else
      throw <| .panic s!"{ρ₀} is not equivalent to {ρ₁} with respect to {μ}"
  | .app (.lift ϕ) (.row ξτs₀ κ₀?), .row ξτs₁ κ₁? =>
    if h : (ξτs₀.map fun (ξ, τ) => (ξ, ϕ.app τ)) = ξτs₁ then
      return ⟨Γ, by cases h; exact .liftL⟩
    else if h' : μ = .comm .comm ∧
        @List.isPerm _ instBEqOfDecidableEq (ξτs₀.map fun (ξ, τ) => (ξ, ϕ.app τ)) ξτs₁ then
      return ⟨Γ, by
        let ⟨eq, perm⟩ := h'
        cases eq
        exact .trans .liftL (.comm (List.isPerm_iff.mp perm) (κ₀? := κ₀?))⟩
    else
      throw <| .panic s!"{ρ₀} is not equivalent to {ρ₁} with respect to {μ}"
  | .row ξτs₀ _, .app (.lift ϕ) (.row ξτs₁ κ₁?) =>
    if h : ξτs₀ = ξτs₁.map fun (ξ, τ) => (ξ, ϕ.app τ) then
      return ⟨Γ, by cases h; exact .liftR⟩
    else if h' : μ = .comm .comm ∧
        @List.isPerm _ instBEqOfDecidableEq ξτs₀ (ξτs₁.map fun (ξ, τ) => (ξ, ϕ.app τ)) then
      return ⟨Γ, by
        rcases h' with ⟨rfl, perm⟩
        exact .trans (.comm (List.isPerm_iff.mp perm) (κ₁? := κ₁?)) .liftR⟩
    else
      throw <| .panic s!"{ρ₀} is not equivalent to {ρ₁} with respect to {μ}"
  | .row ξτs₀ _, .row ξτs₁ _ =>
    if h : μ = .comm .comm ∧ @List.isPerm _ instBEqOfDecidableEq ξτs₀ ξτs₁ then
      return ⟨Γ, by
        rcases h with ⟨rfl, perm⟩
        exact .comm <| List.isPerm_iff.mp perm⟩
    else
      throw <| .panic s!"{ρ₀} is not equivalent to {ρ₁} with respect to {μ}"
  | _, _ =>
    throw <| .panic "non-equal and non (optionally lifted) concrete rows are not equivalent"

attribute [refl] TypeScheme.Subtyping.refl

def instantiateLeft (ᾱ : UniVar) (σ : TypeScheme) : InferM Unit := sorry

def instantiateRight (σ : TypeScheme) (ᾱ : UniVar) : InferM Unit := sorry

mutual

partial
def rowEquivalenceAndSubtyping (Γ : Context) (ρ₀ μ ρ₁ : Monotype)
  : InferM ((Γout : Context) × (TypeScheme.Subtyping (Monotype.app (Monotype.prodOrSum Ξ μ) ρ₀)
      (Monotype.app (Monotype.prodOrSum Ξ μ) ρ₁))) := sorry

partial
def subtype (Γ : Context) (σ₀ σ₁ : TypeScheme) : InferM ((Γout : Context) × σ₀.Subtyping σ₁) :=
  open TypeScheme in open Monotype in do
  if h : σ₀ = σ₁ then
    return ⟨Γ, by rw [h]⟩
  match σ₀, σ₁ with
  | quant i κ σ₀', σ₁ =>
    let α ← fresh
    let ⟨Γout, st⟩ ← subtype ((.mark α)::(.xunivar α κ)::Γ) (σ₀'.subst (.uvar α) i) σ₁
    return ⟨Γout, st.schemeL⟩
  | σ₀, quant i κ σ₁' =>
    let ⟨Γout, st⟩ ← subtype ((.typevar i κ)::Γ) σ₀ σ₁'
    return ⟨Γout, st.schemeR⟩
  | uvar ᾱ, σ₁ =>
    -- TODO: Account for substitutions in the return type or something so that these can work?
    instantiateLeft ᾱ σ₁
    sorry
  | σ₀, uvar ᾱ =>
    instantiateRight σ₁ ᾱ
    sorry
  | arr τ₀ τ₁, arr τ₂ τ₃ =>
    let ⟨Γ', sₗ⟩ ← subtype Γ τ₂ τ₀
    let ⟨Γout, sᵣ⟩ ← subtype Γ' τ₁ τ₃
    return ⟨Γout, sₗ.arr sᵣ⟩
  | QualifiedType.qual ψ₀ γ₀, QualifiedType.qual ψ₁ γ₁ =>
    let ⟨Γ', sψ⟩ ← subtype Γ ψ₁ ψ₀
    let ⟨Γout, sγ⟩ ← subtype Γ' γ₀ γ₁
    return ⟨Γout, sψ.qual sγ⟩
  | app (prodOrSum .sum μ) (row [] (some .star)), σ => return ⟨Γ, .trans (.decay .comm) .never⟩
  | app (prodOrSum Ξ₀ μ₀) ρ₀, app (prodOrSum Ξ₁ μ₁) ρ₁ =>
    if hΞ : Ξ₀ = Ξ₁ then
      if hμ : μ₀.CommutativityPartialOrdering μ₁ then
        let ⟨Γout, Ξμ₁ρ₀₁st⟩ ← rowEquivalenceAndSubtyping Γ ρ₀ μ₁ ρ₁ (Ξ := Ξ₀)
        return ⟨Γout, by cases hΞ; exact .trans (.decay hμ) Ξμ₁ρ₀₁st⟩
      else
        throw $ .fail "to show compatibility of commutativity"
    else
      throw $ .panic "Subtype of different row constructors"
  | contain ρ₀ μ₀ ρ₁, contain ρ₂ μ₁ ρ₃ =>
    if h : μ₀ = μ₁ then
      let ⟨Γ', ρ₀₂re⟩ ← rowEquivalence Γ ρ₀ μ₀ ρ₂
      let ⟨Γout, ρ₁₃re⟩ ← rowEquivalence Γ' ρ₁ μ₀ ρ₃
      return ⟨Γout, by cases h; exact .contain ρ₀₂re ρ₁₃re⟩
    else
      -- TODO: Should we allow decay here and below?
      throw <| .panic "subtype of contain constraints with different commutatitvity"
  | concat ρ₀ μ₀ ρ₁ ρ₂, concat ρ₃ μ₁ ρ₄ ρ₅ =>
    if h : μ₀ = μ₁ then
      let ⟨Γ', ρ₀₃re⟩ ← rowEquivalence Γ ρ₀ μ₀ ρ₃
      let ⟨Γ'', ρ₁₄re⟩ ← rowEquivalence Γ' ρ₁ μ₀ ρ₄
      let ⟨Γout, ρ₂₅re⟩ ← rowEquivalence Γ'' ρ₂ μ₀ ρ₅
      return ⟨Γout, by cases h; exact .concat ρ₀₃re ρ₁₄re ρ₂₅re⟩
    else
      throw <| .panic "subtype of contain constraints with different commutatitvity"
  | app (all ϕ₀) ρ₀, app (all ϕ₁) ρ₁ =>
    if h : ϕ₀ = ϕ₁ then
      let ⟨Γout, ρ₀₁re⟩ ← rowEquivalence Γ ρ₀ (comm .comm) ρ₁
      return ⟨Γout, by cases h; exact .all ρ₀₁re⟩
    else
      throw <| .panic "subtype of all constraints with different constraint function"
  | Monotype.split ϕ₀ ρ₀ ρ₁ ρ₂, Monotype.split ϕ₁ ρ₃ ρ₄ ρ₅ =>
    if h : ϕ₀ = ϕ₁ then
      let ⟨Γout, st⟩ ← subtype Γ (concat ((lift ϕ₀).app ρ₀) (comm .comm) ρ₁ ρ₂)
        (concat ((lift ϕ₀).app ρ₃) (comm .comm) ρ₄ ρ₅)
      return ⟨Γout, by cases h; exact st.split⟩
    else
      throw <| .panic "subtype of split constraints with different function"
  | app list τ₀, app list τ₁ =>
    let ⟨Γout, s⟩ ← subtype Γ τ₀ τ₁
    return ⟨Γout, s.list⟩
  | σ₀, σ₁ => throw <| .panic s!"expected type {σ₁}, got type: {σ₀}"

end

def constraint (Γ : Context) (ψ : Monotype) : InferM (Context × ψ.ConstraintSolution) := do
  checkKind Γ ψ .constr
  match ψ with
  | .concat ρ₁ μ ρ₂ ρ₃ =>
    let graph := rowSolver.RowGraph.generate Γ
    let .some solution := graph.concatenates ρ₁ μ ρ₂ ρ₃
      | throw $ .fail s!"Could not prove concatenation constraint `{ψ}`"
    return ⟨Γ, solution⟩
  | .contain ρ₁ μ ρ₂ =>
    let graph := rowSolver.RowGraph.generate Γ
    let .some solution := graph.contains ρ₁ μ ρ₂
      | throw $ .fail s!"Could not prove containment constraint `{ψ}`"
    return ⟨Γ, solution⟩
  | .app (.all ϕ) ρ =>
    let graph := rowSolver.RowGraph.generate Γ
    let .some solution := graph.alls ϕ ρ
      | throw $ .fail s!"Could not prove constraint `{ψ}`"
    return ⟨Γ, solution⟩
  | _ => throw $ .fail s!"Proving constraints of the form `{ψ}`is as-of-yet unimplemented"

partial def InferApp (σ : TypeScheme) (e : Term) := (Γ' : Context) × (σ' : TypeScheme) × (∀ (e' : Term), (e'.Typing σ) -> (e'.app e).Typing σ')
mutual
partial def infer (Γ : Context) (e : Term) : InferM ((Γ' : Context) × (σ : TypeScheme) × e.Typing σ) := do
  match e with
  | .var χ =>
    let σ ← getType Γ χ
    return ⟨Γ, σ, .var⟩
  | .annot e σ =>
    let ⟨Γout, t⟩ ← check Γ e σ
    return ⟨Γout, σ, t.annot⟩
  | .let χ σ? e e' =>
    match σ? with
    | .none =>
      let ⟨Γ', σ, t⟩ ← infer Γ e
      let ⟨Γout, σ', t'⟩ ← infer ((.termvar χ σ)::Γ') e'
      return ⟨Γout, σ', t.let (b := false) t'⟩
    | .some σ =>
      let ⟨Γ', t⟩ ← check Γ e σ
      let ⟨Γout, σ', t'⟩ ← infer ((.termvar χ σ)::Γ') e'
      return ⟨Γout, σ', t.let (b := true) t'⟩
  | .app e₁ e₂ =>
    let ⟨Γ', σ₁, t₁⟩ ← infer Γ e₁
    let ⟨Γout, σ, generate_evidence⟩ ← inferApp Γ' σ₁ e₂
    return ⟨Γout, σ, generate_evidence e₁ t₁⟩
  | .lam χ e =>
    let a ← fresh
    let b ← fresh
    let τa := Monotype.uvar a
    let τb := Monotype.uvar b
    let ⟨Γout, t⟩ ← check ((.xunivar b .star)::(.xunivar a .star)::Γ) e τb
    return ⟨Γ, Monotype.arr τa τb, t.lam⟩
  | .label l => return ⟨Γ, Monotype.floor (.label l), .label⟩
  | .unlabel e₁ e₂ =>
    let ⟨Γ', Monotype.app (.prodOrSum Ξ μ) (.row [(ξ, τ)] _), t₁⟩ ← infer Γ e₁
      | throw $ .panic "expected a singleton product or sum"
    let ⟨Γout, t₂⟩ ← check Γ' e₂ (ξ.floor)
    return ⟨Γout, τ, t₁.unlabel⟩
  | .prod MNs =>
    let rec f (Γ : Context) : (MNs : List (Term × Term)) → InferM
      (Context × (ξτs : List (Monotype × Monotype)) ×
        ∀ MNξτ ∈ MNs.zip ξτs, let ((_, N), _, τ) := MNξτ; N.Typing τ)
      | [] => return ⟨Γ, [], nofun⟩
      | (M, N) :: MNs' => do
        let ⟨Γ', ξτs, h⟩ ← f Γ MNs'
        let ⟨Γ'', .qual $ .mono ξ, _⟩ ← infer Γ' M -- TODO: Check that ξ has kind label, evaluate lam apps?
          | throw $ .panic "expected a monotype for the label"
        let ⟨Γout, .qual $ .mono τ, t⟩ ← infer Γ'' N
          | throw $ .panic "expected a monotype in the row"
        return ⟨Γout, by
          refine ⟨(ξ, τ) :: ξτs, ?h⟩
          intro MNξτ mem
          let ((M', N'), ξ', τ') := MNξτ
          rw [List.zip_cons_cons] at mem
          simp only
          exact if h' : N = N' ∧ τ = τ' then by
              rcases h' with ⟨rfl, rfl⟩
              exact t
            else by
              let mem' : ((M', N'), ξ', τ') ∈ MNs'.zip ξτs := by
                match mem with
                | .head _ => match Classical.not_and_iff_or_not_not.mp h' with
                  | .inl h'' => nomatch h''
                  | .inr h'' => nomatch h''
                | .tail _ mem' => exact mem'
              exact h _ mem'⟩
    let ⟨Γout, fst, snd⟩ ← f Γ MNs
    return ⟨Γout,
      (Monotype.prodOrSum .prod (.comm .non)).app (.row fst (some .star)),
      Term.Typing.prod snd
    ⟩
  | .sum e₁ e₂ =>
    let ⟨Γ', .qual <| .mono <| .floor ξ, _⟩ ← infer Γ e₁
      | throw $ .panic "expected a floor for the label"
    checkKind Γ' ξ .label
    let ⟨Γout, .qual $ .mono τ, t⟩ ← infer Γ' e₂
      | throw $ .panic "expected a monotype in the row"
    return ⟨Γout, (Monotype.prodOrSum .sum (.comm .non)).app (.row [(ξ, τ)] none), t.sum⟩
  | .prj e =>
    let ⟨Γ', Monotype.app (.prodOrSum .prod μ) ρ, t⟩ ← infer Γ e
      | throw $ .panic "projection out of non-record term"
    let rx ← fresh
    let ⟨Γout, c⟩ ← constraint (.xunivar rx (.row .star)::Γ') <| .contain (.uvar rx) μ ρ
    return ⟨Γout, Monotype.app (.prodOrSum .prod μ) (.uvar rx), t.prj c⟩
  | .inj e =>
    let ⟨Γ', Monotype.app (.prodOrSum .sum μ) ρ, t⟩ ← infer Γ e
      | throw $ .panic "injection of non-variant term"
    let rx ← fresh
    let ⟨Γout, c⟩ ← constraint (.xunivar rx (.row .star)::Γ') <| .contain ρ μ (.uvar rx)
    return ⟨Γout, Monotype.app (.prodOrSum .sum μ) (.uvar rx), t.inj c⟩
  | .concat m n =>
    let (Γ, μ) ← freshType Γ .comm
    let (Γ, ρₘ) ← freshType Γ (.row .star)
    let ⟨Γ, tₘ⟩ ← check Γ m (Monotype.prodOrSum .prod μ |>.app ρₘ)
    let (Γ, ρₙ) ← freshType Γ (.row .star)
    let ⟨Γ, tₙ⟩ ← check Γ n (Monotype.prodOrSum .prod μ |>.app ρₙ)
    let (Γ, ρ) ← freshType Γ (.row .star)
    let (Γ, c) ← constraint Γ <| .concat ρₘ μ ρₙ ρ
    return ⟨Γ, _, .concat tₘ tₙ c⟩
  | .elim m n =>
    let (Γ, μ) ← freshType Γ .comm
    let (Γ, τ) ← freshType Γ .star
    let (Γ, ρₘ) ← freshType Γ (.row .star)
    let ⟨Γ, tₘ⟩ ← check Γ m (Monotype.prodOrSum .sum μ |>.app ρₘ |>.arr τ)
    let (Γ, ρₙ) ← freshType Γ (.row .star)
    let ⟨Γ, tₙ⟩ ← check Γ n (Monotype.prodOrSum .sum μ |>.app ρₙ |>.arr τ)
    let (Γ, ρ) ← freshType Γ (.row .star)
    let ⟨Γ, c⟩ ← constraint Γ <| (.concat ρₘ μ ρₙ ρ)
    return ⟨Γ, _, tₘ.elim tₙ c⟩
  | .member m =>
    let { TC, κ, .. } ← getClass m
    let (Γout, τ) ← freshType Γ κ
    -- TODO: push the constraint into the environment and get a proof for it.
    let s : ((Monotype.tc TC).app τ).ConstraintSolution := sorry
    let σ' : TypeScheme := sorry
    return ⟨Γout, σ', Term.Typing.member s⟩
  | .ind ϕ ρ l t rp ri rn M N =>
    let .arr κ κ' ← inferKind Γ ϕ | throw <| .panic "ind function with non-arrow kind"
    if κ' ≠ .star then
      throw <| .panic "ind function with non-star result kind"

    let ⟨Γ', so⟩ ← constraint Γ <| .ind ρ
    let ⟨Γ'', Mty⟩ ← check Γ' M _
    let ⟨Γout, Nty⟩ ← check Γ'' N _
    return ⟨Γout, _, .ind (κ := κ) Mty Nty so⟩
  | .splitₚ ϕ e =>
    let ⟨Γ, Monotype.app (.prodOrSum .prod (.comm .comm)) ρ, t⟩ ← infer Γ e
      | throw $ .panic "invalid splitₚ"
    let (Γ, ρ₁) ← freshType Γ (.row .star)
    let (Γ, ρ₂) ← freshType Γ (.row .star)
    let (Γout, c) ← constraint Γ (Monotype.split ϕ ρ₁ ρ₂ ρ)
    return ⟨Γout, _, t.splitₚ c⟩
  | .splitₛ ϕ e₁ e₂ =>
    let (Γ, τ) ← freshType Γ .star
    let (Γ, ρ₁) ← freshType Γ (.row .star)
    let ⟨Γ, t₁⟩ ← check Γ e₁ <| Monotype.arr (.app (.prodOrSum .sum (.comm .comm)) (.app (.lift ϕ) ρ₁)) τ
    let (Γ, ρ₂) ← freshType Γ (.row .star)
    let ⟨Γ, t₂⟩ ← check Γ e₂ <| Monotype.prodOrSum .sum (.comm .comm) |>.app ρ₂ |>.arr τ
    let (Γ, ρ₃) ← freshType Γ (.row .star)
    let ⟨Γ, c⟩ ← constraint Γ (Monotype.split ϕ ρ₁ ρ₂ ρ₃)
    return ⟨Γ, _, t₁.splitₛ t₂ c⟩
  | .nil =>
    let (Γout, τ) ← freshType Γ .star
    return ⟨Γout, _, Term.Typing.nil (τ := τ)⟩
  | .cons e₁ e₂ =>
    -- NOTE: Not sure if the order matters here, but this seems natural.
    let ⟨Γ', .qual $ .mono τ₁, t₁⟩ ← infer Γ e₁
      | throw $ .panic "cons applied to non-monotype"
    let ⟨Γout, t₂⟩ ← check Γ' e₂ (Monotype.list.app τ₁)
    return ⟨Γout, _, t₁.cons t₂⟩
  | .fold i iₐ => return ⟨Γ, _, Term.Typing.fold⟩
  | .int n =>
    return ⟨Γ, _, Term.Typing.int⟩
  | .op _ e₁ e₂ =>
    let ⟨Γ', t₁⟩ ← check Γ e₁ Monotype.int
    let ⟨Γout, t₂⟩ ← check Γ' e₂ Monotype.int
    return ⟨Γout, _, t₁.op t₂⟩
  | .range =>
    return ⟨Γ, _, Term.Typing.range⟩
  | .str s =>
    return ⟨Γ, _, Term.Typing.str⟩
  | .def s =>
    let ex ← fresh
    return ⟨Γ, _, Term.Typing.def (σ := Monotype.uvar ex)⟩
  | .throw =>
    let ex ← fresh
    return ⟨Γ, _, Term.Typing.throw (σ := Monotype.uvar ex)⟩

partial def inferApp (Γ : Context) (σ : TypeScheme) (e : Term) : InferM (InferApp σ e) := do
  match σ with
  | TypeScheme.quant α κ σ =>
    let ᾱ ← fresh;
    let Γ := (.xunivar ᾱ κ)::Γ
    let ⟨Γ', σ', myfun⟩ ← inferApp Γ (σ.subst (.uvar ᾱ) α) e
    return ⟨Γ', σ', fun e' (t : e'.Typing (TypeScheme.quant α κ σ)) =>
      sorry
    ⟩
  | Monotype.uvar ᾱ =>
    let .some item := lookupUniVar ᾱ Γ
      | throw $ .panic "found unknown unification variable"
    let .xunivar ᾱ (.arr κ₁ κ₂) := item
      | throw $ .panic "bad unification variable"
    let (before, after) ← split Γ item
    let ᾱ₁ ← fresh; let ᾱ₂ ← fresh;
    -- RECALL: newers entries appear to the "left" of the Context
    -- if regarded as a stack, this term should make sense
    let injection : List ContextItem := [
      .sunivar ᾱ (.arr (.uvar ᾱ₁) (.uvar ᾱ₂)),
      .xunivar ᾱ₁ κ₁,
      .xunivar ᾱ₂ κ₂,
    ]
    let Γ := after++injection++before
    let ⟨Γout, _t⟩ ← check Γ e (Monotype.uvar ᾱ₁)
    return ⟨Γout, Monotype.uvar ᾱ₂, fun e' t' =>
      sorry
    ⟩
  | Monotype.arr τ₁ τ₂ =>
    let ⟨Γout, _t⟩ ← check Γ e τ₁
    return ⟨Γout, τ₂, fun e' t' =>
      sorry
    ⟩
  | _ => throw $ .panic "can only infer applications for functions"

partial def check (Γ : Context) (e : Term) (σ : TypeScheme) : InferM ((Γ' : Context) × e.Typing σ) := do
  match σ with
  | .quant α κ σ =>
    let ⟨Γout, t⟩ ← check ((.typevar α κ)::Γ) e σ
    return ⟨Γout, t.schemeI⟩
  -- TODO: I am deeply inconfident in this rule.
  | .qual $ .qual ψ γ =>
    checkKind Γ ψ .constr
    let ⟨Γout, t⟩ ← check ((.constraint ψ)::Γ) e γ
    return ⟨Γout, .qualI (fun _ => t)⟩
  | σ =>
    let ⟨Γ', σ', t⟩ ← infer Γ e
    -- TODO: σ' and σ should have their bodies solved before subtyping begins
    let ⟨Γout, s⟩ ← subtype Γ' σ' σ
    return ⟨Γout, t.sub s⟩
end
