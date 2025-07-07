-- UNICODE PALETTE
-- × ⟨⟩ · μ ι ≠ ∘ ←
-- import Lean.Data.HashMap
import Std.Data.HashMap
import Std.Data.HashSet

namespace TabularTypeInterpreter.Interpreter.Resolution

abbrev V := String
structure C where
  name: String
  arity: Nat
deriving Repr, Inhabited, BEq

inductive Term: Type where
| var : V -> Term
| const : C -> List Term -> Term
deriving Repr, Inhabited, BEq

partial def Term.toString : Term -> String
| var v => s!"?{v}"
| const c terms => terms.foldl (fun acc => (acc++" "++·) ∘ Term.toString) c.name
instance : ToString Term where toString := Term.toString

partial def Term.freevars : Term -> List V
| var v => [v]
| const _ body => (body.map Term.freevars).flatten.eraseDups

-- a mapping from variables to terms. This is the biproduct of unification.
abbrev Subst := Std.HashMap V Term
def Subst.freevars : Subst -> (Std.HashSet V) := Std.HashSet.ofList ∘ (·.values.map Term.freevars |>.flatten)
-- assumes each substitution's target contains free variables *only*
partial instance : BEq Subst where
  beq subst1 subst2 :=
    let k1 := subst1.keys.mergeSort
    let k2 := subst2.keys.mergeSort
    if k1 != k2 then false else
    let fv1 := k1.map (fun k => subst1[k]!.freevars) |>.flatten.eraseDups
    let fv2 := k2.map (fun k => subst2[k]!.freevars) |>.flatten.eraseDups
    if fv1.length != fv2.length then false else
    let fvp := fv1.zip fv2
    k1.all (fun k => check_eq subst1[k]! subst2[k]!)
    where check_eq (t1 : Term) (t2 : Term) : Bool :=
      match t1, t2 with
      | .var _, .var _ => true
      | .const c1 cs1, .const c2 cs2 => c1 == c2 && (cs1.zip cs2).all (fun (a, b)=> check_eq a b)
      | _, _ => false

instance : ToString Subst where
toString subst := subst.toList.map (fun (v, t) => s!"{v} -> {t}") |>.toString

/--
A structure representing the pairwise unification of two matching literals. Both `substL` and `substR` create the same exact literal when mapped over their respective literals. The resulting literal represents the most general unifier.
-/
structure Unifier where
  substL : Subst
  substR : Subst
deriving Repr, Inhabited

def Unifier.freevars (self : Unifier) : Std.HashSet V :=
  self.substL.freevars ∪ self.substR.freevars

instance : ToString Unifier where toString
| ⟨l, r⟩ => s!"{l} ^^ {r}"

abbrev Relation := String × Nat
structure Literal : Type where
  relation : Relation
  terms: Vector Term relation.snd
deriving Repr, Inhabited

instance : ToString Literal where
toString
| {relation, terms} =>
  terms
  |>.map toString
  |>.foldl (fun acc s => s!"{acc} {s}") s!"{relation.fst}"

def Literal.freevars (self : Literal) : List V :=
  self.terms.map Term.freevars |>.toList |>.flatten |>.eraseDups

def Literal.coe? (self : Literal) (other : Literal) : Option $ Coe (type_of% self.terms) (type_of% other.terms) :=
  if h : self.relation.snd = other.relation.snd then
    .some ⟨fun t => h.rec t⟩
  else .none

namespace uni

inductive Space where
| left : Space
| right : Space
deriving Inhabited, Repr, BEq, Hashable
instance : ToString Space where toString |.left=>"←"|.right=>"→"
abbrev VS := V × Space
abbrev TermS := Term × Space
instance : Coe VS TermS where coe v := (.var v.fst, v.snd)

inductive RState where
| done : RState
| loop : RState
| term : TermS -> RState
deriving Repr
instance : Coe TermS RState where coe t := .term t

instance : ToString RState where toString
| .done => "done"
| .loop => "loop"
| .term (t, s) => s!"{s}{t}"

inductive UniErr : Type where
  | clash : UniErr
  | loop : UniErr
instance : ToString UniErr where toString
| .clash => "clash"
| .loop => "loop"

structure UniState where
  heartbeats : Nat
  r : Std.HashMap VS RState
  s : Std.HashMap VS RState
abbrev UniM := EStateM UniErr UniState

def beat : UniM Bool := do
  let state ← get
  set {state with heartbeats := state.heartbeats - 1}
  return state.heartbeats <= 0
def rSet (v : VS) (rs : RState) : UniM Unit := do
  let state <- get
  set ({ state with r := state.r.insert v rs })
def rGet (v : VS) : UniM (Option RState) := do
  return (<- get).r.get? v
def sSet (v : VS) (ss : RState) : UniM Unit := do
  let state <- get
  set ({ state with s := state.s.insert v ss })
def sGet (v : VS) : UniM (Option RState) := do
  return (<- get).s.get? v


structure NonEmptyList (a : Type) where
  head : a
  tail : List a
deriving Inhabited
def NonEmptyList.toList : NonEmptyList a -> List a
| { head, tail } => head::tail

partial def source (x : VS) : UniM (NonEmptyList VS) := (do
  let ⟨z, path⟩ ← getPath ⟨x, []⟩
  -- TODO: the following may or may not be necessary:
  -- if let .some .done ← rGet z then return { head := path.head!, tail := path.tail! } else
  return ⟨z, path⟩
  ) where getPath (path : NonEmptyList VS) : UniM (NonEmptyList VS) := do
    if ← beat then panic! "beat" else
    let v := path.head
    if let .some$ .term$ (.var z, s) ← rGet v then
      rSet v .done
      getPath ⟨(z, s), path.toList⟩
    else return path

partial def collapse (varList : List VS) (v : VS) : UniM Unit := do
  for x in varList do rSet x v

mutual
partial def here (t : TermS) (t' : TermS): UniM Unit := do
  if ← beat then panic! "beat" else
  if let ((.var v, s), (.var v', s')) := (t, t') then
    if v == v' && s == s' then return
  match t, t' with
  | (.var v, s), _ => varHere (v, s) t'
  | _, (.var v', s') => varHere (v', s') t
  | (.const c cs, s), (.const c' cs', s') =>
    if c != c' then throw .clash else
    for (x, x') in cs.zip cs' do here (x, s) (x', s')

partial def varHere (u : VS) (t : TermS) : UniM Unit := do
  if let .none ← rGet u then rSet u t
  else match t with
  | (.var t, s) =>
    let t := (t, s)
    if let .none ← rGet t then
      rSet t $ .term (.var u.fst, u.snd)
    else
      let ⟨v, path⟩ ← source u
      match ← rGet v with
      | .none | .some .done => collapse (v::path) t
      | _ => do
        let ⟨w, wPath⟩ ← source t
        if v == w then collapse (path++wPath) v
        else
          let z ← rGet w
          collapse (w::path++wPath) v
          if let .some$ .term zt := z then recurHere v zt
  | _ =>
    let ⟨v, path⟩ ← source u
    collapse path v
    if let .none ← rGet u then rSet v (.term t)
    else recurHere v t

partial def recurHere (v : VS) (t : TermS) : UniM Unit := do
  if let .some$ .term y ← rGet v then
  rSet v .loop
  here y t
  rSet v (.term y)
  else panic! "tried to recurHere on an unsolved variable"
end

mutual
partial def vere (u : VS) : UniM Term := do
  let ⟨v, path⟩ <- source u
  let t : TermS <- (do match ← rGet v with
  | .none =>
    rSet v .done
    pure v
  | .some$ .term t@(.const _ [], _) =>
    rSet v .done
    sSet v t
    pure t
  | .some$ .term (.const c cs, s) =>
    rSet v .done
    for x in v::path do sSet x .loop
    let t := (← termVere c cs s, s)
    sSet v t
    pure t
  | _ => match ← sGet v with
    | .none => pure v
    | .some$ .term t => pure t
    | .some .loop => throw .loop
    | _ => panic! "bad assumption"
  )
  for x in path do sSet x t
  return t.fst

partial def termVere (c : C) (cs : List Term) (s : Space) : UniM Term := do
  if ← beat then panic! "beat" else
  let mut cs := cs
  for i in [0:c.arity] do
    let t_i := cs[i]!
    match t_i with
    | .var v_i =>
      match <- rGet (v_i, s) with
      | .some .done =>
        match <- sGet (v_i, s) with
        | .some .loop => throw .loop
        | .some$ .term (x, sx) =>
          assert! s == sx
          cs := cs.set i x
        | _ => continue
      | .some _ => cs := cs.set i (← vere (v_i, s))
      | .none => continue
    | .const c_i cs_i@(_::_) =>
      cs := cs.set i (← termVere c_i cs_i s)
    | _ => continue
  return .const c cs
end

/-- Unify two literals. -/
def unify (self : Literal) (other : Literal) : Option Unifier :=
  -- we need for each literal to know where it lives, so that equality only makes sense if it's from the same space.
  match other.coe? self with
  | .none => .none
  | .some _ =>
  let result := (do
    for (x, x') in self.terms.zip other.terms do
      here (x, .left) (x', .right)
    let mut substL : Subst := ∅
    let mut substR : Subst := ∅
    for v in self.freevars do
      if ← beat then panic! "beat" else
      substL := substL.insert v (← vere (v, .left))
    for v' in other.freevars do
      if ← beat then panic! "beat" else
      substR := substR.insert v' (← vere (v', .right))

    return Unifier.mk substL substR
  ).run {heartbeats := 20, r := ∅, s := ∅}

  match result with
  | .error e _ =>
    dbg_trace s!"failed to unify {self} with {other}: {e}"
    .none
  | .ok v _ => .some v

end uni

partial def Subst.apply (subst : Subst) (term : Term) : Term := match term with
| .var v => subst.getD v term
| .const c rest => .const c (rest.map subst.apply)

def Subst.applyIn (subst : Subst) (literal : Literal) : Literal :=
  {
    relation := literal.relation,
    terms := literal.terms.map subst.apply
  }

-- NOTE: ordering is `v |-> f(g(v))`
def Subst.compose (f : Subst) (g : Subst) : Subst :=
  -- NOTE: weirdly, hashmaps don't have a `.map` function.
  Std.HashMap.ofList $ g.toList.map (fun (v, term) => (v, f.apply term))

def Literal.canonicalMap (literal : Literal) : Subst :=
  Std.HashMap.ofList $
      literal.freevars
      |>.mapIdx (fun idx v => (v, .var (toString idx)))

def Literal.toCanonical (literal : Literal) : Literal :=
  literal.canonicalMap.applyIn literal

instance : Hashable Literal where
  hash query := (
    let query := query.toCanonical
    hash $ (hash query.relation, hash $ query.terms.map toString |>.toArray)
  )

instance : BEq Literal where
  beq q1 q2 := (
    let canonical1 := q1.toCanonical
    let canonical2 := q2.toCanonical
    if h : canonical1.relation ≠ canonical2.relation then false else
    let z : Vector Term canonical1.relation.snd = Vector Term canonical2.relation.snd := by
      congr 2
      false_or_by_contra
      contradiction
    canonical1.terms == z.symm.rec canonical2.terms
  )

structure Clause : Type where
  body : List Literal
  head : Literal
deriving Repr, Inhabited

instance : ToString Clause where
  toString
  | {body, head} =>
    let body : String :=
      body.tail
      |>.map toString
      |>.foldl (fun acc s => s!"{acc}, {s}") (body.head?|>.map toString|>.getD "[]")
    s!"{body} => {head}"
-- generate matching clauses. This is the only user provided logic (I think)
-- NOTE: the generated list of clauses must "match" the query.
-- Definition:
--   a clause with head `h` matches a query `q` if and only if
--   1. `q.relation == h.relation`
--   2. `q.terms.length == h.terms.length`
--   3. the mapping `q.terms.zip h.terms` is
--     - a well-defined function, i.e. if `(t, ta) (t, tb)` are entries, then `ta == tb`.
--     - the identity over constants, i.e. if `(t, t')` is an entry and `t` is a constant, `t == t'`
variable (ι : Literal -> List Clause)

mutual
  inductive Node : Type where
  | root (key: Literal) : Node
  | child (parent: Node) (branch: Branch) (queries: List Literal) : Node
  deriving Repr

  inductive Branch : Type where
  | clause : Clause -> Unifier -> Branch
  | solution : Subst -> Branch
end
instance : ToString Branch where toString
| .clause c u => s!"clause {c} unified to {u}"
| .solution s => s!"solution {s}"

def Node.key : Node -> Literal
| .root q => q
| .child parent _ _ => parent.key

mutual
  -- the idea is to combine all the maps in this node's history into a single subst.
  partial def Node.collectSolution : Node -> Subst
    | .root _ => panic! "Cannot extract Subst from root node"
    | .child parent branch _ => match branch with
      | .clause _ unifier =>
        if let .root _ := parent then
          unifier.substL
        else
          panic! "Found a clause-branch whose parent is non-root"
      | .solution solution =>
        if let .child _ _ (head::_) := parent then
          (solution.compose head.canonicalMap).compose parent.collectSolution
        else
          panic! "Found a solution-branch whose parent is non-valid node"
end

def Node.toString : Node -> String
  | .root key => s!"{key}"
  | .child parent branch literals =>
    let solution : String :=
      match branch with
      | .clause _ unifier => (s!"{unifier.substL} | {unifier.substR}")
      | .solution solution => s!"{solution}"
    s!"{parent.toString} -{solution}-> {literals}"

instance : ToString Node where
  toString := Node.toString

structure Entry where
  clauses: List Clause
  dependents: List Node
  solutions: List Subst
deriving Repr

instance : ToString Entry where
  toString
  | { clauses, dependents, solutions } =>
    s!"[c={clauses.head?}... d={dependents.map (·.key)} s={solutions.length}]"

def Entry.fresh (query: Literal) : Entry :=
  Entry.mk (ι query.toCanonical) [] []
instance : Inhabited Entry where
  default := (Entry.mk [] [] [])

def Entry.containsSolution (entry : Entry) (solution : Subst) : Bool :=
  entry.solutions.contains solution

structure Table : Type where
  entries : Std.HashMap Literal Entry
  ordering : List Literal
deriving Repr, Inhabited

instance : ToString Table where
  toString
  | { entries, ordering } =>
    let x := ordering.map (fun literal => s!"{literal} {entries[literal]!}")
    x.intersperse "\n" |>.toString

instance : GetElem Table Literal Entry (fun table query => table.entries.contains query.toCanonical)
where
  getElem table query := table.entries.get query.toCanonical

def Table.push (table: Table) (query: Literal) (entry: Entry) : Table :=
  let query := query.toCanonical
  let ordering : List Literal :=
    if table.entries.contains query then
      table.ordering
    else
      query :: table.ordering
  Table.mk (table.entries.insert query entry) ordering
def Table.popClause (table : Table) (key : Literal) : Table × Clause :=
    let next : Clause := table[key]!.clauses.head!
    let table := table.push key { table[key]! with clauses := table[key]!.clauses.tail }
    (table, next)
def Table.pushSolution (table : Table) (key : Literal) (solution : Subst) : Table :=
  let entry := table[key]!
  table.push key { entry with solutions := solution::entry.solutions }
def Table.root (table : Table) : Literal :=
  table.ordering[table.ordering.length - 1]!

def Table.empty : Table := Table.mk ∅ []
def Table.singleton (query : Literal) := Table.empty.push query

-- Algorithm

inductive Exception where
  | done : Subst -> Exception
structure State where
  heartbeats : Nat
  generator : StdGen

abbrev SynthM := EStateM Exception State

def beat : SynthM Bool := do
  let state ← get
  set {state with heartbeats := state.heartbeats - 1}
  return state.heartbeats <= 0
def getNext : SynthM Nat := do
  let state ← get
  let (num, newStdGen) := stdNext state.generator
  set {state with generator := newStdGen}
  return num

def Subst.refresh (self : Subst) : SynthM Subst := do
  let pairs <- self.freevars.toList.mapM (fun v => do return (v, .var s!"!{<- getNext}"))
  let freshMap : Subst := Std.HashMap.ofList (pairs)
  return freshMap.compose self

def Unifier.refresh (self : Unifier) : SynthM Unifier := do
  let pairs <- self.freevars.toList.mapM (fun v => do return (v, .var s!"!{<- getNext}"))
  let freshMap : Subst := Std.HashMap.ofList pairs
  return {
    substL := freshMap.compose self.substL
    substR := freshMap.compose self.substR
  }

-- NOTE: panics if `other` was not generated as the head of a matching clause.
def Literal.unify (self : Literal) (other : Literal) : SynthM (Option Unifier) := do
  let unifier := uni.unify self other
  return ← unifier.mapM Unifier.refresh

mutual
  partial def Table.resume (table: Table) : List (Node × Branch) -> SynthM Table
  | [] => pure table
  | (node, branch)::rest => do
    if ← beat then panic! "beat" else
    let remainder : List Literal <- match node with
    | .root _ =>
      if let Branch.clause clause unifier := branch then
        pure $ clause.body.map unifier.substR.applyIn
      else
        panic! "Tried to resume a root node with a non-clause branch"
    | .child _ _ (head::tail) =>
      if let Branch.solution solution := branch then
        pure $ tail.map (solution.compose head.canonicalMap).applyIn
      else
        panic! "Tried to resume an intermediate node with a non-solution branch"
    | .child _ _ [] => panic! "Tried to resume a node with no children"
    table.consume (Node.child node branch remainder) >>= (·.resume rest)

  -- Process a node by either
  -- 1. extracting a solution from it (if it has no queries) and resuming dependents
  -- 2. branching off of its first query to resume with its solutions
  partial def Table.consume (table: Table) (node: Node): SynthM Table := do
    if ← beat then panic! "beat" else
    match node with
    | .root key =>
      let (table, nextClause) := table.popClause key
      match (<- key.unify nextClause.head) with
      | .some unifier =>
        table.resume [(node, Branch.clause nextClause unifier)]
      | .none => return table
    | .child _ _ (List.cons query _) =>
      let entry : Entry := table[query]?.getD $ Entry.fresh ι query
      table
      |>.push query { entry with dependents := node::entry.dependents }
      |>.resume $ (← entry.solutions.mapM Subst.refresh).map (node, Branch.solution ·)
    | .child _ _ [] =>
      let key := node.key
      let solution := node.collectSolution
      if key == table.root then throw <| .done solution
      if table[key]!.solutions.contains solution then pure table else
      table.pushSolution key solution
      |>.resume $ table[key]!.dependents.map (·, Branch.solution (← solution.refresh))
end

partial def Table.exec (table: Table) : SynthM Table := do
  if ← beat then panic! "beat" else
  let next? : Option Literal := table.ordering.map .some |>.firstM $ .filter (table[·]!.clauses.isEmpty.not)
  match next? with
  | .none => pure table
  | .some key => table.consume ι (Node.root key) >>= exec

def resolve (query: Literal) : Option Subst :=
  let table := Table.singleton query (Entry.fresh ι query)
  let result := (table.exec ι).run { heartbeats := 100, generator := mkStdGen 0 }
  match result with
  | .error (.done s) _ =>  .some s
  | .ok _ _ => .none
