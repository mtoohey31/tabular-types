import TabularTypeInterpreter.Interpreter.Basic
import Lott.Data.Range
import Parser
import Parser.Char

namespace TabularTypeInterpreter.Interpreter.Parser

open TabularTypeInterpreter.Interpreter
open _root_.Parser Char ASCII
open Std

-- TODO: Replace `SimpleParser` with `Parser` and custom error types, and replace `<|>` with `first`
-- using a custom `combine` so that we can report better messages.

private
abbrev CoreM := SimpleParser Substring Char

private
def comment : CoreM Unit := string "--" *> takeUntil (char '\n') anyToken *> pure ()

private
def ws : CoreM Unit := dropMany <|
  tokenFilter [' ', '\n', '\r', '\t'].contains *> pure () <|> comment

local
infixl:60 " **> " => fun l r => l *> liftM ws *> r

local
infixl:60 " <** " => fun l r => l <* liftM ws <* r

local
infixl:50 " <**> " => fun l r => l <*> (liftM ws *> r)

local
prefix:60 "~*> " => fun r => liftM ws *> r

local
postfix:60 " <*~" => fun l => l <* liftM ws

private
def paren [Monad m] [inst : MonadLiftT CoreM m] (p : m α) : m α :=
  (liftM (self := inst) (char '(')) **> p <** (liftM (self := inst) (char ')'))

open Kind in
private partial
def kind (greedy := true) : CoreM Kind := withErrorMessage "expected kind" do
  let κ ← char '*' *> pure star
    <|> char 'L' *> pure label
    <|> char 'U' *> pure comm
    <|> char 'R' **> row <$> kind (greedy := false)
    <|> char 'C' *> pure constr
    <|> paren kind

  if !greedy then
    return κ

  foldl arr κ <| ~*> (string "|->" <|> string "↦") **> kind

private
def _root_.String.Pos.line (pos : String.Pos) (s : Substring) : Nat :=
  s.extract s.startPos pos |>.foldl (fun n d => if d = '\n' then n + 1 else n) 1

private
def _root_.String.Pos.col (pos : String.Pos) (s : String) : Nat :=
  s.extract (s.findLineStart pos) pos |>.length.succ

private
def _root_.String.Pos.lineAndCol (pos : String.Pos) (s : String) : String :=
  s!"{pos.line s}:{pos.col s}"

private
def _root_.Parser.Error.Simple.toString (s : String) : Error.Simple Substring Char → String
  | .unexpected pos (some tok) =>
    s!"unexpected token {repr tok} at {String.Pos.lineAndCol pos s}"
  | .unexpected pos none => s!"unexpected token at {String.Pos.lineAndCol pos s}"
  | .addMessage e pos msg => e.toString s ++ s!"; {msg} at {String.Pos.lineAndCol pos s}"

private
def assertResultEq [BEq α] [ToString α] (input : String) (expected : α)
  (result : Parser.Result (Parser.Error.Simple Substring Char) Substring α)
  : Lean.Elab.TermElabM Unit :=
  match result with
  | .ok _ actual => do
    if expected != actual then
      throwError "× -- expected: {expected}, actual: {actual}"
  | .error _ e => throwError "× -- {e.toString input}"

local
macro "#parse_kind " input:str " to " expected:term : command =>
  `(#eval assertResultEq $input (open Kind in $expected) ((kind <* endOfInput).run $input))

#parse_kind "*" to star
#parse_kind "* |-> L" to star.arr label
#parse_kind "U↦R * ↦ C" to comm.arr <| row star |>.arr constr
#parse_kind "R ( * ↦ * )" to row <| star.arr star
#parse_kind "R * ↦ *" to row star |>.arr star
#parse_kind "R R C" to row <| row constr

private
structure ProgramContext where
  defs : HashSet String := .empty
  typeAliases : HashSet String := .empty
  classToMember : HashMap String String := .empty
deriving Inhabited

namespace ProgramContext

private
def boundTerm (ctx : ProgramContext) : HashSet String :=
  ctx.defs.union <| .ofList ctx.classToMember.values

private
def boundType (ctx : ProgramContext) : HashSet String :=
  ctx.typeAliases.union <| .ofList ctx.classToMember.keys

end ProgramContext

private
abbrev VarTable (α : Type) := Batteries.RBMap String α compare

private
abbrev InvertedVarTable (α : Type) [inst : Ord α] := Batteries.RBMap α String compare

private
structure TypeContext extends ProgramContext where
  typeVars : VarTable TId := .empty
deriving Inhabited

private
structure IdState (n : Name) where
  nextFresh : Nat := 0
  invertedVars : InvertedVarTable (Id n) := .empty
deriving Inhabited

private
structure UVarState where
  nextFresh : Nat := 0
deriving Inhabited

private
structure TypeState where
  id : IdState `type := { }
  uvar : UVarState := { }
deriving Inhabited

private
abbrev TypeM := SimpleParserT Substring Char <| StateT TypeState <| StateM TypeContext

local
instance : Functor (Parser.Result ε σ) where
  map
    | f, .ok s x => .ok s (f x)
    | _, .error s e => .error s e

private
def TypeM.pushVars (ids : List String) : TypeM α → TypeM (α × List TId) := fun x s s' r =>
  let filtered := ids.filter (· != "_")
  let ((res, s''), r') := x s
    { s' with id := {
        s'.id with
        nextFresh := s'.id.nextFresh + ids.length
        invertedVars := ids.foldlIdx (init := s'.id.invertedVars)
          fun i acc id => acc.insert { val := s'.id.nextFresh + i } id
      }
    }
    { r with
      typeVars := filtered.foldlIdx (init := r.typeVars)
        fun i acc id => acc.insert id { val := s'.id.nextFresh + i }
    }
  (
    ((·, [s'.id.nextFresh:s'.id.nextFresh + ids.length].map Id.mk) <$> res, s''),
    { r' with
      typeVars := filtered.foldl (init := r'.typeVars)
        fun acc id => if let some prev := r.typeVars.find? id then
            acc.insert id prev
          else
            acc.erase id
    }
  )

private
def TypeM.pushVar (id : String) : TypeM α → TypeM (α × TId) := fun x s s' r =>
  let ((res, s''), r') := x s
    { s' with id := {
        s'.id with
        nextFresh := s'.id.nextFresh + 1
        invertedVars := s'.id.invertedVars.insert { val := s'.id.nextFresh } id
      }
    }
    { r with
      typeVars :=
        if id != "_" then r.typeVars.insert id { val := s'.id.nextFresh } else r.typeVars
    }
  (
    ((·, { val := s'.id.nextFresh }) <$> res, s''),
    { r' with
      typeVars := if let some prev := r.typeVars.find? id then
          r'.typeVars.insert id prev
        else
          r'.typeVars.erase id
    }
  )

private
def TypeM.addVar (id : String) : TypeM TId := fun s s' r =>
  (
    (
      .ok s { val := s'.id.nextFresh },
      { s' with id := {
          s'.id with
          nextFresh := s'.id.nextFresh + 1
          invertedVars := s'.id.invertedVars.insert { val := s'.id.nextFresh } id
        }
      }
    ),
    { r with
      typeVars :=
        if id != "_" then r.typeVars.insert id { val := s'.id.nextFresh } else r.typeVars
    }
  )

private
def TypeM.getVars : TypeM (VarTable TId) := fun s s' r => ((.ok s r.typeVars, s'), r)

private
instance : MonadLiftT CoreM TypeM where
  monadLift p s s' r := ((p s, s'), r)

private
def rawId : CoreM String := (⟨· :: ·.toList ++ ·.toList⟩) <$>
  (alpha <|> char '_') <*> takeMany (alphanum <|> char '_') <*> takeMany (char '\'')

private
def programReserved := ["def", "type", "class", "instance"]

private
def typeReserved := programReserved ++
  ["where", "C", "N", "P", "S", "Lift", "All", "Ind", "Split", "List", "Int", "String", "o"]

private
def unreservedTypeId : TypeM String := do
  let id ← rawId
  if typeReserved.contains id then
    throwUnexpectedWithMessage none s!"use of reserved identifier '{id}'"

  return id

private
def freshUVar : TypeM (Monotype true) := do
  let { uvar := { nextFresh, .. }, .. } ← getModify fun st =>
    { st with uvar := { st.uvar with nextFresh := st.uvar.nextFresh + 1 } }
  return .uvar nextFresh

private
def typeId (inTerm allowFree : Bool) : TypeM (Monotype inTerm) := do
  let id ← unreservedTypeId

  let { typeVars, typeAliases, classToMember, .. } ← get (m := StateM TypeContext)
  if let some id := typeVars.find? id then
    return .var id

  if h : inTerm && id == "_" then
    return ← by
      simp at h
      rw [h.left]
      exact freshUVar

  if classToMember.contains id then
    return .tc id

  if typeAliases.contains id then
    return .alias id

  if allowFree then return .var <| ← TypeM.addVar id

  throwUnexpectedWithMessage none s!"undeclared type var '{id}'"

private
def comm : TypeM Comm := withErrorMessage "expected commutativity" <|
  char 'C' *> pure Comm.comm <|> (char 'N' <* notFollowedBy (string "at")) *> pure .non

open ProdOrSum
private
def prodOrSum : TypeM ProdOrSum := withErrorMessage "expected prod or sum" <|
  (char 'P' <|> char 'Π') *> pure prod <|> (char 'S' <|> char 'Σ') *> pure sum

private
def «▹» : TypeM String := string "|>" <|> string "▹"

open Monotype in
private partial
def monotype (inTerm allowFree : Bool) (greedy := true) : TypeM (Monotype inTerm) :=
  withErrorMessage "expected monotype" do
  let τ ← typeId inTerm allowFree
    <|> (do
      let idsκs ← (char '\\' <|> char 'λ') **> sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> char ':' **> kind) <** char '.' <*~
      let (τ, idsκs) ← idsκs.foldr (init := ((·, [])) <$> go) fun (ids, κ) acc => do
        let ((τ, idsκs), ids) ← TypeM.pushVars ids.toList acc
        return (τ, (ids, κ) :: idsκs)
      return idsκs.foldr (fun (ids, κ) τ' => ids.foldr (lam · κ ·) τ') τ)
    <|> (label ∘ String.mk ∘ Array.toList ∘ Prod.fst) <$>
      (char '\'' *> takeUntil (char '\'') anyToken)
    <|> floor <$> ((string "|_" <|> string "⌊") **> go <** (string "_|" <|> string "⌋"))
    <|> Monotype.comm <$> comm
    <|> (row ∘ .ofList ∘ Array.toList)
      <$> ((char '<' <|> char '⟨') **> (sepBy (~*> char ',' <*~) (Prod.mk <$> go <**> «▹» **> go)))
        <**> (option? (char ':' **> kind)) <** (char '>' <|> char '⟩')
    <|> Monotype.prodOrSum <$> prodOrSum <**> paren go
    <|> string "Lift" *> pure lift
    <|> string "All" *> pure all
    <|> string "Ind" *> pure ind
    <|> string "Split" *> pure split
    <|> string "List" *> pure list
    <|> string "Int" *> pure int
    <|> string "String" *> pure str
    <|> paren go

  if !greedy then
    return τ

  let τ' ← foldl app τ <| ~*> go false

  let tail := arr τ' <$> (~*> (string "->" <|> string "→") **> go)
    <|> contain τ' <$> (~*> (string "~<" <|> string "≲") **> paren go) <**> go
    <|> concat τ' <$> (~*> (char 'o' <|> char '⊙') **> paren go) <**> go <**> (char '~' **> go)

  optionD tail τ'
where
  go (greedy := true) := monotype inTerm allowFree greedy

private
def «⇒» : CoreM String := string "=>" <|> string "⇒"

open QualifiedType in
private partial
def qualifiedType (inTerm allowFree : Bool) (arrowRequired := false) : TypeM (QualifiedType inTerm) :=
  withErrorMessage "expected qualified type" do
  let τ ← monotype inTerm allowFree
  let γ? ← option? <|
    ~*> (liftM «⇒» **> qualifiedType inTerm allowFree
          <|> string "," **> qualifiedType inTerm allowFree true)
  match γ? with
  | none =>
    if arrowRequired then
      throwUnexpectedWithMessage none "last separator for qualified type must be '⇒' instead of ','"
    return τ
  | some γ => return qual τ γ

open TypeScheme in
private partial
def typeScheme (inTerm allowFree : Bool) : TypeM (TypeScheme inTerm × VarTable TId) :=
  withErrorMessage "expected type scheme" <| (do
      let idsκs ← (string "forall" <|> string "∀") **> sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> char ':' **> liftM kind) <** char '.' <*~
      let ((σ, vt), idsκs) ← idsκs.foldr (init := ((·, [])) <$> typeScheme inTerm allowFree)
        fun (ids, κ) acc => do
          let ((σvt, idsκs), ids) ← TypeM.pushVars ids.toList acc
          return (σvt, (ids, κ) :: idsκs)
      return (idsκs.foldr (fun (ids, κ) σ' => ids.foldr (quant · κ ·) σ') σ, vt))
      <|> (do
        let γ ← qualifiedType inTerm allowFree
        let vt ← TypeM.getVars
        return (qual γ, vt))

namespace Test

local
instance : OfNat TId n where
  ofNat := { val := n }

local
instance : ToString TId where
  toString | { val } => toString val

local
macro "#parse_type " input:str " to " expected:term : command =>
  `(#eval assertResultEq $input (α := TypeScheme true)
      (open TypeScheme in open QualifiedType in open Monotype in $expected)
      <| Prod.fst <$> ((typeScheme true false <* endOfInput) $input { id := { nextFresh := 3 } } {
          typeAliases := { "Option", "Bool" }
          classToMember := { ("Eq", "eq"), ("LE", "le") }
          typeVars := .ofList [("a", 0), ("b", 1), ("c", 2)] compare
        } |>.fst.fst))

#parse_type "b" to var (uvars := true) 1
#parse_type "_ _" to uvar 0 |>.app <| uvar 1
#parse_type "a b c" to app (uvars := true) (app (var 0) (var 1)) (var 2)
#parse_type "λ a : *. a" to lam (uvars := true) 3 .star (var 3)
#parse_type "\\d : R *. a d" to lam (uvars := true) 3 (.row .star) <| app (var 0) (var 3)
#parse_type "λ a b : *, c d : C. a d" to lam (uvars := true) 3 .star <| lam 4 .star <|
  lam 5 .constr <| lam 6 .constr <| app (var 3) (var 6)
#parse_type "λ _ : *. _" to lam 3 .star <| uvar 0
#parse_type "''" to label (uvars := true) ""
#parse_type "⌊'value'⌋" to floor (uvars := true) (label "value")
#parse_type "C" to Monotype.comm (uvars := true) .comm
#parse_type "N" to Monotype.comm (uvars := true) .non
#parse_type "⟨⟩" to row (uvars := true) .nil none
#parse_type "< : * >" to row (uvars := true) .nil <| some .star
#parse_type "⟨'a' ▹ Lift, 'b' |> (All), ('c') ▹ Ind⟩" to row (uvars := true)
  (.cons (label "a") lift (.cons (label "b") all (.cons (label "c") ind .nil))) none
#parse_type "Π(N) ⟨⟩" to Monotype.prodOrSum (uvars := true) .prod (.comm .non) |>.app <|
  row .nil none
#parse_type "P(C)" to Monotype.prodOrSum (uvars := true) .prod <| .comm .comm
#parse_type "Σ(C)" to Monotype.prodOrSum (uvars := true) .sum <| .comm .comm
#parse_type "S(N)" to Monotype.prodOrSum (uvars := true) .sum <| .comm .non
#parse_type "a ≲(N) b" to contain (uvars := true) (var 0) (Monotype.comm .non) (var 1)
#parse_type "a b a ~<(C) c a" to contain (uvars := true) (app (app (var 0) (var 1)) (var 0))
  (Monotype.comm .comm) (app (var 2) (var 0))
#parse_type "a ⊙(N) b ~ c ⇒ a" to qual (uvars := true)
  (concat (var 0) (Monotype.comm .non) (var 1) (var 2)) (mono (var 0))
#parse_type "a o(C) b ~ c => a" to qual (uvars := true)
  (concat (var 0) (Monotype.comm .comm) (var 1) (var 2)) (mono (var 0))
#parse_type "Eq" to tc (uvars := true) "Eq"
#parse_type "LE" to tc (uvars := true) "LE"
#parse_type "Split a b c -> List a" to split (uvars := true) |>.app (var 0) |>.app (var 1)
  |>.app (var 2) |>.arr (list.app <| var 0)
#parse_type "Int → String" to int (uvars := true) |>.arr str
#parse_type "∀ a : *. a" to quant (uvars := true) 3 .star <| qual <| mono <| var 3
#parse_type "forall d : R *. a d" to quant (uvars := true) 3 (.row .star) <| qual <| mono <|
  app (var 0) (var 3)
#parse_type "∀ a b : *, c d : C. a d" to quant (uvars := true) 3 .star <| quant 4 .star <|
  quant 5 .constr <| quant 6 .constr <| qual <| mono <| app (var 3) (var 6)
#parse_type "Bool" to «alias» (uvars := true) "Bool"
#parse_type "Option" to «alias» (uvars := true) "Option"

end Test

private
structure TermContext extends TypeContext where
  termVars : VarTable MId := .empty
deriving Inhabited

private
structure TermState where
  mid : IdState `term := { }
  type : TypeState := { }
deriving Inhabited

private
abbrev TermM := SimpleParserT Substring Char <| StateT TermState <| ReaderM TermContext

namespace TermM

private
def pushVars (ids : List String) : TermM α → TermM (α × List MId) := fun x s s' r =>
  (((·, [s'.mid.nextFresh:s'.mid.nextFresh + ids.length].map Id.mk)) <$> x) s
    { s' with mid := {
        s'.mid with
        nextFresh := s'.mid.nextFresh + ids.length
        invertedVars := ids.foldlIdx (init := s'.mid.invertedVars)
          fun i acc id => acc.insert { val := s'.mid.nextFresh + i } id
      }
    }
    { r with
      termVars := ids.foldlIdx (init := r.termVars)
        fun i acc id => acc.insert id { val := s'.mid.nextFresh + i } }

private
def pushVar (id : String) : TermM α → TermM (α × MId) := fun x s s' r =>
  ((·, { val := s'.mid.nextFresh }) <$> x) s
    { s' with mid := {
        s'.mid with
        nextFresh := s'.mid.nextFresh + 1
        invertedVars := if id != "_" then
            s'.mid.invertedVars.insert { val := s'.mid.nextFresh } id
          else
            s'.mid.invertedVars
      }
    }
    { r with
      termVars :=
        if id != "_" then r.termVars.insert id { val := s'.mid.nextFresh } else r.termVars
    }

private
def includeTypeVars (vt : VarTable TId) : TermM α → TermM α := fun x s s' r =>
  x s s' { r with typeVars := r.typeVars.mergeWith (fun _ _ id => id) vt }

private
def pushTypeVars (ids : List String) : TermM α → TermM (α × List TId) := fun x s s' r =>
  let filtered := ids.filter (· != "_")
  ((·, [s'.type.id.nextFresh:s'.type.id.nextFresh + ids.length].map Id.mk) <$> x) s
    { s' with
      type := {
        s'.type with
        id := {
          s'.type.id with
          nextFresh := s'.type.id.nextFresh + ids.length
          invertedVars := ids.foldlIdx (init := s'.type.id.invertedVars)
            fun i acc id => acc.insert { val := s'.type.id.nextFresh + i } id
        }
      }
    }
    { r with
      typeVars := filtered.foldlIdx (init := r.typeVars)
        fun i acc id => acc.insert id { val := s'.type.id.nextFresh + i }
    }

private
def pushTypeVar (id : String) : TermM α → TermM (α × TId) := fun x s s' r =>
  ((·, { val := s'.type.id.nextFresh }) <$> x) s
    { s' with
      type := {
        s'.type with
        id := {
          s'.type.id with
          nextFresh := s'.type.id.nextFresh + 1
          invertedVars := s'.type.id.invertedVars.insert { val := s'.type.id.nextFresh } id
        }
      }
    }
    { r with
      typeVars :=
        if id != "_" then r.typeVars.insert id { val := s'.type.id.nextFresh } else r.typeVars
    }

end TermM

private
instance : MonadLiftT TypeM TermM where
  monadLift p s s' r :=
    let ((x, s''), _) := p s s'.type r.toTypeContext
    (x, { s' with type := s'' })

private
instance : MonadLiftT CoreM TermM where
  monadLift x := liftM <| liftM (n := TypeM) x

private
def termReserved := programReserved ++ [
    "let",
    "in",
    "prj",
    "inj",
    "ind",
    "splitp",
    "splits",
    "orderp",
    "orders",
    "if",
    "then",
    "else"
  ]

private
def unreservedTermId : TermM String := do
  let id ← liftM rawId
  if termReserved.contains id then
    throwUnexpectedWithMessage none s!"use of reserved identifier '{id}'"

  return id

private
def termId : TermM (Term true) := do
  let id ← unreservedTermId

  let { termVars, defs, classToMember, .. } ← read
  if let some id := termVars.find? id then
    return .var id

  if classToMember.values.contains id then
    return .member id

  if defs.contains id then
    return .def id

  throwUnexpectedWithMessage none s!"undeclared term var '{id}'"

private
def op : TermM «λπι».Op := withErrorMessage "expected binary operator" <|
  char '+' *> pure .add
    <|> char '-' *> pure .sub
    <|> char '*' *> pure .mul
    <|> (string "//" <|> string "÷") *> pure .div
    <|> string "==" *> pure .eq
    <|> (string "<=" <|> string "≤") *> pure .le
    <|> char '<' *> pure .lt
    <|> (string ">=" <|> string "≥") *> pure .ge
    <|> char '>' *> pure .gt

open Term in
private partial
def term (greedy unlabel := true) (allowFree := false) : TermM (Term true) := withErrorMessage "expected term" do
  let M ← termId
    <|> (do
      let idsτ?s ← (char '\\' <|> char 'λ') **> sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTermId <**> option? (char ':' **> monotype true))
        <** char '.' <*~
      let (M, idsτ?s) ← idsτ?s.foldr (init := ((·, [])) <$> go) fun (ids, τ?) acc => do
        let ((τ, idsτ?s), ids) ← TermM.pushVars ids.toList acc
        return (τ, (ids, τ?) :: idsτ?s)
      idsτ?s.foldrM (init := M) fun (ids, τ?) M' =>
        ids.foldrM (init := M') fun id M'' =>
          if let some τ := τ? then
            return annot (lam id M'') <| Monotype.arr τ <| ← freshUVar
          else
            return lam id M'')
    <|> (do
      let id ← string "let" **> unreservedTermId <*~
      let σvt? ← option? (char ':' **> typeScheme <*~)
      if let some (σ, vt) := σvt? then
        let M ← char '=' **> TermM.includeTypeVars vt go <*~
        let (N, id) ← string "in" **> TermM.pushVar id go
        return .let id σ M N
      else
        let M ← char '=' **> go <*~
        let (N, id) ← string "in" **> TermM.pushVar id go
        return .let id none M N)
    <|> (label ∘ String.mk ∘ Array.toList ∘ Prod.fst) <$>
      (char '\'' *> takeUntil (char '\'') anyToken)
    <|> (prod ∘ .ofList ∘ Array.toList) <$> (char '{' **>
      sepBy (~*> char ',' <*~) (Prod.mk <$> go <**> liftM «▹» **> go) <** char '}')
    <|> sum <$> (char '[' **> go) <**> liftM «▹» **> go <** char ']'
    <|> prj <$> (string "prj" **> go false)
    <|> inj <$> (string "inj" **> go false)
    <|> (do
      let ϕ ← string "ind" **> monotype false
      let ρ ← ~*> monotype false
      let (M, as) ← ~*> TermM.pushTypeVars indIds (go false)
      let N ← ~*> go false
      return ind ϕ ρ as[0]! as[1]! as[2]! as[3]! as[4]! M N)
    <|> splitₚ <$> ((string "splitp" <|> string "splitₚ") **> monotype false) <**> go false
    <|> splitₛ <$> ((string "splits" <|> string "splitₛ") **> monotype false)
      <**> go false <**> go false
    <|> string "nil" *> pure nil
    <|> string "fold" *> pure fold
    <|> int <$> (String.toInt! ∘ String.mk ∘ Array.toList) <$> takeMany1 numeric
    <|> string "range" *> pure range
    <|> (str ∘ String.mk ∘ Array.toList ∘ Prod.fst) <$>
      (char '"' *> takeUntil (char '"') anyToken)
    <|> string "throw" *> pure Term.throw
    <|> (do
      let ρ ← (string "orderp" <|> string "orderₚ") **> monotype false
      let ((), xs) ← TermM.pushVars ["orderₚ$outer", "orderₚ$innerl", "orderₚ$inneracc"] <| pure ()
      let ((), as) ← TermM.pushTypeVars ("orderₚ$" :: indIds) <| pure ()
      return lam xs[0]! <|
        ind (.lam as[0]! (.row .star) (.app (.prodOrSum .prod (.comm .non)) (.var as[0]!))) ρ as[1]!
          as[2]! as[3]! as[4]! as[5]!
          (lam xs[1]! <|
            lam xs[2]! (concat (var xs[2]!) (.unlabel (prj (var xs[0]!)) (var xs[1]!))))
          (prod .nil))
    <|> (do
      let ρ ← (string "orders" <|> string "orderₛ") **> monotype false
      let ((), xs) ← TermM.pushVars
        ["orderₚ$outerl", "orderₚ$outeracc", "orderₚ$inner", "orderₚ$init"] <| pure ()
      let ((), as) ← TermM.pushTypeVars ("orderₚ$" :: indIds) <| pure ()
      return ind
        (.lam as[0]! (.row .star) (.arr
          (.app (.prodOrSum .sum (.comm .comm)) (.var as[0]!))
          (.app (.prodOrSum .sum (.comm .non)) (.var as[0]!)))) ρ as[1]! as[2]! as[3]! as[4]! as[5]!
        (lam xs[0]! <| lam xs[1]! <|
          elim (var xs[1]!)
            (lam xs[2]! (inj (sum (var xs[0]!) (.unlabel (var xs[2]!) (var xs[0]!))))))
        (lam xs[3]! (var xs[3]!)))
    -- TODO: These aren't actually the min/max... could probably make things more correct by
    -- erroring if we encounter anything out of range.
    <|> string "minInt" *> pure (int (- 2 ^ 63))
    <|> string "maxInt" *> pure (int (2 ^ 63 - 1))
    <|> (do
      let M ← string "if" **> go
      let (N₀, id₀) ← ~*> string "then" **> TermM.pushVar "if$then" go
      let (N₁, id₁) ← ~*> string "else" **> TermM.pushVar "if$else" go
      let τ := Monotype.row (uvars := true) (.cons (.label "true") .unit .nil) none |>.arr <|
        ← freshUVar
      return N₀.lam id₀ |>.annot τ |>.elim (N₁.lam id₁) |>.app M)
    <|> paren go
    <|> (do
      if allowFree then
        throwUnexpected

      let (_, termStartPos, termStopPos) ← withCapture <| go false false true
      let ((σ, vt), _, stopPos) ← ~*> char ':' **> withCapture typeScheme
      setPosition termStartPos
      let (M, _, termStopPos') ← withCapture <| TermM.includeTypeVars vt <|
        go false false false
      if termStopPos != termStopPos' then
        throwUnexpected
      setPosition stopPos
      return annot M σ)

  if !unlabel then
    return M

  let M' ← foldl Term.unlabel M <| ~*> char '/' **> go false false

  if !greedy then
    return M'

  let M'' ← foldl (fun M'' (isElim, M''') => if isElim then
      M''.elim M'''
    else
      M''.app M''') M' <|
    ~*> Prod.mk <$> (Option.isSome <$> option? (string "\\/" <|> string "▿")) <**> go false

  let tail :=
    (annot M'' ·.fst) <$> (~*> char ':' **> liftM typeScheme)
    <|>
    concat M'' <$> (~*> string "++" **> go)
    <|> cons M'' <$> (~*> string "::" **> go)
    <|> (.op · M'' ·) <$> (~*> op) <**> go

  optionD tail M''
where
  typeScheme := Parser.typeScheme true allowFree
  monotype (greedy := true) : TermM (Monotype true) := Parser.monotype true allowFree greedy
  indIds := ["l", "t", "rp", "ri", "rn"]
  go (greedy unlabel := true) (allowFree := allowFree) := term greedy unlabel allowFree

namespace Test

local
instance : OfNat (Id n) m where
  ofNat := { val := m }

local
instance : ToString (Id n) where
  toString | { val } => toString val

local
macro "#parse_term " input:str " to " expected:term : command =>
  `(#eval assertResultEq $input (α := Term true) (open Term in $expected) <|
      (term <* endOfInput) $input
        { mid := { nextFresh := 3 }, type := { id := { nextFresh := 3 } } }
        {
          defs := { "map", "true" }
          classToMember := { ("Eq", "eq"), ("LE", "le") }
          termVars := .ofList [("x", 0), ("y", 1), ("z", 2)] compare
          typeVars := .ofList [("a", 0), ("b", 1), ("c", 2)] compare
        } |>.fst)

#parse_term "y" to var 1
#parse_term "le" to member "le"
#parse_term "\\x : Int. x" to annot (lam 3 <| var 3) (Monotype.arr (uvars := true) .int (.uvar 0))
#parse_term "λ l acc. acc/l" to lam 3 <| lam 4 <| unlabel (var 4) (var 3)
#parse_term "let xs : List Int = nil in xs xs" to «let» 3 (Monotype.app (uvars := true) .list .int)
  nil <| app (var 3) (var 3)
#parse_term "let xs = nil in xs xs" to «let» 3 none nil <| app (var 3) (var 3)
#parse_term "(λ x : d. x) : ∀ d : *. d → d" to annot
  (annot (lam 5 (var 5)) (Monotype.arr (uvars := true) (.var 5) (.uvar 2)))
  (.quant 5 .star (Monotype.arr (uvars := true) (.var 5) (.var 5)))
#parse_term "''" to label ""
#parse_term "'asdf'" to label "asdf"
#parse_term "{}" to prod .nil
#parse_term "{'foo' ▹ 0, x |> \"hi\"}" to prod <| .cons (label "foo") (int 0) <|
  .cons (var 0) (str "hi") .nil
#parse_term "[z ▹ 5]" to sum (var 2) (int 5)
#parse_term "['baz' |> 0153]" to sum (label "baz") (int 153)
#parse_term "prj x/y z" to app (prj (unlabel (var 0) (var 1))) (var 2)
#parse_term "inj z/'hi'" to inj <| unlabel (var 2) (label "hi")
#parse_term "ind (λ d : R *. P(N) (Lift a d)) b (λ l acc. acc ++ {l : ⌊l⌋ ▹ 0}) {}" to ind
  (.lam 3 (.row .star)
    (.app (.prodOrSum .prod (.comm .non)) (.app (.app .lift (.var 0)) (.var 3))))
  (.var 1)
  4 5 6 7 8
  (lam 3 (lam 4 (concat (var 4)
    (prod (uvars := true) (.cons (annot (var 3) (Monotype.floor (uvars := true) (.var 4))) (int 0) .nil)))))
  (prod .nil)
#parse_term "x ▿ y z" to (var 0).elim (var 1) |>.app <| var 2
#parse_term "x \\/ y z" to (var 0).elim (var 1) |>.app <| var 2
#parse_term "splitₚ List nil" to splitₚ .list nil
#parse_term "splitp List (fold)" to splitₚ .list fold
#parse_term "splitₛ List range y" to splitₛ .list range (var 1)
#parse_term "splits List x y" to splitₛ .list (var 0) (var 1)
#parse_term "\"\"" to str ""
#parse_term "map" to «def» "map"
#parse_term "true" to «def» "true"
#parse_term "5 + 7" to .op .add (int 5) (int 7)
#parse_term "5 - 7" to .op .sub (int 5) (int 7)
#parse_term "5 * 7" to .op .mul (int 5) (int 7)
#parse_term "5 ÷ 7" to .op .div (int 5) (int 7)
#parse_term "5 // 7" to .op .div (int 5) (int 7)
#parse_term "5 == 7" to .op .eq (int 5) (int 7)
#parse_term "5 < 7" to .op .lt (int 5) (int 7)
#parse_term "5 ≤ 7" to .op .le (int 5) (int 7)
#parse_term "5 <= 7" to .op .le (int 5) (int 7)
#parse_term "5 > 7" to .op .gt (int 5) (int 7)
#parse_term "5 ≥ 7" to .op .ge (int 5) (int 7)
#parse_term "5 >= 7" to .op .ge (int 5) (int 7)

end Test

private
structure ProgramState where
  ctx : ProgramContext := { }
  term : TermState := { }
deriving Inhabited

private
abbrev ProgramM := SimpleParserT Substring Char <| StateM ProgramState

instance : MonadLift TermM ProgramM where
  monadLift p s s' :=
    let (res, s'') := p s s'.term { s'.ctx with }
    (res, { s' with term := s'' })

instance : MonadLift TypeM ProgramM where
  monadLift x := liftM <| liftM (n := TermM) x

private partial
def programEntry : ProgramM ProgramEntry := withErrorMessage "expected program entry" <|
  «def» <|> typeAlias <|> «class» <|> «instance»
where
  «def» : ProgramM ProgramEntry := do
    let x ← string "def" **> unreservedTermId
    let { ctx, .. } ← getModify (m := StateM ProgramState) fun st =>
      { st with ctx := { st.ctx with defs := st.ctx.defs.insert x } }
    if ctx.boundTerm.contains x then
      throwUnexpectedWithMessage none s!"redeclaration of '{x}'"
    let σvt? ← option? (~*> char ':' **> typeScheme false false)
    if let some (σ, vt) := σvt? then
      let M ← ~*> char '=' **> TermM.includeTypeVars vt term
      return .def x σ M
    else
      let M ← ~*> char '=' **> term
      return .def x none M
  typeAlias : ProgramM ProgramEntry := do
    let a ← string "type" **> unreservedTypeId
    let { ctx, .. } ← getModify (m := StateM ProgramState) fun st =>
      { st with ctx := { st.ctx with typeAliases := st.ctx.typeAliases.insert a } }
    if ctx.boundType.contains a then
      throwUnexpectedWithMessage none s!"redeclaration of '{a}'"
    let (σ, _) ← ~*> char '=' **> typeScheme false false
    return .typeAlias a σ
  «class» : ProgramM ProgramEntry := do
    let _ ← string "class" <*~
    let (TCₛs, as) ← Array.unzip <$> optionD
      (sepBy (~*> char ',' <*~) (Prod.mk <$> unreservedTypeId <**> unreservedTypeId) <** «⇒») #[]
    let TC ← ~*> unreservedTypeId
    let a ← ~*> unreservedTypeId
    if as.any (· != a) then
      throwUnexpectedWithMessage none "inconsistent type variables in superclasses"
    let κ ← ~*> char ':' **> kind
    let m ← ~*> string "where" **> unreservedTermId

    let { ctx := ctx@{ classToMember, .. }, .. } ← getModify (m := StateM ProgramState) fun st =>
      { st with ctx := { st.ctx with classToMember := st.ctx.classToMember.insert TC m } }
    if let some undeclared := TCₛs.find? (!classToMember.contains ·) then
      throwUnexpectedWithMessage none s!"superclass '{undeclared}' is undeclared"
    if ctx.boundType.contains TC then
      throwUnexpectedWithMessage none s!"redeclaration of '{TC}'"

    let ((σ, _), a) ← ~*> char ':' **> TypeM.pushVar a (typeScheme false false)
    return .class TCₛs.toList TC a κ m σ
  «instance» : ProgramM ProgramEntry := do
    let _ ← string "instance" <*~
    let (ψs, vt) ← liftM (m := TypeM) do
      let ψs ← optionD (sepBy (~*> char ',' <*~) (monotype false true) <** «⇒») #[]
      let { typeVars := vt, .. } ← get (m := StateM TypeContext)
      return (ψs, vt)

    let { classToMember, .. } ← read
    let TC ← ~*> unreservedTypeId
    let some expectedM := classToMember[TC]?
      | throwUnexpectedWithMessage none s!"class '{TC}' is undeclared"

    let τ ← ~*> liftM (m := TypeM) do
      modify (m := StateM TypeContext) fun ctx => { ctx with typeVars := vt }
      monotype false true
    let m ← ~*> string "where" **> unreservedTermId
    if m != expectedM then
      throwUnexpectedWithMessage none s!"incorrect member name '{m}', expected '{expectedM}'"
    let M ← ~*> char '=' **> term
    return .instance vt.values ψs.toList TC τ M

private
def program : ProgramM Program := ~*> Array.toList <$> sepBy ws programEntry <** endOfInput

def parse (s : String) := term.run s default default |>.fst
