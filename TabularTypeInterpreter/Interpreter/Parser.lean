import Batteries.Data.RBMap
import TabularTypeInterpreter.Interpreter.Basic
import Lott.Data.Range
import Parser

namespace TabularTypeInterpreter.Interpreter.Parser

open TabularTypeInterpreter.Interpreter
open _root_.Parser
open Std

private
abbrev CoreM := ParserT Substring _root_.Id

private
def comment : CoreM Unit := string "--" *> «until» any (token '\n') *> pure ()

private
def ws : CoreM Unit :=
  drop <| many <| drop (tokenIf Char.isWhitespace "whitespace character") <|> comment

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
  (liftM (self := inst) (token '(')) **> p <** (liftM (self := inst) (token ')'))

open Kind in
private partial
def kind (greedy := true) : CoreM Kind := do
  let κ ← token '*' *> pure star
    <|> token 'L' *> pure label
    <|> token 'U' *> pure comm
    <|> token 'R' **> row <$> kind (greedy := false)
    <|> token 'C' *> pure constr
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
  s!"{pos.line s.toSubstring}:{pos.col s}"

def _root_.Parser.Error.toString (s : String) (e : Error String.Pos) : String :=
  let expected := e.expected.erase "\"--\"" |>.erase "whitespace character"
  s!"{String.Pos.lineAndCol e.position s}: expected {", ".intercalate expected.toList}"

private
def assertResultEq [BEq α] [ToString α] (input : String) (expected : α)
  (result : Except (Parser.Error String.Pos) α)
  : Lean.Elab.TermElabM Unit :=
  match result with
  | .ok actual => do
    if expected != actual then
      throwError "× -- expected: {expected}, actual: {actual}"
  | .error e => throwError "× -- {e.toString input}"

local
macro "#parse_kind " input:str " to " expected:term : command =>
  `(#eval assertResultEq $input (open Kind in $expected) ((kind <* eoi).run' ($input).toSubstring))

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

structure IdState (n : Name) where
  nextFresh : Nat
  private invertedVars : InvertedVarTable (Id n) := .empty

structure UVarState where
  nextFresh : Nat

structure TypeState where
  private id : IdState `type
  uvar : UVarState

private
abbrev TypeM := ParserT Substring <| StateT TypeState <| StateM TypeContext

private
def TypeM.pushVars (ids : List String) : TypeM α → TypeM (α × List TId) := fun x s e? s' r =>
  let filtered := ids.filter (· != "_")
  let ((((res, s), e?), s''), r') := x s e?
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
    ((((·, [s'.id.nextFresh:s'.id.nextFresh + ids.length].map Id.mk) <$> res, s), e?), s''),
    { r' with
      typeVars := filtered.foldl (init := r'.typeVars)
        fun acc id => if let some prev := r.typeVars.find? id then
            acc.insert id prev
          else
            acc.erase id
    }
  )

private
def TypeM.pushVar (id : String) : TypeM α → TypeM (α × TId) := fun x s e? s' r =>
  let ((((res, s), e?), s''), r') := x s e?
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
    ((((·, { val := s'.id.nextFresh }) <$> res, s), e?), s''),
    { r' with
      typeVars := if let some prev := r.typeVars.find? id then
          r'.typeVars.insert id prev
        else
          r'.typeVars.erase id
    }
  )

private
def TypeM.addVar (id : String) : TypeM TId := fun s e? s' r =>
  (
    (
      (
        (
          .ok { val := s'.id.nextFresh },
          s
        ),
        e?
      ),
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
def TypeM.getVars : TypeM (VarTable TId) := fun s e? s' r => ((((.ok r.typeVars, s), e?), s'), r)

private
instance : MonadLiftT CoreM TypeM where
  monadLift p s e? s' r := ((p s e?, s'), r)

private
def rawId : CoreM String := withReplaceExpected "identifier" <| (⟨· :: · ++ ·⟩) <$>
  (tokenIf Char.isAlpha "alpha char" <|> (token '_' *> pure '_')) <*>
    (many (tokenIf Char.isAlphanum "alphanum char" <|> (token '_' *> pure '_'))) <*>
    (many (token '\'' *> pure '\''))

private
def programReserved := ["def", "type", "class", "instance"]

private
def typeReserved := programReserved ++
  ["where", "C", "N", "P", "S", "Lift", "All", "Ind", "Split", "List", "Int", "String", "o"]

private
def unreservedTypeId : TypeM String := do
  let p ← getPosition
  let id ← rawId
  if typeReserved.contains id then
    throwExpectedAt s!"non-reserved identifier" p

  return id

private
def freshUVar : TypeM Monotype := do
  let { uvar := { nextFresh, .. }, .. } ← ParserT.lift <| getModify fun st =>
    { st with uvar := { st.uvar with nextFresh := st.uvar.nextFresh + 1 } }
  return .uvar { val := nextFresh }

private
def typeId (inTerm allowFree : Bool) : TypeM Monotype := do
  let p ← getPosition
  let id ← unreservedTypeId

  let { typeVars, typeAliases, classToMember, .. } ← get (m := StateM TypeContext)
  if let some id := typeVars.find? id then
    return .var id

  if inTerm && id == "_" then
    return ← freshUVar

  if classToMember.contains id then
    return .tc id

  if typeAliases.contains id then
    return .alias id

  if allowFree then return .var <| ← TypeM.addVar id

  throwExpectedAt s!"var '{id}' to be declared before use" p

private
def comm : TypeM Comm :=
  token 'C' *> pure Comm.comm <|> (token 'N' <* notFollowedBy (string "at")) *> pure .non

open ProdOrSum
private
def prodOrSum : TypeM ProdOrSum :=
  (token 'P' <|> token 'Π') *> pure prod <|> (token 'S' <|> token 'Σ') *> pure sum

private
def «▹» : TypeM Unit := string "|>" <|> string "▹"

private
def idsκs : TypeM (List (List String × Kind)) :=
  sepBy1 (~*> token ',' <*~) (Prod.mk <$> (sepBy1 ws unreservedTypeId) <**> token ':' **> kind)
    <** token '.' <*~

open Monotype in
private partial
def monotype (inTerm allowFree : Bool) (greedy := true) : TypeM Monotype := do
  let τ ← typeId inTerm allowFree
    <|> (do
      let idsκs ← (token '\\' <|> token 'λ') **> idsκs
      let (τ, idsκs) ← idsκs.foldr (init := ((·, [])) <$> go) fun (ids, κ) acc => do
        let ((τ, idsκs), ids) ← TypeM.pushVars ids acc
        return (τ, (ids, κ) :: idsκs)
      return idsκs.foldr (fun (ids, κ) τ' => ids.foldr (lam · κ ·) τ') τ)
    <|> (label ∘ String.mk ∘ Prod.fst) <$> (token '\'' *> «until» any (token '\''))
    <|> floor <$> ((string "|_" <|> string "⌊") **> go <** (string "_|" <|> string "⌋"))
    <|> Monotype.comm <$> comm
    <|> row
      <$> ((token '<' <|> token '⟨') **> (sepBy (~*> token ',' <*~) (Prod.mk <$> go <**> «▹» **> go)))
        <**> (option? (token ':' **> kind)) <** (token '>' <|> token '⟩')
    <|> Monotype.prodOrSum <$> prodOrSum <**> paren go
    <|> lift <$> (string "Lift" **> go false)
    <|> all <$> (string "All" **> go false)
    <|> ind <$> (string "Ind" **> go false)
    <|> split <$> (string "Split" **> go false) <**> go false <**> go false <**> go false
    <|> string "List" *> pure list
    <|> string "Int" *> pure int
    <|> string "String" *> pure str
    <|> paren go

  if !greedy then
    return τ

  let τ' ← foldl app τ <| ~*> go false

  let tail := arr τ' <$> (~*> (string "->" <|> string "→") **> go)
    <|> contain τ' <$> (~*> (string "~<" <|> string "≲") **> paren go) <**> go
    <|> concat τ' <$> (~*> (token 'o' <|> token '⊙') **> paren go) <**> go <**> (token '~' **> go)

  optionD τ' tail
where
  go (greedy := true) := monotype inTerm allowFree greedy

private
def «⇒» : CoreM Unit := string "=>" <|> string "⇒"

open QualifiedType in
private partial
def qualifiedType (inTerm allowFree : Bool) (commaPosition? : Option String.Pos := none) :
  TypeM QualifiedType := do
  let τ ← monotype inTerm allowFree
  let γ? ← option? <|
    ~*> (liftM «⇒» **> qualifiedType inTerm allowFree
          <|> getPosition <* string "," <*~ >>= (qualifiedType inTerm allowFree ·))
  match γ? with
  | none =>
    if let some commaPosition := commaPosition? then
      throwExpectedAt "qualified type with final separator of '⇒' instead of ','" commaPosition
    return τ
  | some γ => return qual τ γ

open TypeScheme in
private partial
def typeScheme (inTerm allowFree : Bool) : TypeM (TypeScheme × VarTable TId) :=
  (do
    let idsκs ← (string "forall" <|> string "∀") **> idsκs
    let ((σ, vt), idsκs) ← idsκs.foldr (init := ((·, [])) <$> typeScheme inTerm allowFree)
      fun (ids, κ) acc => do
        let ((σvt, idsκs), ids) ← TypeM.pushVars ids acc
        return (σvt, (ids, κ) :: idsκs)
    return (idsκs.foldr (fun (ids, κ) σ' => ids.foldr (quant · κ ·) σ') σ, vt))
    <|> (do
      let γ ← qualifiedType inTerm allowFree
      let vt ← TypeM.getVars
      return (qual γ, vt))

namespace Test

local
instance : OfNat UId n where
  ofNat := { val := n }

local
instance : ToString UId where
  toString | { val } => toString val

local
instance : OfNat TId n where
  ofNat := { val := n }

local
instance : ToString TId where
  toString | { val } => toString val

local
macro "#parse_type " input:str " to " expected:term : command =>
  `(#eval assertResultEq $input (α := TypeScheme)
      (open TypeScheme in open QualifiedType in open Monotype in $expected) <|
      Prod.fst <$>
        ((typeScheme true false <* eoi).run' ($input).toSubstring
          { id := { nextFresh := 3 }, uvar := { nextFresh := 0 } } {
          typeAliases := { "Option", "Bool" }
          classToMember := { ("Eq", "eq"), ("LE", "le") }
          typeVars := .ofList [("a", 0), ("b", 1), ("c", 2)] compare
        } |>.fst.fst))

#parse_type "b" to var 1
#parse_type "_ _" to uvar 0 |>.app <| uvar 1
#parse_type "a b c" to app (app (var 0) (var 1)) (var 2)
#parse_type "λ a : *. a" to lam 3 .star (var 3)
#parse_type "\\d : R *. a d" to lam 3 (.row .star) <| app (var 0) (var 3)
#parse_type "λ a b : *, c d : C. a d" to lam 3 .star <| lam 4 .star <|
  lam 5 .constr <| lam 6 .constr <| app (var 3) (var 6)
#parse_type "λ _ : *. _" to lam 3 .star <| uvar 0
#parse_type "''" to label ""
#parse_type "⌊'value'⌋" to floor (label "value")
#parse_type "C" to Monotype.comm .comm
#parse_type "N" to Monotype.comm .non
#parse_type "⟨⟩" to row .nil none
#parse_type "< : * >" to row .nil <| some .star
#parse_type "⟨'a' ▹ Lift a, 'b' |> (All b), ('c') ▹ Ind c⟩" to row
  [(label "a", lift (var 0)), (label "b", all (var 1)), (label "c", ind (var 2))] none
#parse_type "Π(N) ⟨⟩" to Monotype.prodOrSum .prod (.comm .non) |>.app <|
  row .nil none
#parse_type "P(C)" to Monotype.prodOrSum .prod <| .comm .comm
#parse_type "Σ(C)" to Monotype.prodOrSum .sum <| .comm .comm
#parse_type "S(N)" to Monotype.prodOrSum .sum <| .comm .non
#parse_type "a ≲(N) b" to contain (var 0) (Monotype.comm .non) (var 1)
#parse_type "a b a ~<(C) c a" to contain (app (app (var 0) (var 1)) (var 0))
  (Monotype.comm .comm) (app (var 2) (var 0))
#parse_type "a ⊙(N) b ~ c ⇒ a" to qual
  (concat (var 0) (Monotype.comm .non) (var 1) (var 2)) (mono (var 0))
#parse_type "a o(C) b ~ c => a" to qual
  (concat (var 0) (Monotype.comm .comm) (var 1) (var 2)) (mono (var 0))
#parse_type "Eq" to tc "Eq"
#parse_type "LE" to tc "LE"
#parse_type "Split a a b c -> List a" to split (var 0) (var 0) (var 1) (var 2)
  |>.arr (list.app <| var 0)
#parse_type "Int → String" to int |>.arr str
#parse_type "∀ a : *. a" to quant 3 .star <| qual <| mono <| var 3
#parse_type "forall d : R *. a d" to quant 3 (.row .star) <| qual <| mono <|
  app (var 0) (var 3)
#parse_type "∀ a b : *, c d : C. a d" to quant 3 .star <| quant 4 .star <|
  quant 5 .constr <| quant 6 .constr <| qual <| mono <| app (var 3) (var 6)
#parse_type "Bool" to «alias» "Bool"
#parse_type "Option" to «alias» "Option"

end Test

private
structure TermContext extends TypeContext where
  termVars : VarTable MId := .empty
deriving Inhabited

structure TermState where
  mid : IdState `term
  type : TypeState

private
abbrev TermM := ParserT Substring <| StateT TermState <| ReaderM TermContext

namespace TermM

private
def pushVars (ids : List String) : TermM α → TermM (α × List MId) := fun x s e? s' r =>
  (((·, [s'.mid.nextFresh:s'.mid.nextFresh + ids.length].map Id.mk)) <$> x) s e?
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
def pushVar (id : String) : TermM α → TermM (α × MId) := fun x s e? s' r =>
  ((·, { val := s'.mid.nextFresh }) <$> x) s e?
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
def includeTypeVars (vt : VarTable TId) : TermM α → TermM α := fun x s e? s' r =>
  x s e? s' { r with typeVars := r.typeVars.mergeWith (fun _ _ id => id) vt }

private
def pushTypeVars (ids : List String) : TermM α → TermM (α × List TId) := fun x s e? s' r =>
  let filtered := ids.filter (· != "_")
  ((·, [s'.type.id.nextFresh:s'.type.id.nextFresh + ids.length].map Id.mk) <$> x) s e?
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
def pushTypeVar (id : String) : TermM α → TermM (α × TId) := fun x s e? s' r =>
  ((·, { val := s'.type.id.nextFresh }) <$> x) s e?
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
  monadLift p s e? s' r :=
    let ((x, s''), _) := p s e? s'.type r.toTypeContext
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
  let p ← getPosition
  let id ← liftM rawId
  if termReserved.contains id then
    throwExpectedAt s!"non-reserved identifier" p

  return id

private
def termId : TermM Term := do
  let p ← getPosition
  let id ← unreservedTermId

  let { termVars, defs, classToMember, .. } ← read
  if let some id := termVars.find? id then
    return .var id

  if classToMember.values.contains id then
    return .member id

  if defs.contains id then
    return .def id

  throwExpectedAt s!"var '{id}' to be declared before use" p

private
def op : TermM «λπι».Op :=
  token '+' *> pure .add
    <|> token '-' *> pure .sub
    <|> token '*' *> pure .mul
    <|> (string "//" <|> string "÷") *> pure .div
    <|> string "==" *> pure .eq
    <|> (string "<=" <|> string "≤") *> pure .le
    <|> token '<' *> pure .lt
    <|> (string ">=" <|> string "≥") *> pure .ge
    <|> token '>' *> pure .gt

open Term in
private partial
def term' (greedy unlabel := true) (allowFree := false) : TermM Term := do
  let M ← termId
    <|> (do
      let idsτ?s ← (token '\\' <|> token 'λ') **> sepBy1 (~*> token ',' <*~)
        (Prod.mk <$> sepBy1 ws unreservedTermId <**> option? (token ':' **> monotype true))
        <** token '.' <*~
      let (M, idsτ?s) ← idsτ?s.foldr (init := ((·, [])) <$> go) fun (ids, τ?) acc => do
        let ((τ, idsτ?s), ids) ← TermM.pushVars ids acc
        return (τ, (ids, τ?) :: idsτ?s)
      idsτ?s.foldrM (init := M) fun (ids, τ?) M' =>
        ids.foldrM (init := M') fun id M'' =>
          if let some τ := τ? then
            return annot (lam id M'') <| Monotype.arr τ <| ← freshUVar
          else
            return lam id M'')
    <|> (do
      let id ← string "let" **> unreservedTermId <*~
      let σvt? ← option? (token ':' **> typeScheme <*~)
      if let some (σ, vt) := σvt? then
        let M ← token '=' **> TermM.includeTypeVars vt go <*~
        let (N, id) ← string "in" **> TermM.pushVar id go
        return .let id σ M N
      else
        let M ← token '=' **> go <*~
        let (N, id) ← string "in" **> TermM.pushVar id go
        return .let id none M N)
    <|> (label ∘ String.mk ∘ Prod.fst) <$>
      (token '\'' *> «until» any (token '\''))
    <|> prod <$>
      (token '{' **> sepBy (~*> token ',' <*~) (Prod.mk <$> go <**> liftM «▹» **> go) <** token '}')
    <|> sum <$> (token '[' **> go) <**> liftM «▹» **> go <** token ']'
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
    <|> (do
      let ((), xs) ← string "fold" *> (TermM.pushTypeVars ["fold$list", "fold$acc"] <| pure ())
      return fold xs[0]! xs[1]!)
    <|> int <$> (String.toInt! ∘ String.mk) <$> many1 (tokenIf Char.isDigit "numeric character")
    <|> string "range" *> pure range
    <|> (str ∘ String.mk ∘ Prod.fst) <$> (token '"' *> «until» any (token '"'))
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
      let τ := Monotype.row [(.label "true", .unit)] none |>.arr <| ← freshUVar
      return N₀.lam id₀ |>.annot τ |>.elim (N₁.lam id₁) |>.app M)
    <|> paren go
    <|> (do
      if allowFree then
        throwExpected "non-annotation term when free variables are allowed"

      let st ← get
      let termStartPos ← getPosition
      drop <| go false false true
      let termStopPos ← getPosition
      set st
      let (σ, vt) ← ~*> token ':' **> typeScheme
      let stopPos ← getPosition
      setPosition termStartPos
      let M ← TermM.includeTypeVars vt <| go false false false
      let termStopPos' ← getPosition
      if termStopPos != termStopPos' then
        throwExpected "re-parse of term with vars to consume the same number of tokens"
      setPosition stopPos
      return annot M σ)

  if !unlabel then
    return M

  let M' ← foldl Term.unlabel M <| ~*> token '/' **> go false false

  if !greedy then
    return M'

  let M'' ← foldl (fun M'' (isElim, M''') => if isElim then
      M''.elim M'''
    else
      M''.app M''') M' <|
    ~*> Prod.mk <$> (Option.isSome <$> option? (string "\\/" <|> string "▿")) <**> go false

  let tail :=
    (annot M'' ·.fst) <$> (~*> token ':' **> liftM typeScheme)
    <|>
    concat M'' <$> (~*> string "++" **> go)
    <|> cons M'' <$> (~*> string "::" **> go)
    <|> (.op · M'' ·) <$> (~*> op) <**> go

  optionD M'' tail
where
  typeScheme := Parser.typeScheme true allowFree
  monotype (greedy := true) : TermM Monotype := Parser.monotype true allowFree greedy
  indIds := ["l", "t", "rp", "ri", "rn"]
  go (greedy unlabel := true) (allowFree := allowFree) := term' greedy unlabel allowFree

namespace Test

local
instance : OfNat (Id n) m where
  ofNat := { val := m }

local
instance : ToString (Id n) where
  toString | { val } => toString val

local
macro "#parse_term " input:str " to " expected:term : command =>
  `(#eval assertResultEq $input (α := Term) (open Term in $expected) <|
      (term' <* eoi).run' ($input).toSubstring
        {
          mid := { nextFresh := 3 },
          type := {
            id := { nextFresh := 3 },
            uvar := { nextFresh := 0 }
          }
        }
        {
          defs := { "map", "true" }
          classToMember := { ("Eq", "eq"), ("LE", "le") }
          termVars := .ofList [("x", 0), ("y", 1), ("z", 2)] compare
          typeVars := .ofList [("a", 0), ("b", 1), ("c", 2)] compare
        } |>.fst)

#parse_term "y" to var 1
#parse_term "le" to member "le"
#parse_term "\\x : Int. x" to annot (lam 3 <| var 3) (Monotype.arr .int (.uvar 0))
#parse_term "λ l acc. acc/l" to lam 3 <| lam 4 <| unlabel (var 4) (var 3)
#parse_term "let xs : List Int = nil in xs xs" to «let» 3 (Monotype.app .list .int)
  nil <| app (var 3) (var 3)
#parse_term "let xs = nil in xs xs" to «let» 3 none nil <| app (var 3) (var 3)
#parse_term "(λ x : d. x) : ∀ d : *. d → d" to annot
  (annot (lam 3 (var 3)) (Monotype.arr (.var 3) (.uvar 0)))
  (.quant 3 .star (Monotype.arr (.var 3) (.var 3)))
#parse_term "''" to label ""
#parse_term "'asdf'" to label "asdf"
#parse_term "{}" to prod .nil
#parse_term "{'foo' ▹ 0, x |> \"hi\"}" to prod [(label "foo", int 0), (var 0, str "hi")]
#parse_term "[z ▹ 5]" to sum (var 2) (int 5)
#parse_term "['baz' |> 0153]" to sum (label "baz") (int 153)
#parse_term "prj x/y z" to app (prj (unlabel (var 0) (var 1))) (var 2)
#parse_term "inj z/'hi'" to inj <| unlabel (var 2) (label "hi")
#parse_term "ind (λ d : R *. P(N) (Lift a d)) b (λ l acc. acc ++ {l : ⌊l⌋ ▹ 0}) {}" to ind
  (.lam 3 (.row .star)
    (.app (.prodOrSum .prod (.comm .non)) (.app (.lift (.var 0)) (.var 3))))
  (.var 1)
  4 5 6 7 8
  (lam 3 (lam 4 (concat (var 4) (prod [(annot (var 3) (Monotype.floor (.var 4)), int 0)]))))
  (prod [])
#parse_term "x ▿ y z" to (var 0).elim (var 1) |>.app <| var 2
#parse_term "x \\/ y z" to (var 0).elim (var 1) |>.app <| var 2
#parse_term "splitₚ List nil" to splitₚ .list nil
#parse_term "splitp List (fold)" to splitₚ .list (fold 3 4)
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

structure ProgramState where
  private ctx : ProgramContext := { }
  term : TermState

def ProgramState.updateTermNextFresh (st : ProgramState) (nextFresh : Nat) :=
  { st with term := { st.term with mid := { st.term.mid with nextFresh } } }

private
abbrev ProgramM := ParserT Substring <| StateM ProgramState

instance : MonadLift TermM ProgramM where
  monadLift p s e? s' :=
    let (res, s'') := p s e? s'.term { s'.ctx with }
    (res, { s' with term := s'' })

instance : MonadLift TypeM ProgramM where
  monadLift x := liftM <| liftM (n := TermM) x

private partial
def programEntry : ProgramM ProgramEntry := «def» <|> typeAlias <|> «class» <|> «instance»
where
  «def» : ProgramM ProgramEntry := do
    let xp ← string "def" **> getPosition
    let x ← unreservedTermId
    let { ctx, .. } ← getModify (m := StateM ProgramState) fun st =>
      { st with ctx := { st.ctx with defs := st.ctx.defs.insert x } }
    if ctx.boundTerm.contains x then
      throwExpectedAt s!"unused term identifer" xp
    let σvt? ← option? (~*> token ':' **> typeScheme false false)
    if let some (σ, vt) := σvt? then
      let M ← ~*> token '=' **> TermM.includeTypeVars vt term'
      return .def x σ M
    else
      let M ← ~*> token '=' **> term'
      return .def x none M
  typeAlias : ProgramM ProgramEntry := do
    let ap ← string "type" **> getPosition
    let a ← unreservedTypeId
    let { ctx, .. } ← getModify (m := StateM ProgramState) fun st =>
      { st with ctx := { st.ctx with typeAliases := st.ctx.typeAliases.insert a } }
    if ctx.boundType.contains a then
      throwExpectedAt s!"unused type identifier" ap
    let (σ, _) ← ~*> token '=' **> typeScheme false false
    return .typeAlias a σ
  «class» : ProgramM ProgramEntry := do
    let _ ← string "class" <*~
    let (TCₛsps, as) ← Functor.map (f := ProgramM) List.unzip <| option! <|
      sepBy (~*> token ',' <*~) ((fun TCₛp TCₛ as => ((TCₛp, TCₛ), as)) <$>
        getPosition <*> unreservedTypeId <**> unreservedTypeId) <** «⇒»
    let TCp ← ~*> getPosition
    let TC ← unreservedTypeId
    let ap ← ~*> getPosition
    let a ← unreservedTypeId
    if as.any (· != a) then
      throwExpectedAt "superclasses type variables to match parameter type variable" ap
    let κ ← ~*> token ':' **> kind
    let m ← ~*> string "where" **> unreservedTermId

    let { ctx := ctx@{ classToMember, .. }, .. } ← getModify (m := StateM ProgramState) fun st =>
      { st with ctx := { st.ctx with classToMember := st.ctx.classToMember.insert TC m } }
    if let some (p, _) := TCₛsps.find? (!classToMember.contains ·.snd) then
      throwExpectedAt s!"previously declared type class" p
    let (_, TCₛs) := TCₛsps.unzip
    if ctx.boundType.contains TC then
      throwExpectedAt s!"unused type identifier" TCp

    let ((σ, _), a) ← ~*> token ':' **> TypeM.pushVar a (typeScheme false false)
    return .class { TCₛs, TC, a, κ, m, σ }
  «instance» : ProgramM ProgramEntry := set_option linter.deprecated false in do
    let idsκs ← string "instance" **> option! ((string "forall" <|> string "∀") **> idsκs)
    let { classToMember, .. } ← read
    let init : TermM _ := do
      let ψs ← option! <| sepBy1 (~*> token ',' <*~) (monotype false false) <** «⇒»
      let TCp ← ~*> getPosition
      let TC ← unreservedTypeId
      let some expectedM := classToMember[TC]?
        | throwExpectedAt s!"name of declared class" TCp

      let τ ← ~*> monotype false false
      let mp ← ~*> string "where" **> getPosition
      let m ← unreservedTermId
      if m != expectedM then
        throwExpectedAt s!"member name matching '{expectedM}' from the class name" mp
      let M ← ~*> token '=' **> term'

      return (ψs, TC, τ, M)

    let ((ψs, TC, τ, M), aκs) ← liftM (m := TermM) <| idsκs.foldr (init := ((·, []) <$> init))
      fun (ids, κ) acc => do
        let ((res, aκs), as) ← TermM.pushTypeVars ids acc
        return (res, as.map (·, κ) ++ aκs)

    return .instance aκs ψs TC τ M

private
def program' : ProgramM Program := ~*> sepBy ws programEntry <** eoi

abbrev ParseM := StateM ProgramState

def program (s : String) : ParseM (Except (Error String.Pos) Program) := program'.run' s.toSubstring

def term (s : String) : ParseM (Except (Error String.Pos) Term) := do
  let st ← get
  let (res, st') := (term' <** eoi).run' s.toSubstring st.term { st.ctx with }
  set { st with term := st' }
  return res
