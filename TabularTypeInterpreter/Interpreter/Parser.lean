import TabularTypeInterpreter.Interpreter.Basic
import Parser
import Parser.Char

namespace TabularTypeInterpreter.Interpreter.Parser

open TabularTypeInterpreter.Interpreter
open _root_.Parser Char ASCII
open Std

private
abbrev CoreM := SimpleParser Substring Char

private
def ws : CoreM Unit := dropMany <| tokenFilter [' ', '\n', '\r', '\t'].contains

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

  optionD (default := κ) <| arr κ <$> (~*> (string "|->" <|> string "↦") **> kind)

private
def assertResultEq [BEq α] [ToString α] (expected : α)
  (result : Parser.Result (Parser.Error.Simple Substring Char) Substring α)
  : Lean.Elab.TermElabM Unit :=
  match result with
  | .ok _ actual => do
    if expected != actual then
      throwError "× -- expected: {expected}, actual: {actual}"
  | .error _ e => throwError "× -- {e}"

local
macro "#parse_kind " input:str " to " expected:term : command =>
  `(#eval assertResultEq (open Kind in $expected) ((kind <* endOfInput).run $input))

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
  classes : HashSet String := .empty
  methods : HashSet String := .empty
deriving Inhabited

private
structure TypeContext extends ProgramContext where
  -- The names of identifiers declared in enclosing type binders (either lambdas or foralls).
  typeVars : List String
deriving Inhabited

private
structure TypeInTermContext where
  nextFresh : Nat := 0
  -- A map from type var name to the id of the uvar which will represent it within the generalizing
  -- scope.
  varuvars : HashMap String Nat := .empty

private
abbrev TypeM := SimpleParserT Substring Char (StateT TypeInTermContext (ReaderM TypeContext))

private
def TypeM.pushTypeVars (ids : List String) : TypeM α → TypeM α :=
  fun x s s' r => x s s' { r with typeVars := ids ++ r.typeVars }

private
abbrev VarTable := HashMap String Nat

private
structure S where
  termvars: VarTable
  typevars: VarTable
deriving Inhabited

private
abbrev ParseM := SimpleParserT Substring Char (StateM S)

private
instance : MonadLiftT CoreM ParseM where
  monadLift p s := pure <| p s

private
instance : MonadLiftT CoreM TypeM where
  monadLift p s r _ := (p s, r)

private
instance : MonadLiftT TypeM ParseM where
  monadLift p s r := ((p s ·, r) { } |>.fst default |>.fst, r)

private
def rawId : CoreM String := (⟨· :: ·.toList⟩) <$> alpha <*> takeMany (alphanum <|> char '_')

private
def nat : CoreM Nat := (String.toNat! ∘ String.mk ∘ Array.toList) <$> takeMany1 numeric

def var (get : ParseM VarTable) (set : VarTable -> ParseM Unit) (fresh? : Bool) : ParseM Nat := do
  let vars ← get
  let identifier ← rawId
  if fresh? then
    if let .some n := vars.get? identifier then
      return n
    else
      --TODO: throw a more specific error.
      throwUnexpected
  else
    let n := vars.size
    -- TODO: duplicate identifiers get overwritten.
    -- I feel like this is fine as long as when we're done parsing a lambda, we discard the state of variables inside which I believe is what we do. Though I need confirmation.
    set (vars.insert identifier n)
    return n

private
def typeReserved :=
  ["C", "N", "P", "S", "Lift", "All", "Ind", "Split", "List", "Nat", "String", "o"]

private
def unreservedTypeId : TypeM String := do
  let id ← rawId
  if typeReserved.contains id then
    throwUnexpectedWithMessage none s!"use of reserved identifier '{id}'"

  return id

private
def typeId (inTerm : Bool) : TypeM (Monotype inTerm) := do
  let id ← unreservedTypeId

  let { typeVars, typeAliases, classes, .. } ← read
  if let some idx := typeVars.idxOf? id then
    return .var idx

  if classes.contains id then
    return .tc id

  if typeAliases.contains id then
    return .alias id

  match inTerm with
  | true =>
    let { nextFresh, varuvars } ← get
    if let some id := varuvars[id]? then
      return .varuvar id
    else
      set {
        nextFresh := nextFresh + 1
        varuvars := varuvars.insert id nextFresh : TypeInTermContext
      }
      return .varuvar nextFresh
  | false => throwUnexpectedWithMessage none "undeclared type var"

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
def monotype (inTerm : Bool) (greedy := true) : TypeM (Monotype inTerm) :=
  withErrorMessage "expected monotype" do
  let τ ← typeId inTerm
    <|> (do
      let _ ← char '\\' <|> char 'λ' <*~
      let idsκs ← sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> char ':' **> liftM kind) <** char '.' <*~
      let τ ← TypeM.pushTypeVars (idsκs.flatMap Prod.fst).toList.reverse go
      return idsκs.foldr (fun (ids, κ) τ' => ids.foldr (fun _ τ'' => lam κ τ'') τ') τ)
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
    <|> string "Nat" *> pure Monotype.nat
    <|> string "String" *> pure str
    <|> paren go

  if !greedy then
    return τ

  let τ' ← Array.foldl app τ <$> takeMany (~*> go false)

  let tail := arr τ' <$> (~*> (string "->" <|> string "→") **> go)
    <|> contain τ' <$> (~*> (string "~<" <|> string "≲") **> paren go) <**> go
    <|> concat τ' <$> (~*> (char 'o' <|> char '⊙') **> paren go) <**> go <**> (char '~' **> go)

  optionD tail τ'
where
  go (greedy := true) := monotype inTerm greedy

open QualifiedType in
partial
def qualifiedType (inTerm : Bool) : TypeM (QualifiedType inTerm) :=
  withErrorMessage "expected qualified type" do
  let τ ← monotype inTerm
  optionD (qual τ <$> (~*> (string "=>" <|> string "⇒") **> qualifiedType inTerm)) τ

open TypeScheme in
partial
def typeScheme (inTerm : Bool) : TypeM (TypeScheme inTerm) :=
  withErrorMessage "expected type scheme" <| (do
      let _ ← (string "forall" <|> string "∀") <*~
      let idsκs ← sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> char ':' **> liftM kind) <** char '.' <*~
      let σ ← TypeM.pushTypeVars (idsκs.flatMap Prod.fst).toList.reverse <| typeScheme inTerm
      return idsκs.foldr (fun (ids, κ) σ' => ids.foldr (fun _ σ'' => quant κ σ'') σ') σ)
      <|> qual <$> qualifiedType inTerm

local
macro "#parse_type " input:str " to " expected:term : command =>
  `(#eval assertResultEq (α := TypeScheme true)
      (open TypeScheme in open QualifiedType in open Monotype in $expected)
      <| (typeScheme true <* endOfInput) $input { } { typeVars := ["a", "b", "c"] } |>.fst)

#parse_type "b" to Monotype.var (uvars := true) 1
#parse_type "q" to varuvar 0
#parse_type "a b c" to app (uvars := true) (app (.var 0) (.var 1)) (.var 2)
#parse_type "λ a : *. a" to lam (uvars := true) .star (.var 0)
#parse_type "\\d : R *. a d" to lam (uvars := true) (.row .star) <| app (.var 1) (.var 0)
#parse_type "λ a b : *, c d : C. a d" to lam (uvars := true) .star <| lam .star <| lam .constr <|
  lam .constr <| app (.var 3) (.var 0)
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
#parse_type "a ≲(N) b" to contain (uvars := true) (.var 0) (Monotype.comm .non) (.var 1)
#parse_type "a b ~<(C) c d" to contain (uvars := true) (app (.var 0) (.var 1)) (Monotype.comm .comm)
  (app (.var 2) (varuvar 0))
#parse_type "a ⊙(N) b ~ c ⇒ a" to qual (uvars := true)
  (concat (.var 0) (Monotype.comm .non) (.var 1) (.var 2)) (mono (.var 0))
#parse_type "a o(C) b ~ c => a" to qual (uvars := true)
  (concat (.var 0) (Monotype.comm .comm) (.var 1) (.var 2)) (mono (.var 0))
#parse_type "Split a b c -> List a" to split (uvars := true) |>.app (.var 0) |>.app (.var 1)
  |>.app (.var 2) |>.arr (list.app <| .var 0)
#parse_type "Nat → String" to Monotype.nat (uvars := true) |>.arr str
#parse_type "∀ a : *. a" to quant (uvars := true) .star <| qual <| mono <| .var 0
#parse_type "forall d : R *. a d" to quant (uvars := true) (.row .star) <| qual <| mono <|
  app (.var 1) (.var 0)
#parse_type "∀ a b : *, c d : C. a d" to quant (uvars := true) .star <| quant .star <|
  quant .constr <| quant .constr <| qual <| mono <| app (.var 3) (.var 0)

def termvar (fresh? : Bool) : ParseM Nat := withErrorMessage "expected term variable" <| var (get <&> S.termvars) (fun termvars => do set { ← get with termvars }) fresh?

-- TODO: implement proper member parsing.
def member : ParseM String := withErrorMessage "expected member" rawId

def op : ParseM «λπι».Op := withErrorMessage "expected binary operator" do
  char '+' *> pure .add
  <|> char '-' *> pure .sub
  <|> char '*' *> pure .mul
  <|> char '/' *> pure .div

abbrev Term := Interpreter.Term true

open Term in
partial
def term : ParseM Term := withErrorMessage "expected term" do
  let M : Term ←
    paren term
    <|> Term.member <$> member
    <|> Term.var <$> termvar (fresh? := false)
    <|> label <$> (char '.' *> liftM rawId <* char '.')
    <|> lam <$> ((char '\\' <|> char 'λ') **> (termvar (fresh? := true)) **> char '.' **> term)
    <|> Term.«let» <$>
      (string "let" **> termvar (fresh? := true) **> char ':' **> typeScheme)
      <**> (char '=' **> term)
      <**> (string "in" **> term)
    <|> (prod ∘ .ofList ∘ Array.toList) <$> (char '{' **>
      (sepBy (string ",") (Prod.mk <$> term <**> liftM «▹» **> term)) <** char '}')
    <|> sum <$> (char '[' **> term) <**> liftM «▹» **> term <** char ']'
    <|> prj <$> (string "prj" **> term)
    <|> inj <$> (string "inj" **> term)
    <|> ind <$> (string "ind" **> monotype) <**> monotype
      <**> (char ';' **> term) <**> (char ';' **> term)
    <|> splitₚ <$> (string "splitₚ" **> monotype) <**> term
    <|> splitₛ <$> (string "splitₛ" **> monotype) <**> term <**> (char ';' **> term)
    <|> (str ∘ String.mk ∘ Array.toList ∘ Prod.fst) <$>
      (char '"' *> takeUntil (char '"') anyToken)
    <|> Term.nat <$> liftM nat
    <|> string "nil" *> pure nil
    <|> string "fold" *> pure fold
    <|> string "range" *> pure range

  let tail :=
    app M <$> (~*> term)
    <|> annot M <$> (~*> char ':' **> typeScheme)
    <|> unlabel M <$> (~*> char '/' **> term)
    <|> concat M <$> (~*> string "++" **> term)
    <|> elim M <$> (~*> (string "\\/" <|> string "▿") **> term)
    <|> cons M <$> (~*> string "::" **> term)
    <|> (fun o t => .op o M t) <$> (~*> op) <**> term

  optionD tail M
where
  typeScheme : ParseM (TypeScheme true) := liftM <| Parser.typeScheme true
  monotype : ParseM (Monotype true) := liftM <| Parser.monotype true

def parse (s : String) := term.run s ⟨∅, ∅⟩ |>.fst
