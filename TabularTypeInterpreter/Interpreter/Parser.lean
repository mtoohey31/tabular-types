import TabularTypeInterpreter.Interpreter.Basic
import Parser
import Parser.Char

namespace TabularTypeInterpreter.Interpreter.Parser

open TabularTypeInterpreter.Interpreter
open _root_.Parser Char ASCII
open Std

private
abbrev KindParseM := SimpleParser Substring Char

private
def ws : KindParseM Unit :=
  dropMany <| tokenFilter [' ', '\n', '\r', '\t'].contains

local
infixl:60 " **> " => fun l r => l *> liftM ws *> r

local
infixl:60 " <** " => fun l r => l <* liftM ws <* r

local
infixl:60 " <**> " => fun l r => l <*> (liftM ws *> r)

local
prefix:60 "~*> " => fun r => liftM ws *> r

private
def paren [Monad m] [inst : MonadLiftT KindParseM m] (p : m α) : m α :=
  (liftM (self := inst) (char '(')) **> p <** (liftM (self := inst) (char ')'))

open Kind in
private partial
def kind (greedy := true) : KindParseM Kind := withErrorMessage "expected kind" do
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

abbrev VarTable := HashMap String Nat

structure S where
  termvars: VarTable
  typevars: VarTable
deriving Inhabited

abbrev ParseM := SimpleParserT Substring Char (StateM S)

instance : MonadLiftT KindParseM ParseM where
  monadLift p s := pure <| p s

namespace ParseM

def id : ParseM String :=
  (fun c cs => ⟨c::cs.toList⟩) <$> alpha <*> takeMany (alphanum <|> char '_')
def nat : ParseM Nat := do
  let x ← Array.toList <$> takeMany1 numeric
  return (String.mk x).toNat!
def string (s : String) : ParseM Unit := Char.string s *> pure ()
def char (c : Char) : ParseM Unit := Char.char c *> pure ()
def sepBy (pₐ : ParseM α) (sep : ParseM Unit): ParseM (List α) :=
  Parser.sepBy sep pₐ <&> Array.toList

def stringInner : ParseM String := do
  let (tokens, _) ← takeUntil (char '\"') anyToken
  return ⟨tokens.toList⟩

end ParseM

-- TODO: implement proper typeclas parsing
def typeclass : ParseM String := withErrorMessage "expected type class" ParseM.id

def var (get : ParseM VarTable) (set : VarTable -> ParseM Unit) (fresh? : Bool) : ParseM Nat := do
  let vars ← get
  let identifier ← ParseM.id
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

def typevar (fresh? : Bool) : ParseM Nat := withErrorMessage "expected type variable" <| var (get <&> S.typevars) (fun typevars => do set { ← get with typevars }) fresh?

def comm : ParseM Comm := withErrorMessage "expected commutativity" do
  char 'C' *> pure .comm
  <|> char 'N' *> pure .non

def prodOrSum : ParseM ProdOrSum := withErrorMessage "expected prod or sum" do
  (char 'P' <|> char 'Π') *> pure .prod
    <|> (char 'S' <|> char 'Σ') *> pure .sum

private
def «▹» : ParseM String := string "|>" <|> string "▹"

partial def monotype : ParseM Monotype := withErrorMessage "expected monotype" do
  let τ : Monotype ←
    paren monotype
    <|> string "Lift" *> pure .lift
    <|> string "All" *> pure .all
    <|> string "Ind" *> pure .ind
    <|> string "Split" *> pure .split
    <|> string "List" *> pure .list
    <|> string "Nat" *> pure .nat
    <|> string "Str" *> pure .str
    <|> .comm <$> comm
    <|> .prodOrSum <$> prodOrSum <**> paren monotype
    <|> .tc <$> typeclass
    <|> .var <$> typevar (fresh? := false)
    <|> .label <$> (char '.' *> ParseM.id <* char '.')
    -- TODO: I think we can avoid putting quotes around labels if we parse literal .floor separately
    <|> .floor <$> ((string "|_" <|> string "⌊") **> monotype <** (string "_|" <|> string "⌋"))
    <|> .lam <$> ((char '\\' <|> char 'λ') **> (typevar (fresh? := true)) **> char ':' **> kind)
      <**> (char '.' **> monotype)
    <|> (.row ∘ .ofList)
      <$> ((char '<' <|> char '⟨') **>
        (ParseM.sepBy (.mk <$> monotype <**> («▹» **> monotype)) (.string ",")))
        <**> ((option? <| char ':' **> kind) <** (char '>' <|> char '⟩'))

  let tail : ParseM Monotype :=
    .app τ <$> (~*> monotype)
    <|> .arr τ <$> (~*> (string "->" <|> string "→") **> monotype)
    <|> .contain τ
      <$> (~*> (string "~<" <|> string "≲") **> paren monotype)
      <**> monotype
    <|> .concat τ
      <$> (~*> (char 'o' <|> char '⊙') **> paren monotype)
      <**> monotype
      <**> (char '~' **> monotype)

  optionD tail τ

partial def qualifiedType : ParseM QualifiedType := withErrorMessage "expected qualified type" do
  let τ ← monotype
  optionD (QualifiedType.qual τ <$> (~*> (string "=>" <|> string "⇒") **> qualifiedType)) τ

partial def typescheme : ParseM TypeScheme := withErrorMessage  "expected type scheme" do
  TypeScheme.qual <$> qualifiedType
  <|> TypeScheme.quant
    <$> ((string "forall" <|> string "∀") **> (typevar (fresh? := true)) **> char ':' **> kind)
    <**> (char '.' **> typescheme)

def termvar (fresh? : Bool) : ParseM Nat := withErrorMessage "expected term variable" <| var (get <&> S.termvars) (fun termvars => do set { ← get with termvars }) fresh?

-- TODO: implement proper member parsing.
def member : ParseM String := withErrorMessage "expected member" do ParseM.id

def op : ParseM «λπι».Op := withErrorMessage "expected binary operator" do
  char '+' *> pure .add
  <|> char '-' *> pure .sub
  <|> char '*' *> pure .mul
  <|> char '/' *> pure .div

partial def term : ParseM Term := withErrorMessage "expected term" do
  let M : Term ←
    paren term
    <|> .member <$> member
    <|> .var <$> termvar (fresh? := false)
    <|> .label <$> (char '.' *> ParseM.id <* char '.')
    <|> .lam <$> ((char '\\' <|> char 'λ') **> (termvar (fresh? := true)) **> char '.' **> term)
    <|> .let <$> (string "let" **> (termvar (fresh? := true)) **> char ':' **> typescheme) <**>
      (char '=' **> term) <**> (string "in" **> term)
    <|> (.prod ∘ .ofList) <$> (char '{' **>
      (ParseM.sepBy (Prod.mk <$> term <**> («▹» **> term)) ((string ",") *> pure ())) <** char '}')
    <|> .sum <$> (char '[' **> term) <**> («▹» **> term <** char ']')
    <|> .prj <$> (string "prj" **> term)
    <|> .inj <$> (string "inj" **> term)
    <|> .ind <$> (string "ind" **> monotype) <**> monotype <**> (char ';' **> term) <**> (char ';' **> term)
    <|> .splitₚ <$> (string "splitₚ" **> monotype) <**> term
    <|> .splitₛ <$> (string "splitₛ" **> monotype) <**> term <**> (char ';' **> term)
    <|> .str <$> (char '"' *> ParseM.stringInner <* char '"')
    <|> .nat <$> ParseM.nat
    <|> string "nil" *> pure .nil
    <|> string "fold" *> pure .fold
    <|> string "range" *> pure .range

  let tail : ParseM Term :=
    .app M <$> (~*> term)
    <|> .annot M <$> (~*> char ':' **> typescheme)
    <|> .unlabel M <$> (~*> char '/' **> term)
    <|> .concat M <$> (~*> string "++" **> term)
    <|> .elim M <$> (~*> (string "\\/" <|> string "▿") **> term)
    <|> .cons M <$> (~*> string "::" **> term)
    <|> (fun o t => .op o M t) <$> (~*> op) <**> term

  optionD tail M

def parse (s : String) := term.run s ⟨∅, ∅⟩ |>.fst
