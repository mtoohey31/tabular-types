import TabularTypeInterpreter.Interpreter.Basic
import Parser
import Parser.Char

namespace TabularTypeInterpreter.Parser

open TabularTypeInterpreter.Interpreter
open Parser
open Parser.Char
open Parser.Char.ASCII
open Std

structure S where
  next : Nat
deriving Inhabited

abbrev ParseM := SimpleParserT Substring Char (StateM S)

namespace ParseM

def ws : ParseM Unit := Parser.dropMany <|
  Parser.tokenFilter [' ', '\n', '\r', '\t'].contains
def id : ParseM String :=
  (fun c cs => ⟨c::cs.toList⟩) <$> alpha <*> Parser.takeMany (alphanum <|> char '_')
infixl:60 " **> " => fun l r => l *> ws *> r
infixl:60 " <** " => fun l r => l <* ws <* r
infixl:60 " <**> " => fun l r => l <*> (ws *> r)
def paren (p : ParseM α) : ParseM α :=
  char '(' **> p <** char ')'
def nat : ParseM Nat := do
  let x ← Array.toList <$> Parser.takeMany1 numeric
  return (String.mk x).toNat!
def string (s : String) : ParseM Unit := Parser.Char.string s *> pure ()
def char (c : Char) : ParseM Unit := Parser.Char.char c *> pure ()
partial def sepBy (pₐ : ParseM α) (sep : ParseM Unit): ParseM (List α) :=
  Parser.sepBy1 sep pₐ <&> Array.toList

-- terminals
def «Ind» : ParseM Unit := .string "Ind"
def «Lift» : ParseM Unit := .string "Lift"
def «All» : ParseM Unit := .string "All"
def «Split» : ParseM Unit := .string "Split"
def «List» : ParseM Unit := .string "List"
def «Nat» : ParseM Unit := .string "Nat"
def «Str» : ParseM Unit := .string "String"
def «let» : ParseM Unit := .string "let"
def «in» : ParseM Unit := .string "in"
def «prj» : ParseM Unit := .string "prj"
def «inj» : ParseM Unit := .string "inj"
def «order» : ParseM Unit := .string "order"
def «ind» : ParseM Unit := .string "ind"
def «splitₚ» : ParseM Unit := .string "splitₚ"
def «splitₛ» : ParseM Unit := .string "splitₛ"
def «nil» : ParseM Unit := .string "nil"
def «fold» : ParseM Unit := .string "fold"
def «range» : ParseM Unit := .string "range"
def «'» : ParseM Unit := .char '\''
def «"» : ParseM Unit := .char '"'
def «~» : ParseM Unit := .char '~'
def «.» : ParseM Unit := .char '.'
def «:» : ParseM Unit := .char ':'
def «=» : ParseM Unit := .char '='
def «/» : ParseM Unit := .char '/'
def «;» : ParseM Unit := .char ';'
def «++» : ParseM Unit := .string "++"
def «::» : ParseM Unit := .string "::"
def «⇒» : ParseM Unit := .string "=>" <|> .char '⇒'
def «▹» : ParseM Unit := .string "|>" <|> .char '▹'
-- TODO: What's the best ascii version of `▿`?
def «▿» : ParseM Unit := .char 'v' <|> .char '▿'
def «∀» : ParseM Unit := .string "forall" <|> .char '∀'
def «⊙» : ParseM Unit := .char 'o' <|> .char '⊙'
def «⊙'» : ParseM Unit := .«⊙» *> .char '\''
def «λ» : ParseM Unit := .char '\\' <|> .char 'λ'
def «≲» : ParseM Unit := .string "~<" <|> .char '≲'
def «→» : ParseM Unit := .string "->" <|> .char '→'
def «↦» : ParseM Unit := .string "|->" <|> .char '↦'
def «⌊» : ParseM Unit := .string "[_" <|> .char '⌊'
def «⌋» : ParseM Unit := .string "_]" <|> .char '⌋'
def «⟨» : ParseM Unit := .char '<' <|> .char '⟨'
def «⟩» : ParseM Unit := .char '>' <|> .char '⟩'
def «[» : ParseM Unit := .char '['
def «]» : ParseM Unit := .char ']'
def «{» : ParseM Unit := .char '{'
def «}» : ParseM Unit := .char '}'

def stringInner : ParseM String := do
  let (tokens, _) ← Parser.takeUntil (char '\"') Parser.anyToken
  return ⟨tokens.toList⟩

end ParseM

partial def kind : ParseM Kind := Parser.withErrorMessage "expected kind" do
  let κ : Kind ←
    (char '*' <|> char '⋆') *> pure Kind.star
    <|> char 'L' *> pure Kind.label
    <|> char 'U' *> pure Kind.comm
    <|> char 'R' **> Kind.row <$> kind
    <|> ParseM.paren kind
  let tail: ParseM Kind := Kind.arr κ <$> (.ws *> ParseM.«↦» **> kind)
  Parser.optionD tail κ

def typeClass : ParseM String := Parser.withErrorMessage "expected type class" ParseM.id

def typevar : ParseM Nat := Parser.withErrorMessage "expected type variable" do
  return (← ParseM.id).hash.toNat

def comm : ParseM Comm := Parser.withErrorMessage "expected commutativity" do
  char 'C' *> pure .comm
  <|> char 'N' *> pure .non

def prodOrSum : ParseM ProdOrSum := Parser.withErrorMessage "expected prod or sum" do
  char 'Π' *> pure .prod
  <|> char 'Σ' *> pure .sum

partial def monotype : ParseM Monotype := Parser.withErrorMessage "expected monotype" do
  let τ : Monotype ←
    .paren monotype
    <|> .«Lift» *> pure .lift
    <|> .«All» *> pure .all
    <|> .«ind» *> pure .ind
    <|> .«Split» *> pure .split
    <|> .«List» *> pure .list
    <|> .«Nat» *> pure .nat
    <|> .«Str» *> pure .str
    <|> .comm <$> comm
    <|> .prodOrSum <$> prodOrSum <**> (.paren monotype)
    <|> .tc <$> typeClass
    <|> .var <$> typevar
    <|> .label <$> (.«'» *> .id <* .«'»)
    -- TODO: I think we can avoid putting quotes around labels if we parse literal .floor separately
    <|> .floor <$> (.«⌊» **> monotype <** .«⌋»)
    <|> .lam <$> (.«λ» **> typevar **> .«:» **> kind) <**> (.«.» **> monotype)
    <|> .row
      <$> (.«⟨» **> (.sepBy (.mk <$> monotype <**> (.«▹» **> monotype)) (.string ",")))
      <**> ((Parser.option? <| .«:» **> kind) <** .«⟩»)

  let tail : ParseM Monotype := 
    .app τ <$> (.ws *> monotype)
    <|> .arr τ <$> (.ws *> .«→» **> monotype)
    <|> .contain τ
      <$> (.ws *> .«≲» **> .paren monotype) 
      <**> monotype
    <|> .concat τ
      <$> (.ws *> .«⊙» **> .paren monotype)
      <**> monotype
      <**> (.«~» **> monotype)

  Parser.optionD tail τ

partial def qualifiedType : ParseM QualifiedType := Parser.withErrorMessage "expected qualified type" do
  let τ ← monotype
  Parser.optionD (QualifiedType.qual τ <$> (.ws *> .«⇒» **> qualifiedType)) τ

partial def typescheme : ParseM TypeScheme := Parser.withErrorMessage  "expected type scheme" do
  TypeScheme.qual <$> qualifiedType
  <|> TypeScheme.quant
    <$> (ParseM.«∀» **> typevar **> ParseM.«:» **> kind)
    <**> (ParseM.«.» **> typescheme)

def termvar : ParseM Nat := Parser.withErrorMessage "expected term variable" do
  return (← ParseM.id).hash.toNat

def member : ParseM String := Parser.withErrorMessage "expected member" do ParseM.id

def op : ParseM «λπι».Op := Parser.withErrorMessage "expected binary operator" do
  char '+' *> pure .add
  <|> char '-' *> pure .sub
  <|> char '*' *> pure .mul
  <|> char '/' *> pure .div

partial def term : ParseM Term := Parser.withErrorMessage "expected term" do
  let M : Term ←
    .paren term
    <|> .member <$> member
    <|> .var <$> termvar
    <|> .label <$> (.«'» *> .id <* .«'»)
    <|> .lam <$> (.«λ» **> termvar **> .«.» **> term)
    <|> .let <$> (.«let» **> termvar **> .«:» **> typescheme) <**> (.«=» **> term) <**> (.«in» **> term)
    <|> .prod <$> (ParseM.«{» **> (.sepBy (Prod.mk <$> term <**> (ParseM.«▹» **> term)) (.string ",")) <** ParseM.«}»)
    <|> .sum <$> (.«[» **> term) <**> (.«▹» **> term <** .«]»)
    <|> .prj <$> (.«prj» **> term)
    <|> .inj <$> (.«inj» **> term)
    <|> .order <$> (.«order» **> monotype) <**> term
    <|> .ind <$> (.«ind» **> monotype) <**> monotype <**> (.«;» **> term) <**> (.«;» **> term)
    <|> .splitₚ <$> (.«splitₚ» **> monotype) <**> term
    <|> .splitₛ <$> (.«splitₛ» **> monotype) <**> term <**> (.«;» **> term)
    <|> .str <$> (.«"» *> ParseM.stringInner <* .«"»)
    <|> .nat <$> .nat
    <|> .«nil» *> pure .nil
    <|> .«fold» *> pure .fold
    <|> .«range» *> pure .range

  let tail : ParseM Term := 
    .app M <$> (.ws *> term)
    <|> .annot M <$> (.ws *> .«:» **> typescheme)
    <|> .unlabel M <$> (.ws *> .«/» **> term)
    <|> .concat M <$> (.ws *> .«++» **> term)
    <|> .elim M <$> (.ws *> .«▿» **> term)
    <|> .cons M <$> (.ws *> .«::» **> term)
    <|> (fun o t => .op o M t) <$> (.ws *> op) <**> term

  Parser.optionD tail M
