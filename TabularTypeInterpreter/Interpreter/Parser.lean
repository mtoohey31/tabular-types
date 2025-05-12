import TabularTypeInterpreter.Syntax
import Parser
import Parser.Char

namespace TabularTypeInterpreter.Parser

open Parser
open Parser.Char
open Parser.Char.ASCII
open Std

def Kind.toString : Kind → String
| .star => "*"
| .arr κ₁ κ₂ => s!"{Kind.toString κ₁} |-> {Kind.toString κ₂}"
| .label => "L"
| .comm => "U"
| .row κ => s!"R {Kind.toString κ}"
| .constr => "C"
instance : ToString Kind := ⟨Kind.toString⟩
instance : Inhabited Kind := ⟨.star⟩
instance : Inhabited Commutativity := ⟨.comm⟩
instance : Inhabited Monotype := ⟨.row [] .none⟩
instance : Inhabited QualifiedType := ⟨.mono default⟩
instance : Inhabited TypeScheme := ⟨.qual default⟩
instance : Inhabited TypeLambda := ⟨TypeLambda.mk default default⟩
instance : Inhabited Term := ⟨.prod []⟩

structure S where
  next : Nat
deriving Inhabited

abbrev ParseM := SimpleParserT Substring Char (StateM S)
-- helpers
def ws : ParseM Unit := Parser.dropMany <|
  Parser.tokenFilter [' ', '\n', '\r', '\t'].contains
infixl:60 " **> " => fun l r => l *> ws *> r
infixl:60 " <** " => fun l r => l <* ws <* r
infixl:60 " <**> " => fun l r => l <*> (ws *> r)
def ParseM.paren (p : ParseM α) : ParseM α :=
  char '(' **> p <** char ')'
def ParseM.string (s : String) : ParseM Unit := Parser.Char.string s *> pure ()
def ParseM.char (c : Char) : ParseM Unit := Parser.Char.char c *> pure ()
partial def ParseM.sepBy (pₐ : ParseM α) (sep : ParseM Unit): ParseM (List α) :=
  Parser.optionD (List.cons <$> pₐ <**> (Parser.optionD (sep **> sepBy pₐ sep) [])) []

-- terminals
def ParseM.«Ind» : ParseM Unit := .string "Ind"
def ParseM.«Lift» : ParseM Unit := .string "Lift"
def ParseM.«All» : ParseM Unit := .string "All"
def ParseM.«Split» : ParseM Unit := .string "Split"
def ParseM.«let» : ParseM Unit := .string "let"
def ParseM.«in» : ParseM Unit := .string "in"
def ParseM.«prj» : ParseM Unit := .string "prj"
def ParseM.«inj» : ParseM Unit := .string "inj"
def ParseM.«order» : ParseM Unit := .string "order"
def ParseM.«ind» : ParseM Unit := .string "ind"
def ParseM.«splitₚ» : ParseM Unit := .string "splitₚ"
def ParseM.«splitₛ» : ParseM Unit := .string "splitₛ"
def ParseM.«~» : ParseM Unit := .char '~'
def ParseM.«.» : ParseM Unit := .char '.'
def ParseM.«:» : ParseM Unit := .char ':'
def ParseM.«=» : ParseM Unit := .char '='
def ParseM.«/» : ParseM Unit := .char '/'
def ParseM.«;» : ParseM Unit := .char ';'
def ParseM.«++» : ParseM Unit := .string "++"
def ParseM.«⇒» : ParseM Unit := .string "=>" <|> .char '⇒'
def ParseM.«▹» : ParseM Unit := .string "|>" <|> .char '▹'
-- TODO: What's the best ascii version of `▿`?
def ParseM.«▿» : ParseM Unit := .char 'v' <|> .char '▿'
def ParseM.«∀» : ParseM Unit := .string "forall" <|> .char '∀'
def ParseM.«⊙» : ParseM Unit := .char 'o' <|> .char '⊙'
def ParseM.«⊙'» : ParseM Unit := .«⊙» *> .char '\''
def ParseM.«λ» : ParseM Unit := .char '\\' <|> .char 'λ'
def ParseM.«≲» : ParseM Unit := .string "~<" <|> .char '≲'
def ParseM.«→» : ParseM Unit := .string "->" <|> .char '→'
def ParseM.«⌊» : ParseM Unit := .string "[_" <|> .char '⌊'
def ParseM.«⌋» : ParseM Unit := .string "_]" <|> .char '⌋'
def ParseM.«⟨» : ParseM Unit := .char '<' <|> .char '⟨'
def ParseM.«⟩» : ParseM Unit := .char '>' <|> .char '⟩'
def ParseM.«[» : ParseM Unit := .char '['
def ParseM.«]» : ParseM Unit := .char ']'
def ParseM.«{» : ParseM Unit := .char '{'
def ParseM.«}» : ParseM Unit := .char '}'

partial def kind : ParseM Kind := Parser.withErrorMessage "expected kind" do
  let κ ←
    (char '*' <|> char '⋆') *> pure Kind.star
    <|> char 'L' *> pure Kind.label
    <|> char 'U' *> pure Kind.comm
    <|> char 'R' **> Kind.row <$> kind
    <|> ParseM.paren kind
  return match ← Parser.option? <|
    ws *> (ParseM.string "|->" <|> ParseM.char '↦') **> kind
  with
  | .some κ' => .arr κ κ'
  | .none => κ

def label : ParseM Label := Parser.withErrorMessage "expected label" do
  -- TODO: return idenifier for this label
  return (← labelString).hash.toNat
  where labelString : ParseM String := do
    let start ← alpha
    let rest ← Parser.takeMany (alphanum <|> char '_')
    let s : String := ⟨start :: rest.toList⟩
    return s

def typeClass : ParseM TypeClass := Parser.withErrorMessage "expected type class" do
  -- TODO: return identifier for this typeclass
  return (← typeClassString).hash.toNat
  where typeClassString : ParseM String := do
    let start ← alpha
    let rest ← Parser.takeMany (alphanum <|> char '_')
    let s : String := ⟨start :: rest.toList⟩
    return s

def typevar : ParseM TypeVar := Parser.withErrorMessage "expected type variable" do
  -- TODO: return identifier for this free? variable
  return .free (← typevarString).hash.toNat
  where typevarString : ParseM String := do
    let start ← alpha
    let rest ← Parser.takeMany (alphanum <|> char '_')
    let s : String := ⟨start :: rest.toList⟩
    return s

def comm : ParseM Commutativity := Parser.withErrorMessage "expected commutativity" do
  char 'C' *> pure .comm
  <|> char 'N' *> pure .non

def prodOrSum : ParseM ProdOrSum := Parser.withErrorMessage "expected prod or sum" do
  ParseM.char 'Π' *> pure .prod
  <|> ParseM.char 'Σ' *> pure .sum

mutual
partial def typelambda : ParseM TypeLambda := Parser.withErrorMessage "expected type lambda" do
    TypeLambda.mk <$> (ParseM.«λ» **> typevar **> kind) <**> monotype

partial def monotype : ParseM Monotype := Parser.withErrorMessage "expected monotype" do
  let τ : Monotype ←
    .paren monotype
    <|> .var <$> typevar
    <|> .label <$> label
    <|> .floor <$> (.«⌊» **> monotype <** .«⌋»)
    <|> .comm <$> comm
    <|> .row
      <$> (.«⟨» **> (.sepBy (.mk <$> monotype <**> (.«▹» **> monotype)) (.string ",")))
      <**> ((Parser.option? <| .«:» **> kind) <** .«⟩»)
    <|> .prodOrSum
      <$> prodOrSum
      <**> (.paren monotype)
      <**> monotype
    <|> .lift <$> (.«Lift» **> typelambda) <**> monotype
    <|> .typeClass <$> typeClass <**> monotype
    <|> .all <$> (.«All» **> typelambda) <**> monotype
    <|> .ind <$> (.«Ind» **> monotype)
    <|> .split 
      <$> (.«Split» **> typelambda)
      <**> monotype
      <**> (.«⊙'» **> monotype)
      <**> (.«~» **> monotype)

  let tail : ParseM Monotype := 
    .app τ <$> (ws *> monotype)
    <|> .arr τ <$> (ws *> .«→» **> monotype)
    <|> .contain τ
      <$> (ws *> .«≲» **> .paren monotype) 
      <**> monotype
    <|> .concat τ
      <$> (ws *> .«⊙» **> .paren monotype)
      <**> monotype
      <**> (.«~» **> monotype)

  Parser.optionD tail τ
end

partial def qualifiedType : ParseM QualifiedType := Parser.withErrorMessage "expected qualified type" do
  QualifiedType.qual <$> monotype <**> (ParseM.«⇒» **> qualifiedType)
  <|> QualifiedType.mono <$> monotype

partial def typescheme : ParseM TypeScheme := Parser.withErrorMessage  "expected type scheme" do
  TypeScheme.qual <$> qualifiedType
  <|> TypeScheme.quant <$> (ParseM.«∀» **> typevar **> ParseM.«:» **> kind) <**> (ParseM.«.» **> typescheme)

def termvar : ParseM TermVar := Parser.withErrorMessage "expected term variable" do
  -- TODO: return identifier for this free? variable
  return .free (← termvarString).hash.toNat
  where termvarString : ParseM String := do
    let start ← alpha
    let rest ← Parser.takeMany (alphanum <|> char '_')
    let s : String := ⟨start :: rest.toList⟩
    return s

def member : ParseM Member := Parser.withErrorMessage "expected member" do
  -- TODO: return identifier for this member
  return (← memberString).hash.toNat
  where memberString : ParseM String := do
    let start ← alpha
    let rest ← Parser.takeMany (alphanum <|> char '_')
    let s : String := ⟨start :: rest.toList⟩
    return s

partial def term : ParseM Term := Parser.withErrorMessage "expected term" do
  let M : Term ←
    .paren term
    <|> .var <$> termvar
    <|> .member <$> member
    <|> .lam <$> (.«λ» **> termvar **> .«.» **> term)
    <|> .let <$> (.«let» **> termvar **> .«:» **> typescheme) <**> (.«=» **> term) <**> (.«in» **> term)
    <|> .label <$> label
    <|> .prod <$> (ParseM.«{» **> (.sepBy (Prod.mk <$> term <**> (ParseM.«▹» **> term)) (.string ",")) <** ParseM.«}»)
    <|> .sum <$> (.«[» **> term) <**> (.«▹» **> term <** .«]»)
    <|> .prj <$> (.«prj» **> term)
    <|> .inj <$> (.«inj» **> term)
    <|> .order <$> (.«order» **> monotype) <**> term
    <|> .ind <$> (.«ind» **> typelambda) <**> monotype <**> (.«;» **> term) <**> (.«;» **> term)
    <|> .splitₚ <$> (.«splitₚ» **> typelambda) <**> term
    <|> .splitₛ <$> (.«splitₛ» **> typelambda) <**> term <**> (.«;» **> term)

  let tail : ParseM Term := 
    .app M <$> (ws *> term)
    <|> .annot M <$> (ws *> .«:» **> typescheme)
    <|> .unlabel M <$> (ws *> .«/» **> term)
    <|> .concat M <$> (ws *> .«++» **> term)
    <|> .elim M <$> (ws *> .«▿» **> term)

  Parser.optionD tail M
