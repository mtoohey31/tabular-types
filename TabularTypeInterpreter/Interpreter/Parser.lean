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
instance : Inhabited Monotype := ⟨.comm default⟩
instance : Inhabited TypeLambda := ⟨TypeLambda.mk default default⟩

structure S where
  next : Nat
deriving Inhabited

abbrev ParseM := SimpleParserT Substring Char (StateM S)
-- helpers
def ws : ParseM Unit := Parser.dropMany <|
  Parser.tokenFilter [' ', '\n', '\r', '\t'].contains
def ParseM.paren (p : ParseM α) : ParseM α :=
  char '(' *> ws *> p <* ws <* char ')'
def ParseM.string (s : String) : ParseM Unit := Parser.Char.string s *> pure ()
def ParseM.char (c : Char) : ParseM Unit := Parser.Char.char c *> pure ()

-- terminals
def ParseM.«Ind» : ParseM Unit := .string "Ind"
def ParseM.«Lift» : ParseM Unit := .string "Lift"
def ParseM.«All» : ParseM Unit := .string "All"
def ParseM.«Split» : ParseM Unit := .string "Split"
def ParseM.«~» : ParseM Unit := .char '~'
def ParseM.«⊙» : ParseM Unit := .char 'o' <|> .char '⊙'
def ParseM.«⊙'» : ParseM Unit := .«⊙» *> .char '\''
def ParseM.«λ» : ParseM Unit := .char '\\' <|> .char 'λ'
def ParseM.«≲» : ParseM Unit := .string "~<" <|> .char '≲'
def ParseM.«→» : ParseM Unit := .string "->" <|> .char '→'
def ParseM.«⌊» : ParseM Unit := .string "[_" <|> .char '⌊'
def ParseM.«⌋» : ParseM Unit := .string "_]" <|> .char '⌋'

partial def kind : ParseM Kind := Parser.withErrorMessage "expected kind" do
  let κ ←
    (char '*' <|> char '⋆') *> pure Kind.star
    <|> char 'L' *> pure Kind.label
    <|> char 'U' *> pure Kind.comm
    <|> char 'R' *> ws *> Kind.row <$> kind
    <|> ParseM.paren kind
  return match ← Parser.option? <|
    ws *> (ParseM.string "|->" <|> ParseM.char '↦') *> ws *> kind
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
  -- TODO: return identifier for this label
  return (← typeClassString).hash.toNat
  where typeClassString : ParseM String := do
    let start ← alpha
    let rest ← Parser.takeMany (alphanum <|> char '_')
    let s : String := ⟨start :: rest.toList⟩
    return s

def typevar : ParseM TypeVar := Parser.withErrorMessage "expected variable" do
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

def prodOrSum : ParseM ProdOrSum := (.char 'Π' *> pure .prod) <|> (.char 'Σ' *> pure .sum)

partial def monotype : ParseM Monotype := Parser.withErrorMessage "expected monotype" do
  -- TODO: row
  let τ : Monotype ←
    .paren monotype
    <|> .var <$> typevar
    <|> .label <$> label
    <|> .floor <$> (.«⌊» *> ws *> monotype <* ws <* .«⌋»)
    <|> .comm <$> comm
    <|> .prodOrSum
      <$> (ws *> prodOrSum)
      <*> (ws *> .paren monotype)
      <*> (ws *> monotype)
    <|> .lift <$> (.«Lift» *> ws *> typelambda) <*> (ws *> monotype)
    <|> .typeClass <$> typeClass <*> (ws *> monotype)
    <|> .all <$> (.«All» *> ws *> typelambda) <*> (ws *> monotype)
    <|> .ind <$> (.«Ind» *> ws *> monotype)
    <|> .split 
      <$> (.«Split» *> ws *> typelambda)
      <*> (ws *> monotype)
      <*> (ws *> .«⊙'» *> ws *> monotype)
      <*> (ws *> .«~» *> ws *> monotype)

  let tail : ParseM Monotype := 
    .app τ <$> (ws *> monotype)
    <|> .arr τ <$> (ws *> .«→» *> ws *> monotype)
    <|> .contain τ
      <$> (ws *> .«≲» *> ws *> .paren monotype) 
      <*> (ws *> monotype)
    <|> .concat τ
      <$> (ws *> .«⊙» *> ws *> .paren monotype)
      <*> (ws *> monotype)
      <*> (ws *> .«~» *> ws *> monotype)

  Parser.optionD tail τ

  where typelambda : ParseM TypeLambda := do
    -- NOTE: is this not supposed to take the typevar as argument?
    TypeLambda.mk <$> (.«λ» *> ws *> typevar *> ws *> kind) <*> (ws *> monotype)

