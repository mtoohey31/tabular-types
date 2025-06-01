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
structure TypeContext extends ProgramContext where
  -- The names of identifiers declared in enclosing type binders (either lambdas or foralls).
  typeVars : List String
deriving Inhabited

private
structure UVarState where
  nextFresh : Nat := 0
deriving Inhabited

private
structure TypeInTermState extends UVarState where
  -- A map from type var name to the id of the uvar which will represent it within the generalizing
  -- scope.
  varuvars : HashMap String Nat := .empty
deriving Inhabited

private
abbrev TypeM := SimpleParserT Substring Char (StateT TypeInTermState (ReaderM TypeContext))

private
def TypeM.pushVar (id : String) : TypeM α → TypeM α :=
  fun x s s' r => x s s' { r with typeVars := id :: r.typeVars }

private
def TypeM.pushVars (ids : List String) : TypeM α → TypeM α :=
  fun x s s' r => x s s' { r with typeVars := ids ++ r.typeVars }

private
instance : MonadLiftT CoreM TypeM where
  monadLift p s s' _ := (p s, s')

private
def rawId : CoreM String := (⟨· :: ·.toList ++ ·.toList⟩) <$>
  (alpha <|> char '_') <*> takeMany (alphanum <|> char '_') <*> takeMany (char '\'')

private
def programReserved := ["def", "type", "class", "instance"]

private
def typeReserved := programReserved ++
  ["where", "C", "N", "P", "S", "Lift", "All", "Ind", "Split", "List", "Nat", "String", "o"]

private
def unreservedTypeId : TypeM String := do
  let id ← rawId
  if typeReserved.contains id then
    throwUnexpectedWithMessage none s!"use of reserved identifier '{id}'"

  return id

private
def freshUVar : TypeM (Monotype true) := do
  let { nextFresh, .. } ← getModify fun ctx => { ctx with nextFresh := ctx.nextFresh + 1 }
  return .uvar nextFresh

private
def typeId (inTerm : Bool) : TypeM (Monotype inTerm) := do
  let id ← unreservedTypeId

  let { typeVars, typeAliases, classToMember, .. } ← read
  if let some idx := typeVars.idxOf? id then
    return .var idx

  if h : inTerm && id == "_" then
    return ← by
      simp at h
      rw [h.left]
      exact freshUVar

  if classToMember.contains id then
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
        varuvars := varuvars.insert id nextFresh : TypeInTermState
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
      let idsκs ← (char '\\' <|> char 'λ') **> sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> char ':' **> kind) <** char '.' <*~
      let τ ← TypeM.pushVars (idsκs.flatMap Prod.fst).toList.reverse go
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

private
def «⇒» : CoreM String := string "=>" <|> string "⇒"

open QualifiedType in
private partial
def qualifiedType (inTerm : Bool) : TypeM (QualifiedType inTerm) :=
  withErrorMessage "expected qualified type" do
  let τ ← monotype inTerm
  optionD (qual τ <$> (~*> liftM «⇒» **> qualifiedType inTerm)) τ

open TypeScheme in
private partial
def typeScheme (inTerm : Bool) : TypeM (TypeScheme inTerm) :=
  withErrorMessage "expected type scheme" <| (do
      let idsκs ← (string "forall" <|> string "∀") **> sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> char ':' **> liftM kind) <** char '.' <*~
      let σ ← TypeM.pushVars (idsκs.flatMap Prod.fst).toList.reverse <| typeScheme inTerm
      return idsκs.foldr (fun (ids, κ) σ' => ids.foldr (fun _ σ'' => quant κ σ'') σ') σ)
      <|> qual <$> qualifiedType inTerm

local
macro "#parse_type " input:str " to " expected:term : command =>
  `(#eval assertResultEq (α := TypeScheme true)
      (open TypeScheme in open QualifiedType in open Monotype in $expected)
      <| (typeScheme true <* endOfInput) $input { } {
          typeAliases := { "Option", "Bool" }
          classToMember := { ("Eq", "eq"), ("LE", "le") }
          typeVars := ["a", "b", "c"]
        } |>.fst)

#parse_type "b" to var (uvars := true) 1
#parse_type "q" to varuvar 0
#parse_type "_ _" to uvar 0 |>.app <| uvar 1
#parse_type "a b c" to app (uvars := true) (app (var 0) (var 1)) (var 2)
#parse_type "λ a : *. a" to lam (uvars := true) .star (var 0)
#parse_type "\\d : R *. a d" to lam (uvars := true) (.row .star) <| app (var 1) (var 0)
#parse_type "λ a b : *, c d : C. a d" to lam (uvars := true) .star <| lam .star <| lam .constr <|
  lam .constr <| app (var 3) (var 0)
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
#parse_type "a b d ~<(C) c d" to contain (uvars := true) (app (app (var 0) (var 1)) (varuvar 0))
  (Monotype.comm .comm) (app (var 2) (varuvar 0))
#parse_type "a ⊙(N) b ~ c ⇒ a" to qual (uvars := true)
  (concat (var 0) (Monotype.comm .non) (var 1) (var 2)) (mono (var 0))
#parse_type "a o(C) b ~ c => a" to qual (uvars := true)
  (concat (var 0) (Monotype.comm .comm) (var 1) (var 2)) (mono (var 0))
#parse_type "Eq" to tc (uvars := true) "Eq"
#parse_type "LE" to tc (uvars := true) "LE"
#parse_type "Split a b c -> List a" to split (uvars := true) |>.app (var 0) |>.app (var 1)
  |>.app (var 2) |>.arr (list.app <| var 0)
#parse_type "Nat → String" to Monotype.nat (uvars := true) |>.arr str
#parse_type "∀ a : *. a" to quant (uvars := true) .star <| qual <| mono <| var 0
#parse_type "forall d : R *. a d" to quant (uvars := true) (.row .star) <| qual <| mono <|
  app (var 1) (var 0)
#parse_type "∀ a b : *, c d : C. a d" to quant (uvars := true) .star <| quant .star <|
  quant .constr <| quant .constr <| qual <| mono <| app (var 3) (var 0)
#parse_type "Bool" to «alias» (uvars := true) "Bool"
#parse_type "Option" to «alias» (uvars := true) "Option"

private
structure TermContext extends ProgramContext where
  -- The names of identifiers declared in enclosing term binders (either lambdas or lets).
  termVars : List String
deriving Inhabited

private
abbrev TermM := SimpleParserT Substring Char (StateT TypeInTermState (ReaderM TermContext))

namespace TermM

private
def pushVar (id : String) : TermM α → TermM α :=
  fun x s s' r => x s s' { r with termVars := id :: r.termVars }

private
def pushVars (ids : List String) : TermM α → TermM α :=
  fun x s s' r => x s s' { r with termVars := ids ++ r.termVars }

private
def newGenScope : TermM α → TermM α :=
  fun x s s' r =>
    let (res, { nextFresh, .. }) := x s { s' with varuvars := .empty } r
    (res, { s' with nextFresh })

end TermM

private
instance : MonadLiftT TypeM TermM where
  monadLift p s s' r := p s s' { r with typeVars := [] }

private
instance : MonadLiftT CoreM TermM where
  monadLift x := liftM <| liftM (n := TypeM) x

private
def termReserved := programReserved ++ ["let", "in", "prj", "inj", "ind", "splitp", "splits"]

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
  if let some idx := termVars.idxOf? id then
    return .var idx

  if classToMember.values.contains id then
    return .member id

  if defs.contains id then
    return .def id

  throwUnexpectedWithMessage none "undeclared term var"

private
def op : TermM «λπι».Op := withErrorMessage "expected binary operator" <|
  char '+' *> pure .add
    <|> char '-' *> pure .sub
    <|> char '*' *> pure .mul
    <|> char '/' *> pure .div

open Term in
private partial
def term (greedy unlabel := true) : TermM (Term true) := withErrorMessage "expected term" do
  let M ← termId
    <|> (do
      let idsτ?s ← (char '\\' <|> char 'λ') **> sepBy (~*> char ',' <*~)
        (Prod.mk <$> sepBy ws unreservedTypeId <**> option? (char ':' **> monotype true))
        <** char '.' <*~
      let M ← TermM.pushVars (idsτ?s.flatMap Prod.fst).toList.reverse term
      idsτ?s.foldrM (init := M) fun (ids, τ?) M' =>
        ids.foldrM (init := M') fun _ M'' =>
          if let some τ := τ? then
            return annot (lam M'') <| Monotype.arr τ <| ← freshUVar
          else
            return lam M'')
    <|> (do
      let id ← string "let" **> unreservedTermId <*~
      let σ? ← option? (char ':' **> typeScheme <*~)
      if let some σ := σ? then
        let M ← char '=' **> TermM.newGenScope term <*~
        let N ← string "in" **> TermM.pushVar id term
        return .let σ M N
      else
        let M ← char '=' **> term <*~
        let N ← string "in" **> TermM.pushVar id term
        return .let none M N)
    <|> (label ∘ String.mk ∘ Array.toList ∘ Prod.fst) <$>
      (char '\'' *> takeUntil (char '\'') anyToken)
    <|> (prod ∘ .ofList ∘ Array.toList) <$> (char '{' **>
      sepBy (~*> char ',' <*~) (Prod.mk <$> term <**> liftM «▹» **> term) <** char '}')
    <|> sum <$> (char '[' **> term) <**> liftM «▹» **> term <** char ']'
    <|> prj <$> (string "prj" **> term false)
    <|> inj <$> (string "inj" **> term false)
    <|> ind <$> (string "ind" **> monotype false) <**> monotype false
      <**> TermM.newGenScope (term false) <**> term false
    <|> splitₚ <$> ((string "splitp" <|> string "splitₚ") **> monotype false) <**> term false
    <|> splitₛ <$> ((string "splits" <|> string "splitₛ") **> monotype false)
      <**> term false <**> term false
    <|> (str ∘ String.mk ∘ Array.toList ∘ Prod.fst) <$>
      (char '"' *> takeUntil (char '"') anyToken)
    <|> Term.nat <$> (String.toNat! ∘ String.mk ∘ Array.toList) <$> takeMany1 numeric
    <|> string "nil" *> pure nil
    <|> string "fold" *> pure fold
    <|> string "range" *> pure range
    <|> paren term

  if !unlabel then
    return M

  let M' ← Array.foldl Term.unlabel M <$> takeMany (~*> char '/' **> term false false)

  if !greedy then
    return M'

  let M'' ← Array.foldl app M' <$> takeMany (~*> term false)

  let tail := annot M'' <$> (~*> char ':' **> typeScheme)
    <|> concat M'' <$> (~*> string "++" **> term)
    <|> elim M'' <$> (~*> (string "\\/" <|> string "▿") **> term)
    <|> cons M'' <$> (~*> string "::" **> term)
    <|> (.op · M'' ·) <$> (~*> op) <**> term

  optionD tail M''
where
  typeScheme : TermM (TypeScheme true) := Parser.typeScheme true
  monotype (greedy := true) : TermM (Monotype true) := Parser.monotype true greedy

local
macro "#parse_term " input:str " to " expected:term : command =>
  `(#eval assertResultEq (α := Term true) (open Term in $expected) <|
      (term <* endOfInput) $input { } {
          defs := { "map", "true" }
          classToMember := { ("Eq", "eq"), ("LE", "le") }
          termVars := ["a", "b", "c"]
        } |>.fst)

#parse_term "b" to var 1
#parse_term "le" to member "le"
#parse_term "\\a : Nat. a" to annot (lam <| var 0) (Monotype.arr (uvars := true) .nat (.uvar 0))
#parse_term "λ l acc. acc/l" to lam <| lam <| unlabel (var 0) (var 1)
-- TODO: Test generalizing scope handling here.
#parse_term "let xs : List Nat = nil in xs xs" to «let» (Monotype.app (uvars := true) .list .nat)
  nil <| app (var 0) (var 0)
#parse_term "let xs = nil in xs xs" to «let» none nil <| app (var 0) (var 0)
#parse_term "''" to label ""
#parse_term "'asdf'" to label "asdf"
#parse_term "{}" to prod .nil
#parse_term "{'foo' ▹ 0, a |> \"hi\"}" to prod <| .cons (label "foo") (nat 0) <|
  .cons (var 0) (str "hi") .nil
#parse_term "[c ▹ 5]" to sum (var 2) (nat 5)
#parse_term "['baz' |> 0153]" to sum (label "baz") (nat 153)
#parse_term "prj a/b c" to app (prj (unlabel (var 0) (var 1))) (var 2)
#parse_term "inj c/'hi'" to inj <| unlabel (var 2) (label "hi")
-- q inside the lam is distinct from the one outside since type vars can be shadowed at
-- generalization points, which the first term argument to ind qualifies as.
#parse_term "ind (λ d : R *. P(N) (Lift q d)) r (λ l acc. acc ++ {l : ⌊q⌋ ▹ 0}) {}" to ind
  (.lam (.row .star)
    (.app (.prodOrSum .prod (.comm .non)) (.app (.app .lift (.varuvar 0)) (.var 0))))
  (.varuvar 1)
  (lam (lam (concat (var 0)
    (prod (.cons (Term.annot (var 1) (Monotype.floor (.varuvar 2))) (nat 0) .nil))))) (prod .nil)
#parse_term "splitₚ List nil" to splitₚ .list nil
#parse_term "splitp List (fold)" to splitₚ .list fold
#parse_term "splitₛ List range b" to splitₛ .list range (var 1)
#parse_term "splits List a b" to splitₛ .list (var 0) (var 1)
#parse_term "\"\"" to str ""
#parse_term "map" to «def» "map"
#parse_term "true" to «def» "true"

private
abbrev ProgramM := SimpleParserT Substring Char (StateM ProgramContext)

instance : MonadLift TypeM ProgramM where
  monadLift p s s' := (p s { } { s' with typeVars := [] } |>.fst, s')

instance : MonadLift TermM ProgramM where
  monadLift p s s' := (p s { } { s' with termVars := [] } |>.fst, s')

private partial
def programEntry : ProgramM ProgramEntry := withErrorMessage "expected program entry" <|
  «def» <|> typeAlias <|> «class» <|> «instance»
where
  «def» : ProgramM ProgramEntry := do
    let x ← string "def" **> unreservedTermId
    let ctx ← liftM <| getModify (m := StateM ProgramContext) fun ctx =>
      { ctx with defs := ctx.defs.insert x }
    if ctx.boundTerm.contains x then
      throwUnexpectedWithMessage none s!"redeclaration of '{x}'"
    let σ? ← option? (~*> char ':' **> typeScheme false)
    let M ← ~*> char '=' **> term
    return .def x σ? M
  typeAlias : ProgramM ProgramEntry := do
    let a ← string "type" **> unreservedTypeId
    let ctx ← liftM <| getModify (m := StateM ProgramContext) fun ctx =>
      { ctx with typeAliases := ctx.typeAliases.insert a }
    if ctx.boundType.contains a then
      throwUnexpectedWithMessage none s!"redeclaration of '{a}'"
    let σ ← ~*> char '=' **> typeScheme false
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

    let ctx@{ classToMember, .. } ← liftM <| getModify (m := StateM ProgramContext) fun ctx =>
      { ctx with classToMember := ctx.classToMember.insert TC m }
    if let some undeclared := TCₛs.find? (!classToMember.contains ·) then
      throwUnexpectedWithMessage none s!"superclass '{undeclared}' is undeclared"
    if ctx.boundType.contains TC then
      throwUnexpectedWithMessage none s!"redeclaration of '{TC}'"

    let σ ← ~*> char ':' **> TypeM.pushVars [a] (typeScheme false)
    return .class TCₛs.toList TC κ m σ
  «instance» : ProgramM ProgramEntry := do
    let _ ← string "instance" <*~
    let ψs ← optionD (sepBy (~*> char ',' <*~) (monotype true) <** «⇒») #[]

    let { classToMember, .. } ← read
    let TC ← ~*> unreservedTypeId
    let some expectedM := classToMember[TC]?
      | throwUnexpectedWithMessage none s!"class '{TC}' is undeclared"

    let τ ← ~*> monotype true
    let m ← ~*> string "where" **> unreservedTermId
    if m != expectedM then
      throwUnexpectedWithMessage none s!"incorrect member name '{m}', expected '{expectedM}'"
    let M ← ~*> char '=' **> term
    return .instance ψs.toList TC τ M

private
def program : ProgramM Program := ~*> Array.toList <$> sepBy ws programEntry <** endOfInput

def parse (s : String) := term.run s default default |>.fst
