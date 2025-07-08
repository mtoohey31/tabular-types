import TabularTypeInterpreter.Elab.Options
import TabularTypeInterpreter.Interpreter

open IO FS
open System
open TabularTypeInterpreter.Interpreter Inference Term

inductive Status where
  | ok
  | syntaxOrSemanticError
  | cliError
  | ioError
  | internalError

open Status

instance : Coe Status UInt8 where
  coe
    | ok => 0
    | syntaxOrSemanticError => 1
    | cliError => 2
    | ioError => 3
    | internalError => 4

instance : Coe Status UInt32 where
  coe s := (s : UInt8).toUInt32

structure Args where
  table : Bool := false
  files : List FilePath := [ ]
  term : Option String := none
  core : Bool := true

def corePath := by_elab do
  let opts ← Lean.MonadOptions.getOptions
  let some path := opts.get? tti.corePath.name | throwError "'tti.corePath' variable should be set"
  return Lean.mkStrLit path

def coreFiles : List FilePath := List.map (FilePath.join corePath) [
    "And.tt",
    "Bool.tt",
    "Const.tt",
    "Eq.tt",
    "flip.tt",
    "is.tt",
    "Unit.tt",
    "Labels.tt",
    "LabelsMatch.tt",
    "LE.tt",
    "Option.tt",
    "List.tt"
  ]

def Args.allFiles (args : Args) := (if args.core then coreFiles else []) ++ args.files

def Args.parse : List String → (optParam Args { }) → IO Args
  | [], acc => return acc
  | "--table" :: args, acc => parse args { acc with table := true }
  | "-e" :: term :: args, acc => parse args { acc with term }
  | "--nocore" :: args, acc => parse args { acc with core := false }
  | "--" :: files', acc@{ files, .. } => return { acc with files := files ++ files'.map (↑·) }
  | file :: args, acc@{ files, .. } => do
    if file.get? 0 == some '-' then
      let stderr ← getStderr
      stderr.putStrLn "Usage: tti [--table] [<file>...] [-e <term>]"
      Process.exit cliError

    parse args { acc with files := files ++ [↑file] }

set_option linter.deprecated false in
def main (args : List String) : IO UInt32 := do
  let stdin ← getStdin
  let stdout ← getStdout
  let stderr ← getStderr
  let args ← Args.parse args

  let mut st : Parser.ProgramState := { }
  let mut pgm : Program := []
  let mut defElabs := default
  for file in args.allFiles do
    let s ← readFile file
    let (pgm!, st') := Parser.program s st
    match pgm! with
    | .error _ e =>
      stderr.putStrLn s!"parse error in {file}: {e}"
      return syntaxOrSemanticError
    | .ok _ pgm' =>
      st := st'
      for e in pgm' do
        match e with
        | .def x σ? M =>
          let ⟨_, ty⟩ ← match σ? with
            | some σ =>
              match check M σ { prog := pgm } with
              | .error e _ =>
                stderr.putStrLn s!"type checking error in def {x}: {e}"
                return syntaxOrSemanticError
              | .ok res _ => pure ⟨σ, res⟩
            | none =>
              match infer M { prog := pgm } with
              | .error e _ =>
                stderr.putStrLn s!"type checking error in def {x}: {e}"
                return syntaxOrSemanticError
              | .ok res _ => pure res

          let (E, nextFresh) ← ty.elab defElabs st.term.mid.nextFresh
          defElabs := defElabs.insert x E
          st := st.updateTermNextFresh nextFresh
        | .typeAlias a σ =>
          if let .error e _ := inferKind σ { prog := pgm } then
            stderr.putStrLn s!"kind inference error in type alias {a}: {e}"
            return syntaxOrSemanticError
        | .class { TCₛs, TC, a, κ, σ, .. } =>
          for e in pgm do
            let .class { TC := TC', κ := κ', .. } := e | continue
            if TCₛs.contains TC' && κ ≠ κ' then
              stderr.putStrLn s!"superclass {TC'} of {TC} has kind {κ'} which does not match {κ}: {e}"
              return syntaxOrSemanticError

          if let .error e _ := checkKind σ .star { prog := pgm, Γ := [.typevar a κ] } then
            stderr.putStrLn s!"kind checking error in class {TC}: {e}"
            return syntaxOrSemanticError
        | .instance as ψs TC τ M =>
          for ψ in ψs do
            -- TODO: We need to figure out kinds for as somehow...
            if let .error e _ := checkKind ψ .constr { prog := pgm } then
              stderr.putStrLn s!"kind checking error in constraints of instance of {TC} for {τ}: {e}"
              return syntaxOrSemanticError

          let some { TCₛs, a, κ, σ, .. : ClassDeclaration } := List.head? <| pgm.filterMap fun
              | .class decl@{ TC := TC', .. } => .someIf decl (TC == TC')
              | _ => none
            | unreachable!

          for TCₛ in TCₛs do
            -- TODO: We need to figure out kinds for `as` somehow...
            if let .error e _ := constraint (.app (.tc TCₛ) τ) { prog := pgm, Γ := ψs.map ContextItem.constraint } then
              stderr.putStrLn s!"failed to solve superclass {TCₛ} in instance of {TC} for {τ}: {e}"
              return syntaxOrSemanticError

          -- TODO: We need to figure out kinds for `as` somehow...
          if let .error e _ := checkKind τ κ { prog := pgm } then
            stderr.putStrLn s!"kind checking error in instance of {TC} for {τ}: {e}"
            return syntaxOrSemanticError

          -- TODO: We need to figure out kinds for `as` somehow...
          if let .error e _ := check M (σ.subst τ a) { prog := pgm } then
            stderr.putStrLn s!"type checking error in instance of {TC} for {τ}: {e}"
            return syntaxOrSemanticError

        pgm := pgm ++ [e]

  let evalTerm (s : String) : IO Status := do
    match Parser.term s st with
    | .error _ e =>
      stderr.putStrLn s!"parse error in term: {e}"
      return syntaxOrSemanticError
    | .ok _ M => match infer M { prog := pgm } with
      | .error e _ =>
        stderr.putStrLn s!"inference error in term: {e}"
        return syntaxOrSemanticError
      | .ok ⟨σ, ty⟩ _ => match ty.elab defElabs st.term.mid.nextFresh |>.fst.eval with
        | .error e =>
          stderr.putStrLn s!"eval error: {e}\nthis means there is a bug in a prior stage"
          Process.exit internalError
        | .ok V =>
          let some N := V.delab σ |
            stderr.putStrLn "evaluation succeeded but result could not be delaborated for printing; only values which contain no lambdas can be printed"
            return ok
          stdout.putStrLn <| N.toString (table := args.table)
          return ok

  match args.term with
  | some s => evalTerm s
  | none =>
    repeat
      stdout.putStr "tti > "
      let s ← stdin.getLine
      if s == "" then
        stdout.putStrLn ""
        break

      let _ ← evalTerm s
    return ok
