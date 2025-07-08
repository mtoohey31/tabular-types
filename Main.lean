import TabularTypeInterpreter.Elab.Options
import TabularTypeInterpreter.Interpreter

open IO FS
open System
open TabularTypeInterpreter.Interpreter Inference Parser Term

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
  let some (path : String) := opts.get? tti.corePath.name | throwError "'tti.corePath' variable should be set"
  return Lean.mkStrLit <| ← FilePath.toString <$> realPath path

def coreFiles : List FilePath := List.map (FilePath.join corePath) [
    "And.tt",
    "Unit.tt",
    "Bool.tt",
    "Const.tt",
    "Eq.tt",
    "flip.tt",
    "is.tt",
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

structure MainState where
  programState : ProgramState
  program : Program

abbrev MainM := StateT MainState IO

def getProgram : MainM Program := MainState.program <$> get

def pushProgram (e : ProgramEntry) : MainM Unit :=
  fun st@{ program, .. } => return ((), { st with program := program ++ [e] })

def liftInfer : InferM α → MainM (Except InferError α) := fun x st@{ programState, program, .. } =>
  match x { nextFresh := programState.term.type.uvar.nextFresh, prog := program } with
  | .ok a { nextFresh, .. } =>
    return (.ok a, { st with programState := st.programState.updateTermNextFresh nextFresh })
  | .error e { nextFresh, .. } =>
    return (.error e, { st with programState := st.programState.updateTermNextFresh nextFresh })

instance : MonadLift Parser.ParseM MainM where
  monadLift
    | x, st@{ programState, .. } => do
      let (a, programState) := x programState
      return (a, { st with programState })

instance : MonadLift ElabM MainM where
  monadLift
    | x, st@{ programState, .. } => do
      let (a, n) := x programState.term.mid.nextFresh
      return (a, { st with programState := programState.updateTermNextFresh n })

set_option linter.deprecated false in
def main' (args : Args) : MainM Status := do
  let stdin ← getStdin
  let stdout ← getStdout
  let stderr ← getStderr

  let mut defElabs := default
  for file in args.allFiles do
    let s ← readFile file
    let pgm! ← Parser.program s
    match pgm! with
    | .error _ e =>
      stderr.putStrLn s!"parse error in {file}: {e}"
      return syntaxOrSemanticError
    | .ok _ pgm' =>
      for e in pgm' do
        match e with
        | .def x σ? M =>
          let ⟨_, ty⟩ ← match σ? with
            | some σ =>
              match ← liftInfer <| check M σ with
              | .error e =>
                stderr.putStrLn s!"type checking error in def {x}: {e}"
                return syntaxOrSemanticError
              | .ok res => pure ⟨σ, res⟩
            | none =>
              match ← liftInfer <| infer M with
              | .error e =>
                stderr.putStrLn s!"type checking error in def {x}: {e}"
                return syntaxOrSemanticError
              | .ok res => pure res

          defElabs := defElabs.insert x <| ← ty.elab defElabs
        | .typeAlias a σ =>
          if let .error e ← liftInfer <| inferKind σ then
            stderr.putStrLn s!"kind inference error in type alias {a}: {e}"
            return syntaxOrSemanticError
        | .class { TCₛs, TC, a, κ, σ, .. } =>
          for e in ← getProgram do
            let .class { TC := TC', κ := κ', .. } := e | continue
            if TCₛs.contains TC' && κ ≠ κ' then
              stderr.putStrLn s!"superclass {TC'} of {TC} has kind {κ'} which does not match {κ}: {e}"
              return syntaxOrSemanticError

          if let .error e ← liftInfer <| withItem (.typevar a κ) <| checkKind σ .star then
            stderr.putStrLn s!"kind checking error in class {TC}: {e}"
            return syntaxOrSemanticError
        | .instance as ψs TC τ M =>
          for ψ in ψs do
            -- TODO: We need to figure out kinds for as somehow...
            if let .error e ← liftInfer <| checkKind ψ .constr then
              stderr.putStrLn s!"kind checking error in constraints of instance of {TC} for {τ}: {e}"
              return syntaxOrSemanticError

          let pgm ← getProgram
          let some { TCₛs, a, κ, σ, .. : ClassDeclaration } := List.head? <| pgm.filterMap fun
              | .class decl@{ TC := TC', .. } => .someIf decl (TC == TC')
              | _ => none
            | unreachable!

          for TCₛ in TCₛs do
            -- TODO: We need to figure out kinds for `as` somehow...
            let items := ψs.map ContextItem.constraint
            if let .error e ← liftInfer <| withItems items <| constraint (.app (.tc TCₛ) τ) then
              stderr.putStrLn s!"failed to solve superclass {TCₛ} in instance of {TC} for {τ}: {e}"
              return syntaxOrSemanticError

          -- TODO: We need to figure out kinds for `as` somehow...
          if let .error e ← liftInfer <| checkKind τ κ then
            stderr.putStrLn s!"kind checking error in instance of {TC} for {τ}: {e}"
            return syntaxOrSemanticError

          -- TODO: We need to figure out kinds for `as` somehow...
          if let .error e ← liftInfer <| check M (σ.subst τ a) then
            stderr.putStrLn s!"type checking error in instance of {TC} for {τ}: {e}"
            return syntaxOrSemanticError

        pushProgram e

  let evalTerm (s : String) : MainM Status := do
    match ← Parser.term s with
    | .error _ e =>
      stderr.putStrLn s!"parse error in term: {e}"
      return syntaxOrSemanticError
    | .ok _ M => match ← liftInfer <| infer M with
      | .error e =>
        stderr.putStrLn s!"inference error in term: {e}"
        return syntaxOrSemanticError
      | .ok ⟨σ, ty⟩ => match ← «λπι».Term.eval <$> ty.elab defElabs with
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

def main (args : List String) : IO UInt32 := do
  let args ← Args.parse args
  main' args |>.run' {
    programState := {
      term := {
        mid := { nextFresh := 0 },
        type := { id := { nextFresh := 0 }, uvar := { nextFresh := 0 } } }
    },
    program := []
  }
