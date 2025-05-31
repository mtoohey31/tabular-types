import TabularTypeInterpreter.Interpreter

open IO
open TabularTypeInterpreter.Interpreter Term

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

def Args.parse : List String → IO Args
  | [] => return { }
  | ["--table"] => return { table := true }
  | _ => do
    let stderr ← getStderr
    stderr.putStrLn "Usage: tti [--table]"
    Process.exit cliError

def main (args : List String) : IO UInt32 := do
  let stdin ← getStdin
  let stdout ← getStdout
  let stderr ← getStderr
  let args ← Args.parse args
  match Parser.parse (← stdin.getLine) with
  | .error _ e =>
    stderr.putStrLn (toString e)
    return internalError
  | .ok _ M =>
  let σ : TypeScheme := sorry
  let M' : Term := sorry
  let ty : Typing M' σ := sorry
  match ty.elab.eval with
  | .error e =>
    stderr.putStrLn s!"eval error: {e}\nthis means there is a bug in a prior stage"
    return internalError
  | .ok V =>
    let some N := V.delab σ |
      stderr.putStrLn "evaluation succeeded but result could not be delaborated for printing; only values which contain no lambdas can be printed"
      return ok
    stdout.putStrLn <| N.toString (table := args.table)
    return ok
