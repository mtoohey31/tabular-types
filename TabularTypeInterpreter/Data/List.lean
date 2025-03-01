
import Mathlib.Data.List.Basic
import TabularTypeInterpreter.Data.Range

namespace List

def combinations {α : Type} (l : List α) :  List (List α)  :=
  l.foldl (fun acc a => acc ++ acc.map (fun l => a :: l)) [nil]

end List
