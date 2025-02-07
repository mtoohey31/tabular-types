import Mathlib.Data.List.Basic
import TabularTypeInterpreter.Range

namespace List

def combinations {α : Type} (l : List α) :  List (List α)  :=
  l.foldl (fun acc a => acc ++ acc.map (fun l => a :: l)) [nil]

-- (╯︵╰,) those functions can be replaced by matthew's approach, where he uses `get!` and friends.

def toFn {α: Type} (l: List α) (default: α) (n: Nat): α :=
  if h: n < l.length then
    l.get (.mk n h)
  else
    default -- it doesn't really matter what we return here

def toFn_spec {d: α} {l: List α} i (le: i < l.length): l.toFn d i = l[i] := by simp_all [toFn]

theorem toFn_spec' {d: α} {l: List α}: [0:l.length].map (l.toFn d) = l := by
  induction l using List.reverseRecOn
  . case nil => simp_all [Std.Range.toList]
  . case append_singleton xs x ih =>
    simp_all [Std.Range.map]
    rw [<- Std.Range.toList_append (m := xs.length)] <;> simp_all
    have aux : ∀α (a b c d: List α), a = b → c = d → a ++ c = b ++ d := by simp
    apply aux
    . rw (occs := .pos [3]) [<- ih]
      apply List.map_congr_left
      intro a In
      apply Std.Range.mem_toList_le at In
      have In' : a < xs.length + 1 := by simp_all [Nat.lt_add_right]
      simp_all [toFn]
      simp_all [List.getElem_append]
      simp
    . simp [Std.Range.toList, toFn]

end List
