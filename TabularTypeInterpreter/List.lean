namespace List

-- TODO better get some sane names for these
theorem whateverL1 : l1.length = l2.length -> map (f ∘ Prod.fst) (zip l1 l2) = map f l1 := sorry
theorem whateverL2 : l1.length = l2.length -> map (f ∘ Prod.snd) (zip l1 l2) = map f l2 := sorry
theorem whateverflat : (map (fun x => [f x]) l).flatten = map f l := sorry

theorem zip_member : (a,b) ∈ zip l1 l2 → a ∈ l1 ∧ b ∈ l2 := by
  intro h
  induction l1 generalizing l2 <;> (try simp_all; done)
  . case cons _ _ hd1 tl1 ih1 =>
    induction l2
    . case nil => simp_all
    . case cons hd2 tl2 ih2 =>
      simp_all
      cases h
      . case inl => simp_all
      . case inr H =>
        have H' := ih1 H
        simp_all

theorem zip_member_map_same : (a,b) ∈ zip (map f l) (map g l) -> ∃ c, c ∈ l ∧ a = f c ∧ b = g c := by
  induction l
  . case nil => simp_all
  . case cons =>
    simp_all
    intro h
    cases h <;> simp_all

def combinations {α : Type} (l : List α) :  List (List α)  :=
  l.foldl (fun acc a => acc ++ acc.map (fun l => a :: l)) [nil]

end List
