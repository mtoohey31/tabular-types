namespace Std.Range

def get!InverseOn (p p' : List Nat) (n : Nat) :=
  (∀ i ∈ [:n], p'.get! (p.get! i) = i) ∧ ∀ i ∈ [:n], p.get! (p'.get! i) = i

end Std.Range
