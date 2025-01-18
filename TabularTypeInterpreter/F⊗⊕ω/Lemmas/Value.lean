import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term

namespace TabularTypeInterpreter.«F⊗⊕ω».Value

theorem eq_lam_of_ty_arr (VtyAarrB : [[ε ⊢ V : A → B]])
  : ∃ A' E, V.1 = [[λ x : A'. E]] := sorry

theorem eq_typeApp_of_ty_forall (Vty : [[ε ⊢ V : ∀ a : K. A]])
  : ∃ K E, V.1 = [[Λ a : K. E]] := sorry

theorem eq_prodIntro_of_ty_prod (Vty : [[ε ⊢ V : ⊗ {</ A@i // i in [:n] />}]])
  : ∃ V' : Nat → Value, V.1 = [[(</ V'@i // i in [:n] />)]] := sorry

theorem eq_sumIntro_of_ty_sum (Vty : [[ε ⊢ V : ⊕ {</ A@i // i in [:n'] />}]])
  : ∃ n ∈ [0:n'], ∃ V', V.1 = [[ι n V']] := sorry

end TabularTypeInterpreter.«F⊗⊕ω».Value
