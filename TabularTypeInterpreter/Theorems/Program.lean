import TabularTypeInterpreter.Lemmas.InstanceEnvironment
import TabularTypeInterpreter.Semantics.Program
import TabularTypeInterpreter.Theorems.Term

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

instance : Inhabited TypeClass where
  default := .zero
in
instance : Inhabited Method where
  default := .zero
in
instance : Inhabited TypeScheme where
  default := .qual (.mono (.row [] none))
in
instance : Inhabited «F⊗⊕ω».Kind where
  default := .star
in
theorem Program.TypingAndElaboration.soundness (pte : [[Γᵢ; Γc ⊢ pgm : σ ⇝ E]])
  (Γᵢw : [[Γc ⊢ Γᵢ]] := by exact .empty) (Γcw : [[⊢c Γc]] := by exact .empty)
  (σke : [[Γc; ε ⊢ σ : * ⇝ A]]) : [[ε ⊢ E : A]] := match pte with
  | .cls TC'in TCnin mnin σ₀ke p'te (κ := κ) (A' := A') =>
    let ⟨_, κe⟩ := κ.Elaboration_total
    let Aki := (σ₀ke · |>.soundness Γcw (.typeExt .empty nofun κe) .star)
    let ⟨_, TC'in'⟩ := Range.skolem TC'in
    let ⟨A'', TC'in''⟩ := Range.skolem TC'in'
    let ⟨nₛ, TC'in'''⟩ := Range.skolem TC'in''
    let ⟨_, TC'in''''⟩ := Range.skolem TC'in'''
    let ⟨_, TC'in'''''⟩ := Range.skolem TC'in''''
    let ⟨_, TC'in''''''⟩ := Range.skolem TC'in'''''
    let TCake i mem a : TypeScheme.KindingAndElaboration _ _ _ _
      ((A' i).TypeVar_open a) := by
      let ⟨Aeq, TC'in'''''''⟩ := TC'in'''''' i mem
      rw [Aeq, Type.TypeVar_open, Type.TypeVar_open, List.mapMem_eq_map, List.map_cons,
          List.map_map, ← Range.map, Type.TypeVar_open_eq_Type_open_var,
          Range.map_eq_of_eq_of_mem'' (by
            intro j mem'
            rw [Function.comp, Type.TypeVar_open_eq_Type_open_var]
      )]
      exact .tc TC'in''''''' (.var .head (Γ := .typeExt .empty a κ))
    let Γc'w := Γcw.ext TCnin mnin κe σ₀ke Aki TCake
      (TCake · · · |>.soundness Γcw (.typeExt .empty nofun κe) .constr)
    p'te.soundness (Γᵢw.weakening Γc'w (Γc' := .ext .empty ..)) Γc'w <|
      σke.class_weakening Γc'w (Γc' := .ext .empty ..)
  | .inst γcin ψke TC'τce τke Mte p'te (TC' := TC') (A' := A') (σ₀ := σ₀) (A := A) (κ' := κ')
      (l := l) (o := o) => by
    apply p'te.soundness _ Γcw σke
    let ⟨K₁, κ'e⟩ := Classical.skolem.mp (κ' · |>.Elaboration_total)
    let ⟨_, κ₀e, σke, _, TC'ke, _⟩ := Γcw.In_inversion γcin
    apply Γᵢw.ext γcin ψke τke fun i _ => κ'e i
    · intro a x
      let aκ'we := TypeEnvironment.WellFormednessAndElaboration.empty.multiTypeExt (fun _ => nofun)
        a.property (fun i _ => κ'e i) (n := o) (Γc := Γc)
      let aκ'ψ'xwe := aκ'we.multiConstrExt (by
        intro _
        rw [TypeEnvironment.TermVarNotInDom, TypeEnvironment.termVarDom_multiTypeExt,
            TypeEnvironment.termVarDom]
        nofun
      ) x.property (ψke · · a) (n := l)
      apply Mte a x |>.soundness _ Γᵢw Γcw aκ'ψ'xwe
      let ⟨a', a'nin⟩ := σ₀.freeTypeVars ++ ↑A.freeTypeVars ++
        [[(ε,, </ a@k : κ'@k // k in [:o] />)]].typeVarDom |>.exists_fresh
      let ⟨a'ninσ₀A, a'ninaκ'⟩ := List.not_mem_append'.mp a'nin
      let ⟨a'ninσ₀, a'ninA⟩ := List.not_mem_append'.mp a'ninσ₀A
      let aκ'a'we := aκ'we.typeExt a'ninaκ' κ₀e
      let σke' := σke a'
      rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at aκ'a'we
      rw [← TypeEnvironment.empty_append (.typeExt ..)] at σke'
      let σke'' := σke'.weakening aκ'a'we (Γ := .empty) (Γ'' := .typeExt .empty ..)
      rw [TypeEnvironment.empty_append] at σke'' aκ'a'we
      rw [TypeEnvironment.append, TypeEnvironment.append] at σke''
      rw [← TypeEnvironment.append_empty (.multiConstrExt ..),
          TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty)] at aκ'ψ'xwe
      have := σke''.Monotype_open_preservation Γcw aκ'a'we nofun a'ninσ₀ a'ninA (τke a) (Γ' := .empty)
        |>.weakening aκ'ψ'xwe (Γ := .multiTypeExt .empty ..) (Γ' := .multiConstrExt .empty ..)
          (Γ'' := .empty)
      rw [← TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty),
          TypeEnvironment.append_empty] at this
      exact this
    · intro i mem a x
      let aκ'we := TypeEnvironment.WellFormednessAndElaboration.empty.multiTypeExt (fun _ => nofun)
        a.property (fun i _ => κ'e i) (n := o) (Γc := Γc)
      let aκ'ψ'xwe := aκ'we.multiConstrExt (by
        intro _
        rw [TypeEnvironment.TermVarNotInDom, TypeEnvironment.termVarDom_multiTypeExt,
            TypeEnvironment.termVarDom]
        nofun
      ) x.property (ψke · · a) (n := l)
      apply TC'τce i mem a x |>.soundness _ Γᵢw Γcw aκ'ψ'xwe
      let ⟨a', a'nin⟩ := ↑(A' i).freeTypeVars ++
        [[(ε,, </ a@k : κ'@k // k in [:o] />)]].typeVarDom |>.exists_fresh
      let ⟨a'ninA'ᵢ, a'ninaκ'⟩ := List.not_mem_append'.mp a'nin
      let aκ'a'we := aκ'we.typeExt a'ninaκ' κ₀e
      rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at aκ'a'we
      let TC'a'ke := TC'ke a' i mem |>.weakening aκ'a'we (Γ := .empty) (Γ'' := .typeExt .empty ..)
      rw [TypeEnvironment.empty_append] at TC'a'ke aκ'a'we
      have : Monotype.typeClass (TC' i) (.var (.free a')) =
        (.TypeVar_open (.typeClass (TC' i) (.var (.bound 0))) a') := by
        simp [Monotype.TypeVar_open]
      rw [this, ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at TC'a'ke
      rw [← TypeEnvironment.append_empty (.multiConstrExt ..),
          TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty)] at aκ'ψ'xwe
      let this := TC'a'ke.Monotype_open_preservation Γcw aκ'a'we nofun (by
        rw [TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars,
            Monotype.freeTypeVars]
        nofun
      ) a'ninA'ᵢ (τke a) (Γ' := .empty)
        |>.weakening aκ'ψ'xwe (Γ := .multiTypeExt .empty ..) (Γ' := .multiConstrExt .empty ..)
          (Γ'' := .empty)
      rw [← TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty),
          TypeEnvironment.append_empty, TypeScheme.Monotype_open, QualifiedType.Monotype_open,
          Monotype.Monotype_open, Monotype.Monotype_open, if_pos rfl] at this
      exact this

  | .term Mte => Mte.soundness σke Γᵢw Γcw .empty

end TabularTypeInterpreter
