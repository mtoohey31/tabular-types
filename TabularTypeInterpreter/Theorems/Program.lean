import TabularTypeInterpreter.Lemmas.InstanceEnvironment
import TabularTypeInterpreter.Semantics.Program
import TabularTypeInterpreter.Theorems.Term

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

instance : Inhabited TypeClass where
  default := .zero
in
instance : Inhabited Member where
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
  | .cls TCₛin TCnin mnin σ₀ke p'te (κ := κ) (Aₛ := Aₛ) =>
    let ⟨_, κe⟩ := κ.Elaboration_total
    let Aki := (σ₀ke · |>.soundness Γcw (.typeExt .empty nofun κe) .star)
    let ⟨_, TCₛin'⟩ := Range.skolem TCₛin
    let ⟨Aₛ', TCₛin''⟩ := Range.skolem TCₛin'
    let ⟨nₛ, TCₛin'''⟩ := Range.skolem TCₛin''
    let ⟨_, TCₛin''''⟩ := Range.skolem TCₛin'''
    let ⟨_, TCₛin'''''⟩ := Range.skolem TCₛin''''
    let ⟨_, TCₛin''''''⟩ := Range.skolem TCₛin'''''
    let TCake i mem a : TypeScheme.KindingAndElaboration _ _ _ _
      ((Aₛ i).TypeVar_open a) := by
      let ⟨Aeq, TCₛin'''''''⟩ := TCₛin'''''' i mem
      rw [Aeq, Type.TypeVar_open, Type.TypeVar_open, List.mapMem_eq_map, List.map_cons,
          List.map_map, ← Range.map, Type.TypeVar_open_eq_Type_open_var,
          Range.map_eq_of_eq_of_mem'' (by
            intro j mem'
            rw [Function.comp, Type.TypeVar_open_eq_Type_open_var]
      )]
      exact .tc TCₛin''''''' (.var .head (Γ := .typeExt .empty a κ))
    let Γc'w := Γcw.ext TCnin mnin κe σ₀ke Aki TCake
      (TCake · · · |>.soundness Γcw (.typeExt .empty nofun κe) .constr)
    p'te.soundness (Γᵢw.weakening Γc'w (Γc' := .ext .empty ..)) Γc'w <|
      σke.class_weakening Γc'w (Γc' := .ext .empty ..)
  | .inst γcin ψke TCₛτce τke Mte p'te (TCₛ := TCₛ) (Aₛ := Aₛ) (σ₀ := σ₀) (A := A) (κ₁ := κ₁)
      (l := l) (o := o) => by
    apply p'te.soundness _ Γcw σke
    let ⟨K₁, κ₁e⟩ := Classical.skolem.mp (κ₁ · |>.Elaboration_total)
    let ⟨_, κ₀e, σke, _, TCₛke, _⟩ := Γcw.In_inversion γcin
    apply Γᵢw.ext γcin ψke τke fun i _ => κ₁e i
    · intro a x
      let aκ₁we := TypeEnvironment.WellFormednessAndElaboration.empty.multiTypeExt (fun _ => nofun)
        a.property (fun i _ => κ₁e i) (n := o) (Γc := Γc)
      let aκ₁ψ'xwe := aκ₁we.multiConstrExt (by
        intro _
        rw [TypeEnvironment.TermVarNotInDom, TypeEnvironment.termVarDom_multiTypeExt,
            TypeEnvironment.termVarDom]
        nofun
      ) x.property (ψke · · a) (n := l)
      apply Mte a x |>.soundness _ Γᵢw Γcw aκ₁ψ'xwe
      let ⟨a', a'nin⟩ := σ₀.freeTypeVars ++ ↑A.freeTypeVars ++
        [[(ε,, </ a@k : κ₁@k // k in [:o] />)]].typeVarDom |>.exists_fresh
      let ⟨a'ninσ₀A, a'ninaκ₁⟩ := List.not_mem_append'.mp a'nin
      let ⟨a'ninσ₀, a'ninA⟩ := List.not_mem_append'.mp a'ninσ₀A
      let aκ₁a'we := aκ₁we.typeExt a'ninaκ₁ κ₀e
      let σke' := σke a'
      rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at aκ₁a'we
      rw [← TypeEnvironment.empty_append (.typeExt ..)] at σke'
      let σke'' := σke'.weakening aκ₁a'we (Γ := .empty) (Γ'' := .typeExt .empty ..)
      rw [TypeEnvironment.empty_append] at σke'' aκ₁a'we
      rw [TypeEnvironment.append, TypeEnvironment.append] at σke''
      rw [← TypeEnvironment.append_empty (.multiConstrExt ..),
          TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty)] at aκ₁ψ'xwe
      have := σke''.Monotype_open_preservation Γcw aκ₁a'we nofun a'ninσ₀ a'ninA (τke a) (Γ' := .empty)
        |>.weakening aκ₁ψ'xwe (Γ := .multiTypeExt .empty ..) (Γ' := .multiConstrExt .empty ..)
          (Γ'' := .empty)
      rw [← TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty),
          TypeEnvironment.append_empty] at this
      exact this
    · intro i mem a x
      let aκ₁we := TypeEnvironment.WellFormednessAndElaboration.empty.multiTypeExt (fun _ => nofun)
        a.property (fun i _ => κ₁e i) (n := o) (Γc := Γc)
      let aκ₁ψ'xwe := aκ₁we.multiConstrExt (by
        intro _
        rw [TypeEnvironment.TermVarNotInDom, TypeEnvironment.termVarDom_multiTypeExt,
            TypeEnvironment.termVarDom]
        nofun
      ) x.property (ψke · · a) (n := l)
      apply TCₛτce i mem a x |>.soundness _ Γᵢw Γcw aκ₁ψ'xwe
      let ⟨a', a'nin⟩ := ↑(Aₛ i).freeTypeVars ++
        [[(ε,, </ a@k : κ₁@k // k in [:o] />)]].typeVarDom |>.exists_fresh
      let ⟨a'ninAₛᵢ, a'ninaκ₁⟩ := List.not_mem_append'.mp a'nin
      let aκ₁a'we := aκ₁we.typeExt a'ninaκ₁ κ₀e
      rw [← TypeEnvironment.empty_append (.multiTypeExt ..)] at aκ₁a'we
      let TCₛa'ke := TCₛke a' i mem |>.weakening aκ₁a'we (Γ := .empty) (Γ'' := .typeExt .empty ..)
      rw [TypeEnvironment.empty_append] at TCₛa'ke aκ₁a'we
      have : Monotype.typeClass (TCₛ i) (.var (.free a')) =
        (.TypeVar_open (.typeClass (TCₛ i) (.var (.bound 0))) a') := by
        simp [Monotype.TypeVar_open]
      rw [this, ← QualifiedType.TypeVar_open, ← TypeScheme.TypeVar_open] at TCₛa'ke
      rw [← TypeEnvironment.append_empty (.multiConstrExt ..),
          TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty)] at aκ₁ψ'xwe
      let this := TCₛa'ke.Monotype_open_preservation Γcw aκ₁a'we nofun (by
        rw [TypeScheme.freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars,
            Monotype.freeTypeVars]
        nofun
      ) a'ninAₛᵢ (τke a) (Γ' := .empty)
        |>.weakening aκ₁ψ'xwe (Γ := .multiTypeExt .empty ..) (Γ' := .multiConstrExt .empty ..)
          (Γ'' := .empty)
      rw [← TypeEnvironment.multiConstrExt_eq_append (Γ' := .empty),
          TypeEnvironment.append_empty, TypeScheme.Monotype_open, QualifiedType.Monotype_open,
          Monotype.Monotype_open, Monotype.Monotype_open, if_pos rfl] at this
      exact this

  | .term Mte => Mte.soundness σke Γᵢw Γcw .empty

end TabularTypeInterpreter
