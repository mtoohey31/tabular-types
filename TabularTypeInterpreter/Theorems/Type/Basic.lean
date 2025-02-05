import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Term
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.Lemmas.ClassEnvironment
import TabularTypeInterpreter.Lemmas.Type
import TabularTypeInterpreter.Lemmas.TypeEnvironment
import TabularTypeInterpreter.Semantics.Type
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter

open «F⊗⊕ω»
open Std

namespace Monotype.RowEquivalenceAndElaboration

theorem symm (ρee : [[Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ Fₚ' Fₛ', [[Γc; Γ ⊢ ρ₁ ≡(μ) ρ₀ ⇝ Fₚ', Fₛ']] := match ρee with
  | refl ρek κe => ⟨_, _, refl ρek κe⟩
  | comm perm perm' inv ξτske κe (ξ := ξ) (τ := τ) (A := A) (p := p) (p' := p') (n := n) => by
    let ξ' i := ξ (p.get! i)
    let τ' i := τ (p.get! i)
    rw [List.map_singleton_flatten, List.map_singleton_flatten, ← Std.Range.map_get!_eq (as := p),
        List.map_map]
    have : (fun i => (ξ i, τ i)) ∘ p.get! = fun i => (ξ' i, τ' i) := rfl
    rw [this]
    have : [:n].toList.map (fun i => (ξ i, τ i)) = p'.map fun i => (ξ' i, τ' i) := by
      symm
      let lengths_eq := perm'.length_eq
      rw [Std.Range.length_toList, Nat.sub_zero] at lengths_eq
      rw [← Std.Range.map_get!_eq (as := p'), List.map_map, Std.Range.map_eq_of_eq_of_mem (by
        intro i imem
        show _ = (ξ i, τ i)
        simp only [Function.comp, ξ', τ']
        rw [perm'.length_eq, Std.Range.length_toList] at imem
        rw [inv.right i imem]
      ), ← lengths_eq]
    rw [this, ← List.map_singleton_flatten, ← List.map_singleton_flatten (f := fun _ => (_, _))]
    rw [perm.length_eq, Std.Range.length_toList, Nat.sub_zero]
    let ⟨⟨B, ξke⟩, uni, ⟨_, _, _, κeq, h, _, τke⟩⟩ := ξτske.row_inversion
    cases κeq
    let lengths_eq := perm.length_eq
    rw [Std.Range.length_toList, Nat.sub_zero] at lengths_eq
    cases lengths_eq
    let ξ'ke i (imem : i ∈ [:p.length]) := ξke (p.get! i) <| Std.Range.mem_of_mem_toList <|
      perm.mem_iff.mp <| List.get!_mem imem.right
    let τ'ke i (imem : i ∈ [:p.length]) := τke (p.get! i) <| Std.Range.mem_of_mem_toList <|
      perm.mem_iff.mp <| List.get!_mem imem.right
    let uni' := uni.Perm_preservation perm (fun _ => rfl)
    exact ⟨_, _, comm perm' perm inv.symm (.row ξ'ke uni' τ'ke h) κe⟩
  | trans _ κe ρ₀₁ee ρ₁₂ee =>
    let ⟨_, _, ρ₁₀ee⟩ := ρ₀₁ee.symm Γwe
    let ⟨_, _, ρ₂₁ee⟩ := ρ₁₂ee.symm Γwe
    let ⟨κ', _, _, _, ρ₂ke⟩ := ρ₁₂ee.to_Kinding Γwe
    let ⟨_, κ'e⟩ := κ'.Elaboration_total
    ⟨_, _, trans ρ₂ke κ'e ρ₂₁ee ρ₁₀ee⟩
  | liftL μ liftke κe => ⟨_, _, liftR μ liftke κe⟩
  | liftR μ liftke κe => ⟨_, _, liftL μ liftke κe⟩

theorem soundness (ρee : [[Γc; Γ ⊢ ρ₀ ≡(μ) ρ₁ ⇝ Fₚ, Fₛ]])
  (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) (ρ₀ke : [[Γc; Γ ⊢ ρ₀ : R κ ⇝ A]]) (ρ₁ke : [[Γc; Γ ⊢ ρ₁ : R κ ⇝ B]])
  (κe : [[⊢ κ ⇝ K]])
  : [[Δ ⊢ Fₚ : ∀ a : K ↦ *. (⊗ (a$0 ⟦A⟧)) → ⊗ (a$0 ⟦B⟧)]] ∧
    [[Δ ⊢ Fₛ : ∀ a : K ↦ *. (⊕ (a$0 ⟦A⟧)) → ⊕ (a$0 ⟦B⟧)]] ∧
    Fₚ.TypeVarLocallyClosed ∧ Fₛ.TypeVarLocallyClosed := by match ρee with
  | refl ρ₀ke' κe' =>
    let ⟨κeq, Aeq⟩ := ρ₀ke.deterministic ρ₀ke'
    cases κeq
    cases Aeq
    cases κe.deterministic κe'
    cases ρ₀ke.deterministic ρ₁ke |>.right
    let Δwf := Γwe.soundness
    let Aki := ρ₀ke.soundness Γwe κe.row
    let Alc := Aki.TypeVarLocallyClosed_of
    exact ⟨.prod_id Δwf Aki, .sum_id Δwf Aki, .prod_id Alc, .sum_id Alc⟩
  | trans ρ₀ke' κe' ρ₀₁ee ρ₁₂ee =>
    let ⟨κeq, Aeq⟩ := ρ₀ke.deterministic ρ₀ke'
    cases κeq
    cases Aeq
    cases κe.deterministic κe'
    let ⟨_, _, A₁, ρ₀ke'', ρ₁ke'⟩ := ρ₀₁ee.to_Kinding Γwe
    cases ρ₀ke'.deterministic ρ₀ke'' |>.left
    let ⟨Fₚ₀₁ty, Fₛ₀₁ty, Fₚ₀₁lc, Fₛ₀₁lc⟩ := ρ₀₁ee.soundness Γwe ρ₀ke ρ₁ke' κe
    let ⟨_, _, A₂, ρ₁ke'', ρ₂ke⟩ := ρ₁₂ee.to_Kinding Γwe
    cases ρ₁ke'.deterministic ρ₁ke'' |>.left
    cases ρ₁ke.deterministic ρ₂ke |>.right
    let ⟨Fₚ₁₂ty, Fₛ₁₂ty, Fₚ₁₂lc, Fₛ₁₂lc⟩ := ρ₁₂ee.soundness Γwe ρ₁ke' ρ₂ke κe
    let Δwf := Γwe.soundness
    let I := A.freeTypeVars ++ A₁.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom
    let Aki := ρ₀ke.soundness Γwe κe.row
    let Alc := Aki.TypeVarLocallyClosed_of
    let A₁lc := ρ₁ke'.soundness Γwe κe.row |>.TypeVarLocallyClosed_of
    let Blc := ρ₁ke.soundness Γwe κe.row |>.TypeVarLocallyClosed_of
    exact ⟨
      .typeLam (I := I) fun a anin => by
        let ⟨aninAA₁B, aninΔ⟩ := List.not_mem_append'.mp anin
        let ⟨aninAA₁, aninB⟩ := List.not_mem_append'.mp aninAA₁B
        let ⟨aninA, aninA₁⟩ := List.not_mem_append'.mp aninAA₁
        let Δa := Δ.typeExt a (K.arr .star)
        let Δawf : [[⊢ Δa]] := Δwf.typeVarExt aninΔ
        simp only [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
        exact .lam (I := Δ.termVarDom) fun x xnin => by
          simp only [«F⊗⊕ω».Term.TermVar_open, if_pos]
          rw [Fₚ₀₁lc.TypeVar_open_id, Fₚ₁₂lc.TypeVar_open_id,
              Fₚ₀₁ty.TermVarLocallyClosed_of.TermVar_open_id,
              Fₚ₁₂ty.TermVarLocallyClosed_of.TermVar_open_id]
          rw [Alc.TypeVar_open_id]
          let Δax := Δa.termExt x [[⊗ (a ⟦A⟧)]]
          let Δaxwf := Δawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
            Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          apply Typing.app (A := [[⊗ (a ⟦A₁⟧)]])
          · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id (A := .arr ..) <| by
                  rw [Blc.TypeVar_open_id]
                  exact .arr (.prod (.listApp .var_free A₁lc)) (.prod (.listApp .var_free Blc))]
            apply Typing.typeApp _ <| .var <| .termVarExt .head
            simp only [Type.TypeVar_close, if_pos]
            rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁,
                Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninB]
            exact Fₚ₁₂ty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          · apply Typing.app (A := [[⊗ (a ⟦A⟧)]])
            · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id <|
                    .arr (.prod (.listApp .var_free Alc)) (.prod (.listApp .var_free A₁lc))]
              apply Typing.typeApp _ <| .var <| .termVarExt .head
              simp only [Type.TypeVar_close, if_pos]
              rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA,
                  Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁]
              exact Fₚ₀₁ty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
            · exact .var Δaxwf .head,
      .typeLam (I := I) fun a anin => by
        let ⟨aninAA₁B, aninΔ⟩ := List.not_mem_append'.mp anin
        let ⟨aninAA₁, aninB⟩ := List.not_mem_append'.mp aninAA₁B
        let ⟨aninA, aninA₁⟩ := List.not_mem_append'.mp aninAA₁
        let Δa := Δ.typeExt a (K.arr .star)
        let Δawf : [[⊢ Δa]] := Δwf.typeVarExt aninΔ
        simp only [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
        exact .lam (I := Δ.termVarDom) fun x xnin => by
          simp only [«F⊗⊕ω».Term.TermVar_open, if_pos]
          rw [Fₛ₀₁lc.TypeVar_open_id, Fₛ₁₂lc.TypeVar_open_id,
              Fₛ₀₁ty.TermVarLocallyClosed_of.TermVar_open_id,
              Fₛ₁₂ty.TermVarLocallyClosed_of.TermVar_open_id]
          rw [Alc.TypeVar_open_id]
          let Δax := Δa.termExt x [[⊕ (a ⟦A⟧)]]
          let Δaxwf := Δawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
            Aki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          apply Typing.app (A := [[⊕ (a ⟦A₁⟧)]])
          · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id (A := .arr ..) <| by
                  rw [Blc.TypeVar_open_id]
                  exact .arr (.sum (.listApp .var_free A₁lc)) (.sum (.listApp .var_free Blc))]
            apply Typing.typeApp _ <| .var <| .termVarExt .head
            simp only [Type.TypeVar_close, if_pos]
            rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁,
                Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninB]
            exact Fₛ₁₂ty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
          · apply Typing.app (A := [[⊕ (a ⟦A⟧)]])
            · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id <|
                    .arr (.sum (.listApp .var_free Alc)) (.sum (.listApp .var_free A₁lc))]
              apply Typing.typeApp _ <| .var <| .termVarExt .head
              simp only [Type.TypeVar_close, if_pos]
              rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA,
                  Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁]
              exact Fₛ₀₁ty.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty)
            · exact .var Δaxwf .head,
      .typeLam <| .lam (.prod <| .listApp (.var_bound Nat.one_pos) Alc.weaken) <|
        .app (.typeApp Fₚ₁₂lc.weaken (.var_bound Nat.one_pos)) <|
        .app (.typeApp Fₚ₀₁lc.weaken (.var_bound Nat.one_pos)) .var,
      .typeLam <| .lam (.sum <| .listApp (.var_bound Nat.one_pos) Alc.weaken) <|
        .app (.typeApp Fₛ₁₂lc.weaken (.var_bound Nat.one_pos)) <|
        .app (.typeApp Fₛ₀₁lc.weaken (.var_bound Nat.one_pos)) .var
    ⟩
  | comm perm perm' inv ξτske κe' (A := A') (p := p) (p' := p') =>
    rw [← Range.map_get!_eq (as := p)] at ρ₁ke ⊢
    rw [List.map_map, ← Range.map] at ρ₁ke
    let ⟨⟨_, ξke⟩, _, ⟨B', _, Beq, κeq, _, _, τke⟩⟩ := ρ₁ke.row_inversion
    cases Beq
    cases κeq
    let ⟨κeq, Aeq⟩ := ξτske.deterministic ρ₀ke
    cases κeq
    cases Aeq
    cases κe.deterministic κe'
    let ⟨⟨_, _⟩, _, ⟨A'', _, eq, eqκ, _, _, τke'⟩⟩ := ρ₀ke.row_inversion
    cases eqκ
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at eq
    let A'eq := Range.eq_of_mem_of_map_eq <| Type.list.inj eq
    let length_eq := perm.length_eq
    rw [Range.length_toList] at length_eq
    let length_eq' := perm'.length_eq
    rw [Range.length_toList, Nat.sub_zero] at length_eq'
    cases length_eq
    let A'slc' := by
      show ∀ i ∈ [:p.length], (A' i).TypeVarLocallyClosed 1
      intro i mem
      rw [A'eq i mem]
      rw [← Nat.zero_add 1]
      exact τke' i mem |>.soundness Γwe κe |>.TypeVarLocallyClosed_of.weaken
    let A'slc := by
      show ∀ A ∈ ([:p.length].map fun i => [A' i]).flatten, A.TypeVarLocallyClosed 1
      intro A' mem
      rw [List.map_singleton_flatten] at mem
      let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
      cases eq
      exact A'slc' i mem'
    exact ⟨
      .typeLam (I := Δ.typeVarDom) fun a anin => by
        simp only [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
        let Δawf := Γwe.soundness.typeVarExt anin (K := K.arr .star)
        exact .lam (I := Δ.termVarDom) fun x xnin => by
          simp only [«F⊗⊕ω».Term.TermVar_open, List.mapMem_eq_map, if_pos]
          rw [List.map_singleton_flatten, List.map_singleton_flatten, List.map_singleton_flatten,
              List.map_map, List.map_map, List.map_map, List.map_map, List.map_map,
              ← List.map_singleton_flatten, ← Range.map, ← List.map_singleton_flatten,
              ← Range.map, ← List.map_singleton_flatten, ← Range.map]
          apply Typing.equiv _ <| .prod .listAppR
          simp only [Function.comp, «F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TermVar_open, if_pos]
          apply Typing.prodIntro
          intro i imem
          simp only
          rw [← inv.left i imem]
          show Typing _ _
            ((fun i => .app (.var (.free a)) ((B' (p'.get! i)).TypeVar_open a)) (p.get! i))
          rw [inv.left i imem]
          apply Typing.prodElim _
            (Range.mem_of_mem_toList <| perm.mem_iff.mp <| List.get!_mem imem.right)
            (A := fun i => .app (.var (.free a)) ((B' (p'.get! i)).TypeVar_open a))
          apply Typing.equiv _ <| .prod .listAppL
          rw [Range.map, Range.map_eq_of_eq_of_mem fun i imem => by
                show [(A' i).TypeVar_open a] = [(B' (p'.get! i)).TypeVar_open a]
                let iltlen := imem.right
                rw [← length_eq'] at iltlen
                let τeki := τke (p'.get! i) <| Range.mem_of_mem_toList <| perm'.mem_iff.mp <|
                  List.get!_mem iltlen
                let τek'i := τke' i imem
                rw [← A'eq i imem] at τek'i
                rw [inv.right i imem] at τeki
                rw [τeki.deterministic τek'i |>.right] ]
          apply Typing.var _ .head
          apply Δawf |>.termVarExt xnin
          apply Kinding.prod
          apply Kinding.listApp <| .var .head
          apply Kinding.list
          intro i imem
          let iltlen := imem.right
          rw [← length_eq'] at iltlen
          let τkei := τke (p'.get! i) <| Range.mem_of_mem_toList <| perm'.mem_iff.mp <|
            List.get!_mem iltlen
          let B'ki := τkei.soundness Γwe κe
          simp only
          rw [B'ki.TypeVarLocallyClosed_of.TypeVar_open_id]
          exact B'ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty),
      .typeLam (I := Δ.typeVarDom) fun a anin => by
        simp only [«F⊗⊕ω».Term.TypeVar_open, Type.TypeVar_open, if_pos]
        let Δa := Δ.typeExt a <| K.arr .star
        let Δawf : [[⊢ Δa]] := Γwe.soundness.typeVarExt anin (K := K.arr .star)
        exact .lam (I := Δ.termVarDom) fun x xnin => by
          let Δaxwf := Δawf.termVarExt xnin <| by
            apply Kinding.sum
            apply Kinding.listApp <| .var .head
            apply Kinding.list
            intro i imem
            show Kinding _ ((A' i).TypeVar_open a) _
            let A'ki := τke' i imem |>.soundness Γwe κe
            rw [← A'eq i imem] at A'ki
            rw [A'ki.TypeVarLocallyClosed_of.TypeVar_open_id]
            exact A'ki.weakening Δawf (Δ' := .typeExt .empty ..) (Δ'' := .empty)
          simp only [«F⊗⊕ω».Term.TermVar_open, List.mapMem_eq_map, if_pos]
          rw [← Range.map_get!_eq (as := p'), length_eq', Range.map, List.map_singleton_flatten,
              List.map_singleton_flatten, List.map_singleton_flatten, List.zip_eq_zipWith,
              Range.map, List.zipWith_map_right, List.zipWith_same, List.map_map, List.map_map,
              List.map_map, List.map_map, List.map_map, ← List.map_singleton_flatten,
              ← Range.map, ← List.map_singleton_flatten, ← Range.map, ← List.map_singleton_flatten,
              ← Range.map]
          simp only [Function.comp]
          apply Typing.sumElim
          · exact .equiv (.var Δaxwf .head) <| .sum <| .listAppL
          · intro i imem
            simp only
            simp only [Type.TypeVar_open, «F⊗⊕ω».Term.TypeVar_open, «F⊗⊕ω».Term.TermVar_open,
                       if_pos]
            rw [if_neg (nomatch ·)]
            exact .lam (I := x :: Δa.termVarDom) fun x' x'nin => by
              simp only [«F⊗⊕ω».Term.TermVar_open, if_pos]
              apply Typing.equiv _ <| .sum <| .listAppR
              let iltplen := imem.right
              rw [← length_eq'] at iltplen
              apply Typing.sumIntro <| Range.mem_of_mem_toList <| perm'.mem_iff.mp <|
                List.get!_mem iltplen
              let iltlen := imem.right
              rw [← length_eq'] at iltlen
              let τeki := τke (p'.get! i) <| Range.mem_of_mem_toList <| perm'.mem_iff.mp <|
                List.get!_mem iltlen
              let τek'i := τke' i imem
              rw [← A'eq i imem] at τek'i
              rw [inv.right i imem] at τeki
              rw [← τeki.deterministic τek'i |>.right]
              apply Typing.var _ .head
              apply Δaxwf.termVarExt x'nin
              apply Kinding.app
              · exact .var <| .termVarExt <| .head
              · let B'ki := τeki.soundness Γwe κe
                rw [B'ki.TypeVarLocallyClosed_of.TypeVar_open_id]
                exact B'ki.weakening Δaxwf (Δ' := .termExt (.typeExt .empty ..) ..) (Δ'' := .empty),
      .typeLam <| .lam (.prod <| .listApp (.var_bound Nat.one_pos) (.list A'slc)) <|
        .prodIntro fun E mem => by
          rw [List.map_singleton_flatten, Range.map, List.map_map] at mem
          let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
          cases eq
          simp only [Function.comp]
          exact .prodElim .var,
      .typeLam <| .lam (.sum <| .listApp (.var_bound Nat.one_pos) (.list A'slc)) <|
        .sumElim .var fun E mem => by
          rw [List.map_singleton_flatten, ← Range.map_get!_eq (as := p'), length_eq',
              List.zip_eq_zipWith, Range.map, List.zipWith_map_right, List.zipWith_same,
              List.map_map] at mem
          let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
          cases eq
          simp only [Function.comp]
          exact .lam (.app (.var_bound Nat.one_pos) <| A'slc' i mem') <| .sumIntro .var
    ⟩
  | liftL μ liftke@(.lift I τ₁ke κ₀e ξτ₀ke) κe' (τ₀ := τ₀) (τ₁ := τ₁) =>
    rename_i A' _ _
    let ⟨κeq, Aeq⟩ := liftke.deterministic ρ₀ke
    cases κeq
    cases Aeq
    cases κe.deterministic κe'
    let ⟨⟨_, ξke⟩, uni, ⟨A'', _, eq₀, eq₁, h, _, τ₀ke⟩⟩ := ξτ₀ke.row_inversion
    cases eq₀
    cases eq₁
    let ξτopke := TypeScheme.KindingAndElaboration.row ξke uni (fun i imem =>
      let σ := TypeScheme.qual (QualifiedType.mono τ₁)
      let ⟨a, anin⟩ := σ.freeTypeVars ++ ↑A'.freeTypeVars ++ Γ.typeVarDom ++ I |>.exists_fresh
      let ⟨aninσA'Γ, aninI⟩ := List.not_mem_append'.mp anin
      let ⟨aninσA', aninΓ⟩ := List.not_mem_append'.mp aninσA'Γ
      let ⟨aninσ, aninA'⟩ := List.not_mem_append'.mp aninσA'
      τ₁ke a aninI |>.Monotype_open_preservation (Γ' := .empty) (Γwe.typeExt aninΓ κ₀e) (nomatch ·)
        aninσ aninA' <| τ₀ke i imem) h
    let ⟨κeq, Aeq⟩ := ξτopke.deterministic ρ₁ke
    cases κeq
    cases Aeq
    let Δwf := Γwe.soundness
    let Aki := ρ₀ke.soundness Γwe κe.row
    let Alc := Aki.TypeVarLocallyClosed_of
    exact ⟨
      .equiv (.prod_id Δwf Aki) <| .scheme (I := []) fun a anin => by
        simp only [Type.TypeVar_open, if_pos]
        rw [List.mapMem_eq_map, List.mapMem_eq_map, Range.map, List.map_singleton_flatten,
            List.map_singleton_flatten, List.map_map, List.map_map, ← List.map_singleton_flatten,
            ← Range.map, ← List.map_singleton_flatten, ← Range.map]
        simp only [Function.comp]
        apply TypeEquivalence.arr .refl <| .prod <| .trans _ .listAppR
        apply TypeEquivalence.trans (.listApp .refl .listAppL) <| .trans .listAppL <| .list _
        intro i imem
        apply TypeEquivalence.app .refl <| .trans .lamAppL _
        let .list A'opslc := ρ₁ke.soundness Γwe κe.row |>.TypeVarLocallyClosed_of
        rw [List.map_singleton_flatten] at A'opslc
        let A''ilc := τ₀ke i imem |>.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
        rw [A''ilc.TypeVar_open_id, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_id,
            A''ilc.Type_open_TypeVar_open_eq]
        exact .refl,
     .equiv (.sum_id Δwf Aki) <| .scheme (I := []) fun a anin => by
        simp only [Type.TypeVar_open, if_pos]
        rw [List.mapMem_eq_map, List.mapMem_eq_map, Range.map, List.map_singleton_flatten,
            List.map_singleton_flatten, List.map_map, List.map_map, ← List.map_singleton_flatten,
            ← Range.map, ← List.map_singleton_flatten, ← Range.map]
        simp only [Function.comp]
        apply TypeEquivalence.arr .refl <| .sum <| .trans _ .listAppR
        apply TypeEquivalence.trans (.listApp .refl .listAppL) <| .trans .listAppL <| .list _
        intro i imem
        apply TypeEquivalence.app .refl <| .trans .lamAppL _
        let .list A'opslc := ρ₁ke.soundness Γwe κe.row |>.TypeVarLocallyClosed_of
        rw [List.map_singleton_flatten] at A'opslc
        let A''ilc := τ₀ke i imem |>.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
        rw [A''ilc.TypeVar_open_id, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_id,
            A''ilc.Type_open_TypeVar_open_eq]
        exact .refl,
      .prod_id Alc,
      .sum_id Alc
    ⟩
  | liftR μ liftke@(.lift I τ₁ke κ₀e ξτ₀ke) κe' (τ₀ := τ₀) (τ₁ := τ₁) =>
    rename_i A' _ _
    let ⟨κeq, Aeq⟩ := liftke.deterministic ρ₁ke
    cases κeq
    cases Aeq
    cases κe.deterministic κe'
    let ⟨⟨_, ξke⟩, uni, ⟨A'', _, eq₀, eq₁, h, _, τ₀ke⟩⟩ := ξτ₀ke.row_inversion
    cases eq₀
    cases eq₁
    let ξτopke := TypeScheme.KindingAndElaboration.row ξke uni (fun i imem =>
      let σ := TypeScheme.qual (QualifiedType.mono τ₁)
      let ⟨a, anin⟩ := σ.freeTypeVars ++ ↑A'.freeTypeVars ++ Γ.typeVarDom ++ I |>.exists_fresh
      let ⟨aninσA'Γ, aninI⟩ := List.not_mem_append'.mp anin
      let ⟨aninσA', aninΓ⟩ := List.not_mem_append'.mp aninσA'Γ
      let ⟨aninσ, aninA'⟩ := List.not_mem_append'.mp aninσA'
      τ₁ke a aninI |>.Monotype_open_preservation (Γ' := .empty) (Γwe.typeExt aninΓ κ₀e) (nomatch ·)
        aninσ aninA' <| τ₀ke i imem) h
    let ⟨κeq, Aeq⟩ := ξτopke.deterministic ρ₀ke
    cases κeq
    cases Aeq
    let Δwf := Γwe.soundness
    let Aki := ρ₁ke.soundness Γwe κe.row
    let Alc := Aki.TypeVarLocallyClosed_of
    exact ⟨
      .equiv (.prod_id Δwf Aki) <| .scheme (I := []) fun a anin => by
        simp only [Type.TypeVar_open, if_pos]
        rw [List.mapMem_eq_map, List.mapMem_eq_map, Range.map, List.map_singleton_flatten,
            List.map_singleton_flatten, List.map_map, List.map_map, ← List.map_singleton_flatten,
            ← Range.map, ← List.map_singleton_flatten, ← Range.map]
        simp only [Function.comp]
        apply TypeEquivalence.arr (.prod <| .trans _ .listAppR) .refl
        apply TypeEquivalence.trans (.listApp .refl .listAppL) <| .trans .listAppL <| .list _
        intro i imem
        apply TypeEquivalence.app .refl <| .trans .lamAppL _
        let .list A'opslc := ρ₀ke.soundness Γwe κe.row |>.TypeVarLocallyClosed_of
        rw [List.map_singleton_flatten] at A'opslc
        let A''ilc := τ₀ke i imem |>.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
        rw [A''ilc.TypeVar_open_id, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_id,
            A''ilc.Type_open_TypeVar_open_eq]
        exact .refl,
      .equiv (.sum_id Δwf Aki) <| .scheme (I := []) fun a anin => by
        simp only [Type.TypeVar_open, if_pos]
        rw [List.mapMem_eq_map, List.mapMem_eq_map, Range.map, List.map_singleton_flatten,
            List.map_singleton_flatten, List.map_map, List.map_map, ← List.map_singleton_flatten,
            ← Range.map, ← List.map_singleton_flatten, ← Range.map]
        simp only [Function.comp]
        apply TypeEquivalence.arr (.sum <| .trans _ .listAppR) .refl
        apply TypeEquivalence.trans (.listApp .refl .listAppL) <| .trans .listAppL <| .list _
        intro i imem
        apply TypeEquivalence.app .refl <| .trans .lamAppL _
        let .list A'opslc := ρ₀ke.soundness Γwe κe.row |>.TypeVarLocallyClosed_of
        rw [List.map_singleton_flatten] at A'opslc
        let A''ilc := τ₀ke i imem |>.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
        rw [A''ilc.TypeVar_open_id, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_id,
            A''ilc.Type_open_TypeVar_open_eq]
        exact .refl,
      .prod_id Alc,
      .sum_id Alc
    ⟩

end Monotype.RowEquivalenceAndElaboration

theorem TypeScheme.KindingAndElaboration.TypeVar_open_deterministic {I₀ I₁ : List TypeVarId}
  (σke₀ : ∀ a ∉ I₀, [[Γc; Γ, a : κ ⊢ σ^a : κ₀ ⇝ A^a]])
  (σke₁ : ∀ a ∉ I₁, [[Γc; Γ, a : κ ⊢ σ^a : κ₁ ⇝ B^a]]) : κ₀ = κ₁ ∧ A = B :=
  let ⟨a, anin⟩ := I₀ ++ I₁ ++ ↑A.freeTypeVars ++ ↑B.freeTypeVars |>.exists_fresh
  let ⟨anin', aninB⟩ := List.not_mem_append'.mp anin
  let ⟨anin'', aninA⟩ := List.not_mem_append'.mp anin'
  let ⟨aninI₀, aninI₁⟩ := List.not_mem_append'.mp anin''
  let ⟨κeq, opeq⟩ := σke₀ a aninI₀ |>.deterministic <| σke₁ a aninI₁
  ⟨κeq, Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA aninB opeq⟩

theorem _root_.Exists.mkFun [Inhabited α] {p : Nat → α → Prop}
  : (∀ i ∈ [:n], ∃ a, p i a) → ∃ f : Nat → α, ∀ i ∈ [:n], p i (f i) := by
  intro h
  induction n with
  | zero => exact ⟨fun _ => default, fun i mem => nomatch mem⟩
  | succ n ih =>
    let ⟨f', h'⟩ := ih fun i mem => h i ⟨mem.lower, Nat.lt_add_right _ mem.upper⟩
    let ⟨a, h''⟩ := h n ⟨Nat.zero_le _, Nat.lt_succ_self _⟩
    let f i := if i = n then a else f' i
    apply Exists.intro f
    intro i mem
    dsimp only [f]
    split
    · case isTrue h''' =>
      cases h'''
      exact h''
    · case isFalse h''' =>
      exact h' i ⟨mem.lower, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ mem.upper) h'''⟩

namespace TypeScheme.EquivalenceAndElaboration

local instance : Inhabited «Type» where
  default := .list []
in
theorem to_Kinding (σee : [[Γc; Γ ⊢ σ₀ ≡ σ₁ ⇝ F]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]]) :
  ∃ κ A B, [[Γc; Γ ⊢ σ₀ : κ ⇝ A]] ∧ [[Γc; Γ ⊢ σ₁ : κ ⇝ B]] := by match σee with
  | refl σke => exact ⟨_, _, _, σke, σke⟩
  | arr τ₂₀ee τ₁₃ee τ₀τ₁ke τ₂ke =>
    let .arr _ τ₁ke := τ₀τ₁ke
    let ⟨_, _, _, τ₁ke', τ₃ke⟩ := τ₁₃ee.to_Kinding Γwe
    cases τ₁ke.deterministic τ₁ke' |>.left
    exact ⟨_, _, _, τ₀τ₁ke, τ₂ke.arr τ₃ke⟩
  | qual ψ₁₀ee γ₀₁ee ψ₀γ₀ke ψ₁ke =>
    let .qual _ γ₀ke κe := ψ₀γ₀ke
    let ⟨_, _, _, γ₀ke', γ₁ke⟩ := γ₀₁ee.to_Kinding Γwe
    cases γ₀ke.deterministic γ₀ke' |>.left
    exact ⟨_, _, _, ψ₀γ₀ke, ψ₁ke.qual γ₁ke κe⟩
  | scheme I σ'ee κ₀e σ₀ke (κ₁ := κ₁) (σ₁ := σ₁') =>
    let .scheme I' σ₀'ke _ := σ₀ke
    let ⟨a, anin⟩ := I ++ I' ++ Γ.typeVarDom ++ σ₁'.freeTypeVars |>.exists_fresh
    let ⟨aninII'Γ, aninσ₁'⟩ := List.not_mem_append'.mp anin
    let ⟨aninII', aninΓ⟩ := List.not_mem_append'.mp aninII'Γ
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let Γawe := Γwe.typeExt aninΓ κ₀e
    let ⟨_, _, B, σ₀'ke', σ₁'ke⟩ := σ'ee a aninI |>.to_Kinding Γawe
    cases σ₀'ke a aninI' |>.deterministic σ₀'ke' |>.left
    exact ⟨_, _, _, σ₀ke, .scheme (a :: Γ.typeVarDom) (A := B.TypeVar_close a) (by
      intro a' a'nin
      let ⟨a'nea, a'ninΓ⟩ := List.not_mem_cons.mp a'nin
      let ⟨_, κ₁e⟩ := κ₁.Elaboration_total
      rw [← σ₁'ke.soundness Γawe κ₁e |>.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_close_id
            (a := a)] at σ₁'ke
      let Γa'awe :=
        Γwe.typeExt a'ninΓ κ₀e |>.typeExt (List.not_mem_cons.mpr ⟨a'nea.symm, aninΓ⟩) κ₀e
      have := σ₁'ke.weakening Γa'awe (Γ' := .typeExt .empty ..) (Γ'' := .typeExt .empty ..)
        |>.Monotype_open_preservation (Γ' := .empty) Γa'awe (nomatch ·) aninσ₁'
        Type.not_mem_freeTypeVars_TypeVar_close (.var .head)
      rw [TypeEnvironment.TypeVar_subst, ← Type.TypeVar_open_eq_Type_open_var,
          ← TypeVar_open_eq_Monotype_open_var] at this
      exact this
    ) κ₀e⟩
  | prod τ₀₁ee prodke (n := n) (ξ := ξ) (τ₀ := τ₀) (τ₁ := τ₁) (b := b) =>
    let .prod μke ξτ₀ke := prodke
    generalize ξτ₀s'eq : ([:n].map fun i => [(ξ i, τ₀ i)]).flatten = ξτ₀s' at *
    generalize κ?eq : Option.filter (fun _ => b) (some Kind.star) = κ? at *
    let .row ξ'ke uni τ₀'ke h (ξ := ξ') := ξτ₀ke
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξτ₀s'eq
    let neqn' : List.length (List.map ..) = List.length _ := by rw [ξτ₀s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at neqn'
    cases neqn'
    let ξke i mem := by
      have := ξ'ke i mem
      simp only at this
      rw [← And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at this
      exact this
    rw [Range.map, List.map_singleton_flatten, Range.map_eq_of_eq_of_mem
          (Eq.symm <| And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq · ·),
        ← List.map_singleton_flatten, ← Range.map] at uni
    let τ₀ke i mem := by
      have := τ₀'ke i mem
      simp only at this
      rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at this
      exact this
    let ⟨_, τ₁ke⟩ := Exists.mkFun (n := n)
      (p := fun i A => KindingAndElaboration Γc Γ (.qual (.mono (τ₁ i))) .star A) <| by
      intro i mem
      let ⟨_, _, A, τ₀ke', τ₁ke⟩ := τ₀₁ee i mem |>.to_Kinding Γwe
      cases τ₀ke i mem |>.deterministic τ₀ke' |>.left
      exact ⟨A, τ₁ke⟩
    exact ⟨_, _, _, prodke, .prod μke <| .row ξke uni τ₁ke h⟩
  | sum τ₀₁ee sumke τ₀ke (n := n) (ξ := ξ) (τ₀ := τ₀) (τ₁ := τ₁) (b := b) =>
    let .sum μke ξτ₀ke := sumke
    generalize ξτ₀s'eq : ([:n].map fun i => [(ξ i, τ₀ i)]).flatten = ξτ₀s' at *
    generalize κ?eq : Option.filter (fun _ => b) (some Kind.star) = κ? at *
    let .row ξ'ke uni τ₀'ke h (ξ := ξ') := ξτ₀ke
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξτ₀s'eq
    let neqn' : List.length (List.map ..) = List.length _ := by rw [ξτ₀s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at neqn'
    cases neqn'
    let ξke i mem := by
      have := ξ'ke i mem
      simp only at this
      rw [← And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at this
      exact this
    rw [Range.map, List.map_singleton_flatten, Range.map_eq_of_eq_of_mem
          (Eq.symm <| And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq · ·),
        ← List.map_singleton_flatten, ← Range.map] at uni
    let ⟨_, τ₁ke⟩ := Exists.mkFun (n := n)
      (p := fun i A => KindingAndElaboration Γc Γ (.qual (.mono (τ₁ i))) .star A) <| by
      intro i mem
      let ⟨_, _, A, τ₀ke', τ₁ke⟩ := τ₀₁ee i mem |>.to_Kinding Γwe
      cases τ₀ke i mem |>.deterministic τ₀ke' |>.left
      exact ⟨A, τ₁ke⟩
    exact ⟨_, _, _, sumke, .sum μke <| .row ξke uni τ₁ke h⟩
  | prodRow ρ₀₁ee prodke@(.prod μke ρ₀ke) =>
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, prodke, .prod μke ρ₁ke⟩
  | sumRow ρ₀₁ee sumke@(.sum μke ρ₀ke) =>
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, sumke, .sum μke ρ₁ke⟩
  | contain _ _ _ _ containke _ _ ρ₂ke ρ₃ke κe =>
    let .contain μke .. := containke
    exact ⟨_, _, _, containke, .contain μke ρ₂ke ρ₃ke κe⟩
  | concat _ _ _ _ _ _ concatke _ _ _ ρ₃ke ρ₄ke ρ₅ke κe contain₀₂₃₅ee contain₁₂₄₅ee =>
    let .concat μke .. := concatke
    exact ⟨
      _,
      _,
      _,
      concatke,
      .concat μke ρ₃ke ρ₄ke ρ₅ke κe (.contain μke ρ₃ke ρ₅ke κe) (.contain μke ρ₄ke ρ₅ke κe)
    ⟩
  | tc τ₀₁ee σop₀₁ee _ TCₛee TCτ₀ke
  | tcRow τ₀₁ee σop₀₁ee _ TCₛee TCτ₀ke =>
    let ⟨_, _, _, τ₀ke, τ₁ke⟩ := τ₀₁ee.to_Kinding Γwe
    let .tc Γcw «γcin» τ₀ke' := TCτ₀ke
    cases τ₀ke.deterministic τ₀ke' |>.left
    exact ⟨_, _, _, TCτ₀ke, .tc Γcw «γcin» τ₁ke⟩
  | allRow I ρ₀₁ee allke ψke κe =>
    let ⟨_, _, _, ρ₀ke, ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γwe
    let .all _ _ _ ρ₀ke' := allke
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, _, _, allke, .all I ψke κe ρ₁ke⟩
  | split concatee =>
    let ⟨_, _, _, concatke@(.concat ..), concatke'@(.concat ..)⟩ := concatee.to_Kinding Γwe
    exact ⟨_, _, _, concatke.split, concatke'.split⟩
termination_by σ₀.sizeOf'
decreasing_by
  all_goals simp_arith
  all_goals (
    apply Nat.le_add_right_of_le
    apply Nat.le_add_right_of_le
    apply Nat.le_trans _ <| Nat.le_add_left ..
    rw [funext (f := _ ∘ _) (by
      intro x
      show _ = [(ξ x).sizeOf' + (τ₀ x).sizeOf']
      simp [Function.comp]
    ), List.map_singleton_flatten]
    apply Nat.le_trans (Nat.le_add_left _ (ξ i).sizeOf')
    apply List.le_sum_of_mem'
    exact Range.mem_map_of_mem mem
  )

local instance : Inhabited Term where
  default := .prodIntro []
in
theorem symm (σee : [[Γc; Γ ⊢ σ₀ ≡ σ₁ ⇝ F]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  : ∃ F', [[Γc; Γ ⊢ σ₁ ≡ σ₀ ⇝ F']] := by induction σee generalizing Δ with
  | refl σke => exact ⟨_, refl σke⟩
  | arr _ τ₁₃ee τ₀τ₁ke τ₂ke τ₂₀ih τ₁₃ih =>
    let ⟨_, τ₀₂ee⟩ := τ₂₀ih Γwe
    let ⟨_, τ₃₁ee⟩ := τ₁₃ih Γwe
    let .arr τ₀ke τ₁ke := τ₀τ₁ke
    let ⟨_, _, _, τ₁ke', τ₃ke⟩ := τ₁₃ee.to_Kinding Γwe
    cases τ₁ke.deterministic τ₁ke' |>.left
    exact ⟨_, arr τ₀₂ee τ₃₁ee (τ₂ke.arr τ₃ke) τ₀ke⟩
  | qual _ γ₀₁ee ψ₀γ₀ke ψ₁ke ψ₁₀ih γ₀₁ih =>
    let ⟨_, ψ₀₁ee⟩ := ψ₁₀ih Γwe
    let ⟨_, γ₁₀ee⟩ := γ₀₁ih Γwe
    let .qual ψ₀ke γ₀ke κe := ψ₀γ₀ke
    let ⟨_, _, _, γ₀ke', γ₁ke⟩ := γ₀₁ee.to_Kinding Γwe
    cases γ₀ke.deterministic γ₀ke' |>.left
    exact ⟨_, qual ψ₀₁ee γ₁₀ee (ψ₁ke.qual γ₁ke κe) ψ₀ke⟩
  | scheme I σ₀₁'ee κ₀e σ₀ke σ₀₁'ih => sorry
  | prod τ₀₁ee prodke τ₀₁ih =>
    let ⟨_, _, _, prodke', prod'ke⟩ := prod τ₀₁ee prodke |>.to_Kinding Γwe
    cases prodke.deterministic prodke' |>.left
    let ⟨_, τ₁₀ee⟩ := Exists.mkFun (τ₀₁ih · · Γwe)
    exact ⟨_, prod τ₁₀ee prod'ke⟩
  | sum τ₀₁ee sumke τ₀ke τ₀₁ih =>
    rename_i n _ _ _ τ₁ _ _ ξ b _ _
    let ⟨_, _, _, sumke', sum'ke⟩ := sum τ₀₁ee sumke τ₀ke |>.to_Kinding Γwe
    cases sumke.deterministic sumke' |>.left
    generalize ξτ₁s'eq : ([:n].map fun i => [(ξ i, τ₁ i)]).flatten = ξτ₁s' at sum'ke
    generalize κ?eq : Option.filter (fun _ => b) (some Kind.star) = κ? at sum'ke
    let .sum μke (.row ξ'ke uni τ₁'ke h) := sum'ke
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξτ₁s'eq
    let length_eq : List.length (List.map ..) = List.length _ := by rw [ξτ₁s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at length_eq
    cases length_eq
    rw [Range.map, List.map_singleton_flatten, Range.map_eq_of_eq_of_mem (by
      intro i mem
      show _ = (ξ i, τ₁ i)
      let ⟨ξeq, τeq⟩ := Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₁s'eq i mem
      rw [ξeq, τeq]
    ), ← List.map_singleton_flatten, ← Range.map]
    let ⟨_, τ₁₀ee⟩ := Exists.mkFun (τ₀₁ih · · Γwe)
    let ξke i mem := by
      have := ξ'ke i mem
      simp only at this
      rw [← And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₁s'eq i mem] at this
      exact this
    rw [Range.map, List.map_singleton_flatten, Range.map_eq_of_eq_of_mem (by
      intro i mem
      show _ = ξ i
      rw [And.left <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₁s'eq i mem]
    ), ← List.map_singleton_flatten, ← Range.map] at uni
    let τ₁ke i mem := by
      have := τ₁'ke i mem
      simp only at this
      rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₁s'eq i mem] at this
      exact this
    exact ⟨_, sum τ₁₀ee (.sum μke (.row ξke uni τ₁ke h)) τ₁ke⟩
  | prodRow ρ₀₁ee prodke =>
    let .prod μke ρ₀ke := prodke
    let ⟨_, _, ρ₁₀ee⟩ := ρ₀₁ee.symm Γwe
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, prodRow ρ₁₀ee <| .prod μke ρ₁ke⟩
  | sumRow ρ₀₁ee sumke =>
    let .sum μke ρ₀ke := sumke
    let ⟨_, _, ρ₁₀ee⟩ := ρ₀₁ee.symm Γwe
    let ⟨_, _, _, ρ₀ke', ρ₁ke⟩ := ρ₀₁ee.to_Kinding Γwe
    cases ρ₀ke.deterministic ρ₀ke' |>.left
    exact ⟨_, sumRow ρ₁₀ee <| .sum μke ρ₁ke⟩
  | contain ρ₀₂ee ρ₁₃ee ρ₂₀ee ρ₃₁ee containke ρ₀ke ρ₁ke ρ₂ke ρ₃ke κe =>
    let .contain μke .. := containke
    exact ⟨_, contain ρ₂₀ee ρ₃₁ee ρ₀₂ee ρ₁₃ee (.contain μke ρ₂ke ρ₃ke κe) ρ₂ke ρ₃ke ρ₀ke ρ₁ke κe⟩
  | concat ρ₀₃ee ρ₁₄ee ρ₂₅ee ρ₃₀ee ρ₄₁ee ρ₅₂ee concatke ρ₀ke ρ₁ke ρ₂ke ρ₃ke ρ₄ke ρ₅ke κe
      contain₀₂₃₅ee contain₁₂₄₅ee contain₀₂₃₅ih contain₁₂₄₅ih =>
    let .concat μke .. := concatke
    let ⟨_, contain₃₄₀₂ee⟩ := contain₀₂₃₅ih Γwe
    let ⟨_, contain₄₅₁₂ee⟩ := contain₁₂₄₅ih Γwe
    exact ⟨
      _,
      concat ρ₃₀ee ρ₄₁ee ρ₅₂ee ρ₀₃ee ρ₁₄ee ρ₂₅ee
        (.concat μke ρ₃ke ρ₄ke ρ₅ke κe (.contain μke ρ₃ke ρ₅ke κe) (.contain μke ρ₄ke ρ₅ke κe)) ρ₃ke
        ρ₄ke ρ₅ke ρ₀ke ρ₁ke ρ₂ke κe contain₃₄₀₂ee contain₄₅₁₂ee
    ⟩
  | tc τ₀₁ee σop₀₁ee «γcin» TCₛee TCτ₀ke τ₀₁ih σop₀₁ih TCₛih =>
    let ⟨_, _, _, TCτ₀ke', TCτ₁ke⟩ := tc τ₀₁ee σop₀₁ee «γcin» TCₛee TCτ₀ke |>.to_Kinding Γwe
    cases TCτ₀ke.deterministic TCτ₀ke' |>.left
    let ⟨_, τ₁₀ee⟩ := τ₀₁ih Γwe
    let ⟨_, σop₁₀ee⟩ := σop₀₁ih Γwe
    let ⟨_, TCₛee'⟩ := Exists.mkFun (TCₛih · · Γwe)
    exact ⟨_, tc τ₁₀ee σop₁₀ee «γcin» TCₛee' TCτ₁ke⟩
  | tcRow ρ₀₁ee σop₀₁ee «γcin» TCₛee TCρ₀ke σop₀₁ih TCₛih =>
    let ⟨_, _, _, TCρ₀ke', TCρ₁ke⟩ := tcRow ρ₀₁ee σop₀₁ee «γcin» TCₛee TCρ₀ke |>.to_Kinding Γwe
    cases TCρ₀ke.deterministic TCρ₀ke' |>.left
    let ⟨_, _, ρ₁₀ee⟩ := ρ₀₁ee.symm Γwe
    let ⟨_, σop₁₀ee⟩ := σop₀₁ih Γwe
    let ⟨_, TCₛee'⟩ := Exists.mkFun (TCₛih · · Γwe)
    exact ⟨_, tcRow ρ₁₀ee σop₁₀ee «γcin» TCₛee' TCρ₁ke⟩
  | allRow I ρ₀₁ee allke ψke κe =>
    let ⟨_, _, ρ₁₀ee⟩ := ρ₀₁ee.symm Γwe
    let ⟨_, _, _, allke', all'ke⟩ := allRow I ρ₀₁ee allke ψke κe |>.to_Kinding Γwe
    cases allke.deterministic allke' |>.left
    exact ⟨_, allRow I ρ₁₀ee all'ke ψke κe⟩
  | split _ concatih =>
    let ⟨_, concatke'⟩ := concatih Γwe
    exact ⟨_, concatke'.split⟩

-- TODO: Need to convert the hypothesis to ∀ τ then preserve this flexibility in the conclusions.
theorem _root_.TabularTypeInterpreter.TypeScheme.KindingAndElaboration.class_inversion {TC}
  (TCke : [[Γc; Γ ⊢ TC τ : κ ⇝ A]])
  : ∃ κ' A' n TCₛ Aₛ B m σ, κ = .constr ∧
    [[(</ TCₛ@i a ⇝ Aₛ@i // i in [:n] /> ⇒ TC a : κ') ↦ m : σ ⇝ A' ∈ Γc]] ∧
    [[Γc; Γ ⊢ τ : κ' ⇝ B]] ∧ A = [[⊗ {A'^^B, </ Aₛ@i^^B // i in [:n] />}]] := by
  let TCke@(.tc Γcw γcin τke) := TCke
  exact ⟨_, _, _, _, _, _, _, _, rfl, γcin, τke, rfl⟩

local instance : Inhabited «Type» where
  default := .list []
in
local instance : Inhabited TypeClass where
  default := .zero
in
theorem soundness (σee : [[Γc; Γ ⊢ σ₀ ≡ σ₁ ⇝ F]]) (Γwe : [[Γc ⊢ Γ ⇝ Δ]])
  (σ₀ke : [[Γc; Γ ⊢ σ₀ : κ ⇝ A]]) (σ₁ke : [[Γc; Γ ⊢ σ₁ : κ ⇝ B]]) (κe : [[⊢ κ ⇝ *]])
  : [[Δ ⊢ F : A → B]] := by induction σee generalizing A B κ Δ with
  | refl σke =>
    cases σ₀ke.deterministic σ₁ke |>.right
    rcases σ₀ke.deterministic σke with ⟨rfl, rfl⟩
    exact .id Γwe.soundness <| σke.soundness Γwe κe
  | arr _ _ τ₀₁ke τ₂ke τ₂₀ih τ₁₃ih =>
    let .arr τ₂ke' τ₃ke := σ₁ke
    cases τ₂ke.deterministic τ₂ke' |>.right
    cases σ₀ke.deterministic τ₀₁ke |>.right
    let .arr τ₀ke τ₁ke := τ₀₁ke
    rename TypeEnvironment => Γ
    apply Typing.lam Γ.termVarDom
    intro x xnin
    simp only [Term.TermVar_open, if_pos]
    rw [if_neg (nomatch ·)]
    apply Typing.lam <| x :: Δ.termVarDom
    intro xₐ xₐnin
    simp only [Term.TermVar_open, if_pos]
    rw [if_neg (nomatch ·)]
    let A'ki := τ₀ke.soundness Γwe .star
    let B'ki := τ₁ke.soundness Γwe .star
    let Δxwf := Γwe.soundness.termVarExt (Γwe.TermVarNotInDom_preservation xnin) (.arr A'ki B'ki)
    let Δxxₐwf : EnvironmentWellFormedness ((Δ.termExt x _).termExt xₐ _) := by
      apply Δxwf.termVarExt xₐnin
      exact τ₂ke.soundness Γwe .star |>.weakening Δxwf (Δ' := .termExt .empty ..) (Δ'' := .empty)
    apply Typing.app
    · let Fty := τ₁₃ih Γwe τ₁ke τ₃ke .star
      let Flc := Fty.TermVarLocallyClosed_of
      rw [Flc.weaken.TermVar_open_id, Flc.TermVar_open_id]
      exact Fty.weakening Δxxₐwf (Δ' := .termExt (.termExt .empty ..) ..) (Δ'' := .empty)
    · let xₐnex := List.ne_of_not_mem_cons xₐnin
      apply Typing.app <| .var Δxxₐwf <| .termVarExt .head xₐnex.symm
      apply Typing.app _ <| .var Δxxₐwf .head
      let Ety := τ₂₀ih Γwe τ₂ke τ₀ke .star
      let Elc := Ety.TermVarLocallyClosed_of
      rw [Elc.weaken.TermVar_open_id, Elc.TermVar_open_id]
      exact Ety.weakening Δxxₐwf (Δ' := .termExt (.termExt .empty ..) ..) (Δ'' := .empty)
  | qual _ _ ψ₀γ₀ke ψ₁ke ψ₁₀ih γ₀₁ih =>
    let .qual ψ₁ke' γ₁ke κe := σ₁ke
    cases ψ₁ke.deterministic ψ₁ke' |>.right
    rcases σ₀ke.deterministic ψ₀γ₀ke with ⟨rfl, rfl⟩
    let .qual ψ₀ke γ₀ke κ'e := ψ₀γ₀ke
    rename TypeEnvironment => Γ
    apply Typing.lam Γ.termVarDom
    intro x xnin
    simp only [Term.TermVar_open, if_pos]
    rw [if_neg (nomatch ·)]
    apply Typing.lam <| x :: Δ.termVarDom
    intro xₐ xₐnin
    simp only [Term.TermVar_open, if_pos]
    rw [if_neg (nomatch ·)]
    let A'ki := ψ₀ke.soundness Γwe .constr
    let B'ki := γ₀ke.soundness Γwe κe
    let Δxwf := Γwe.soundness.termVarExt (Γwe.TermVarNotInDom_preservation xnin) (.arr A'ki B'ki)
    let Δxxₐwf : EnvironmentWellFormedness ((Δ.termExt x _).termExt xₐ _) := by
      apply Δxwf.termVarExt xₐnin
      exact ψ₁ke.soundness Γwe .constr |>.weakening Δxwf (Δ' := .termExt .empty ..) (Δ'' := .empty)
    apply Typing.app
    · let Fty := γ₀₁ih Γwe γ₀ke γ₁ke κ'e
      let Flc := Fty.TermVarLocallyClosed_of
      rw [Flc.weaken.TermVar_open_id, Flc.TermVar_open_id]
      exact Fty.weakening Δxxₐwf (Δ' := .termExt (.termExt .empty ..) ..) (Δ'' := .empty)
    · let xₐnex := List.ne_of_not_mem_cons xₐnin
      apply Typing.app <| .var Δxxₐwf <| .termVarExt .head xₐnex.symm
      apply Typing.app _ <| .var Δxxₐwf .head
      let Ety := ψ₁₀ih Γwe ψ₁ke ψ₀ke .constr
      let Elc := Ety.TermVarLocallyClosed_of
      rw [Elc.weaken.TermVar_open_id, Elc.TermVar_open_id]
      exact Ety.weakening Δxxₐwf (Δ' := .termExt (.termExt .empty ..) ..) (Δ'' := .empty)
  | scheme I σ'ee κ'e σ₀ke' σ'ih =>
    rename «F⊗⊕ω».Kind => K'
    rcases σ₀ke.deterministic σ₀ke' with ⟨rfl, rfl⟩
    rename TypeEnvironment => Γ
    apply Typing.lam Γ.termVarDom
    intro x xnin
    simp only [Term.TermVar_open, if_pos]
    let .scheme I' σ'₀ke κ'e' := σ₀ke
    let .scheme I'' σ'₁ke κ'e'' := σ₁ke
    cases κ'e.deterministic κ'e'
    cases κ'e.deterministic κ'e''
    apply Typing.typeLam <| I ++ I' ++ I'' ++ Γ.typeVarDom
    intro a anin
    simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
    let ⟨aninII'I'', aninΓ⟩ := List.not_mem_append'.mp anin
    let ⟨aninII', aninI''⟩ := List.not_mem_append'.mp aninII'I''
    let ⟨aninI, aninI'⟩ := List.not_mem_append'.mp aninII'
    let Δxawf := Γwe.soundness.termVarExt (Γwe.TermVarNotInDom_preservation xnin)
      (σ₀ke'.soundness Γwe κe) |>.typeVarExt (K := K') <| Γwe.TypeVarNotInDom_preservation aninΓ
    let Fty := σ'ih a aninI (Γwe.typeExt aninΓ κ'e) (σ'₀ke a aninI') (σ'₁ke a aninI'') κe
    let Fty := Fty.weakening (Δ' := .termExt .empty x _) (Δ'' := .typeExt .empty a _) Δxawf
    rw [Term.TypeVar_open_TermVar_open_comm, Fty.TermVarLocallyClosed_of.TermVar_open_id]
    apply Typing.app Fty
    rw [Type.TypeVar_open_eq_Type_open_var]
    apply Typing.typeApp <| .var Δxawf <| .typeVarExt .head
    exact .var .head
  | prod τ₀₁ee prodke τ₀₁ih =>
    rename_i n _  _ τ₀ τ₁ F _ ξ b _
    rcases σ₀ke.deterministic prodke with ⟨rfl, rfl⟩
    apply Typing.lam Δ.termVarDom
    intro x xnin
    simp only [Term.TermVar_open]
    rw [List.mapMem_eq_map, List.map_singleton_flatten, List.map_map, funext (f := _ ∘ _) (by
      intro i
      show _ = ((F i).TermVar_open x).app (.prodElim i (.var (.free x)))
      simp only [Function.comp, Term.TermVar_open, if_pos]
    ), ← List.map_singleton_flatten, ← Range.map]
    generalize ξτ₀s'eq : ([:n].map fun i => [(ξ i, τ₀ i)]).flatten = ξτ₀s' at *
    generalize κ?eq : Option.filter (fun _ => b) (some Kind.star) = κ? at *
    let .prod μke (.row ξ'ke uni τ₀'ke h (τ := τ₀') (b := b')) := σ₀ke
    generalize ξτ₁s'eq : ([:n].map fun i => [(ξ i, τ₁ i)]).flatten = ξτ₁s' at *
    generalize κ'?eq : Option.filter (fun _ => b') (some Kind.star) = κ'? at *
    let .prod μke (.row _ uni τ₁'ke h (τ := τ₁')) := σ₁ke
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξτ₀s'eq ξτ₁s'eq
    let length_eq₀ : List.length (List.map ..) = List.length _ := by rw [ξτ₀s'eq]
    let length_eq₁ : List.length (List.map ..) = List.length _ := by rw [ξτ₁s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at length_eq₀ length_eq₁
    cases length_eq₀
    cases length_eq₁
    apply Typing.prodIntro
    intro i mem
    simp only
    let τ₀ke := τ₀'ke i mem
    let τ₁ke := τ₁'ke i mem
    simp only at τ₀ke τ₁ke
    rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at τ₀ke
    rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₁s'eq i mem] at τ₁ke
    let Fty := τ₀₁ih i mem Γwe τ₀ke τ₁ke .star
    rw [Fty.TermVarLocallyClosed_of.TermVar_open_id]
    let Δxwf := Γwe.soundness.termVarExt xnin <| prodke.soundness Γwe .star
    apply Typing.app <| Fty.weakening Δxwf (Δ' := .termExt .empty ..) (Δ'' := .empty)
    exact .prodElim (.var Δxwf .head) mem
  | sum τ₀₁ee sumke τ₀ke τ₀₁ih =>
    rename_i n _  _ τ₀ τ₁ F _ ξ b _ B'
    rcases σ₀ke.deterministic sumke with ⟨rfl, rfl⟩
    rename TypeEnvironment => Γ
    apply Typing.lam Γ.termVarDom
    intro x xnin
    simp only [Term.TermVar_open, if_pos]
    rw [List.mapMem_eq_map, List.map_singleton_flatten, List.map_map, funext (f := _ ∘ _) (by
      intro i
      show _ = Term.lam (B' i) (.sumIntro i (((F i).TermVar_open x (0 + 1)).app (.var (.bound 0))))
      simp only [Function.comp, Term.TermVar_open, if_pos]
      rw [if_neg (nomatch ·)]
    ), ← List.map_singleton_flatten, ← Range.map]
    generalize ξτ₀s'eq : ([:n].map fun i => [(ξ i, τ₀ i)]).flatten = ξτ₀s' at *
    generalize κ?eq : Option.filter (fun _ => b) (some Kind.star) = κ? at *
    let .sum μke (.row ξ'ke uni τ₀'ke h (τ := τ₀') (b := b')) := σ₀ke
    generalize ξτ₁s'eq : ([:n].map fun i => [(ξ i, τ₁ i)]).flatten = ξτ₁s' at *
    generalize κ'?eq : Option.filter (fun _ => b') (some Kind.star) = κ'? at *
    let .sum μke (.row _ uni τ₁'ke h (τ := τ₁')) := σ₁ke
    rw [List.map_singleton_flatten, List.map_singleton_flatten] at ξτ₀s'eq ξτ₁s'eq
    let length_eq₀ : List.length (List.map ..) = List.length _ := by rw [ξτ₀s'eq]
    let length_eq₁ : List.length (List.map ..) = List.length _ := by rw [ξτ₁s'eq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList, Nat.sub_zero,
        Nat.sub_zero] at length_eq₀ length_eq₁
    cases length_eq₀
    cases length_eq₁
    let Δxwf := Γwe.termExt xnin sumke |>.soundness
    apply Typing.sumElim <| .var Δxwf .head
    intro i mem
    simp only
    let τ₀ke' := τ₀'ke i mem
    let τ₁ke := τ₁'ke i mem
    simp only at τ₀ke' τ₁ke
    rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₀s'eq i mem] at τ₀ke'
    rw [← And.right <| Prod.mk.inj <| Range.eq_of_mem_of_map_eq ξτ₁s'eq i mem] at τ₁ke
    let Beq := τ₀ke i mem |>.deterministic τ₀ke' |>.right
    rw [Beq]
    apply Typing.lam <| x :: Δ.termVarDom
    intro x' x'nin
    simp only [Term.TermVar_open, if_pos]
    apply Typing.sumIntro mem
    let Fty := τ₀₁ih i mem Γwe τ₀ke' τ₁ke .star
    let Flc := Fty.TermVarLocallyClosed_of
    rw [Flc.weaken.TermVar_open_id, Flc.TermVar_open_id]
    let Δxx'wf := Δxwf.termVarExt x'nin <| τ₀ke'.soundness Γwe .star |>.weakening Δxwf
      (Δ' := .termExt .empty ..) (Δ'' := .empty)
    apply Typing.app <| Fty.weakening Δxx'wf (Δ' := .termExt (.termExt .empty ..) ..)
      (Δ'' := .empty)
    exact .var Δxx'wf .head
  | prodRow ρ₀₁ee prodke =>
    let Alc := σ₀ke.soundness Γwe κe |>.TypeVarLocallyClosed_of
    let .prod _ ρ₀ke := σ₀ke
    let .prod _ ρ₁ke := σ₁ke
    let Fₚty := ρ₀₁ee.soundness Γwe ρ₀ke ρ₁ke .star |>.left
    have := Typing.typeApp Fₚty (B := [[λ a : *. a$0]])
    simp only [Type.Type_open, if_pos] at this
    rw [ρ₀ke.soundness Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv (this .id) <| .arr (.prod .listAppIdL) (.prod .listAppIdL)
  | sumRow ρ₀₁ee sumke =>
    let Alc := σ₀ke.soundness Γwe κe |>.TypeVarLocallyClosed_of
    let .sum _ ρ₀ke := σ₀ke
    let .sum _ ρ₁ke := σ₁ke
    let Fₛty := ρ₀₁ee.soundness Γwe ρ₀ke ρ₁ke .star |>.right.left
    have := Typing.typeApp Fₛty (B := [[λ a : *. a$0]])
    simp only [Type.Type_open, if_pos] at this
    rw [ρ₀ke.soundness Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id,
        ρ₁ke.soundness Γwe (.row .star) |>.TypeVarLocallyClosed_of.Type_open_id] at this
    exact .equiv (this .id) <| .arr (.sum .listAppIdL) (.sum .listAppIdL)
  | contain ρ₀₂ee ρ₁₃ee ρ₂₀ee ρ₃₁ee containke ρ₀ke ρ₁ke ρ₂ke ρ₃ke κe' =>
    rename «F⊗⊕ω».Kind => K
    rcases σ₀ke.deterministic containke with ⟨rfl, rfl⟩
    let .contain _ ρ₀ke' ρ₁ke' κe'' := containke
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₁ke.deterministic ρ₁ke' |>.right
    cases κe'.deterministic κe''
    let .contain _ ρ₂ke' ρ₃ke' κe''' := σ₁ke
    rcases ρ₂ke.deterministic ρ₂ke' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₃ke.deterministic ρ₃ke' |>.right
    cases κe'.deterministic κe'''
    apply Typing.lam Δ.termVarDom
    intro xₑ xₑnin
    let Δxₑwf := Γwe.soundness.termVarExt xₑnin <| σ₀ke.soundness Γwe .constr
    simp [Term.TermVar_open]
    let ⟨F₀₂ₚty, _, F₀₂ₚlc, _⟩ := ρ₀₂ee.soundness Γwe ρ₀ke ρ₂ke κe'
    let ⟨F₃₁ₚty, _, F₃₁ₚlc, _⟩ := ρ₃₁ee.soundness Γwe ρ₃ke ρ₁ke κe'
    let ⟨_, F₂₀ₛty, _, F₂₀ₛlc⟩ := ρ₂₀ee.soundness Γwe ρ₂ke ρ₀ke κe'
    let ⟨_, F₁₃ₛty, _, F₁₃ₛlc⟩ := ρ₁₃ee.soundness Γwe ρ₁ke ρ₃ke κe'
    rw [F₀₂ₚty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
        F₃₁ₚty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
        F₁₃ₛty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
        F₂₀ₛty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id]
    apply Typing.prodIntro' _ <| by repeat rw [List.length_cons, List.length_singleton]
    intro _ mem
    rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_nil_left] at mem
    let A₀lc := ρ₀ke.soundness Γwe κe'.row |>.TypeVarLocallyClosed_of
    let A₁lc := ρ₁ke.soundness Γwe κe'.row |>.TypeVarLocallyClosed_of
    let A₂ki := ρ₂ke.soundness Γwe κe'.row
    let A₂lc := A₂ki.TypeVarLocallyClosed_of
    let A₃ki := ρ₃ke.soundness Γwe κe'.row
    let A₃lc := A₃ki.TypeVarLocallyClosed_of
    cases mem
    · case head =>
      simp only
      apply Typing.typeLam Δ.typeVarDom
      intro a anin
      let Δxₑawf := Δxₑwf.typeVarExt anin (K := K.arr .star)
      simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
      rw [F₀₂ₚlc.TypeVar_open_id, F₃₁ₚlc.TypeVar_open_id, A₂lc.TypeVar_open_id, A₃lc.TypeVar_open_id]
      apply Typing.lam <| xₑ :: Δ.termVarDom
      intro x xnin
      let xₑnex := List.ne_of_not_mem_cons xnin
      symm at xₑnex
      let Δxₑaxwf := Δxₑawf.termVarExt xnin <| .prod <| .listApp (.var .head) <|
        A₃ki.weakening Δxₑawf (Δ' := .typeExt (.termExt .empty ..) ..) (Δ'' := .empty)
      simp only [Term.TermVar_open, if_pos]
      rw [if_neg (nomatch ·), F₀₂ₚty.TermVarLocallyClosed_of.TermVar_open_id,
          F₃₁ₚty.TermVarLocallyClosed_of.TermVar_open_id]
      apply Typing.app
      · have := Typing.typeApp (B := .var a) <| F₀₂ₚty.weakening Δxₑaxwf
          (Δ' := .termExt (.typeExt (.termExt .empty ..) ..) ..) (Δ'' := .empty)
        simp [Type.Type_open] at this
        rw [A₂lc.Type_open_id,
            ρ₀ke.soundness Γwe κe'.row |>.TypeVarLocallyClosed_of.Type_open_id] at this
        apply this
        exact .var <| .termVarExt .head
      · apply Typing.app
        · rw [← Range.map_get!_eq (as := [_, _]), Range.map, ← List.map_singleton_flatten,
              ← Range.map] at Δxₑaxwf
          have := Typing.typeApp (B := .var a) <| .prodElim (.var Δxₑaxwf <|
            .termVarExt (.typeVarExt .head) xₑnex) ⟨Nat.le_refl _, by simp_arith⟩
          simp only [Type.Type_open, if_pos] at this
          rw [A₀lc.Type_open_id, A₁lc.Type_open_id] at this
          rw [Range.map, List.map_singleton_flatten, ← Range.map, Range.map_get!_eq] at this
          apply this
          exact .var <| .termVarExt .head
        · apply Typing.app _ <| .var Δxₑaxwf .head
          have := Typing.typeApp (B := .var a) <| F₃₁ₚty.weakening Δxₑaxwf
            (Δ' := .termExt (.typeExt (.termExt .empty ..) ..) ..) (Δ'' := .empty)
          simp [Type.Type_open] at this
          rw [A₁lc.Type_open_id, A₃lc.Type_open_id] at this
          apply this
          exact .var <| .termVarExt .head
    · case tail mem' =>
      cases mem'
      case tail mem'' => nomatch mem''
      simp only
      apply Typing.typeLam Δ.typeVarDom
      intro a anin
      let Δxₑawf := Δxₑwf.typeVarExt anin (K := K.arr .star)
      simp only [Term.TypeVar_open, Type.TypeVar_open, if_pos]
      rw [F₂₀ₛlc.TypeVar_open_id, F₁₃ₛlc.TypeVar_open_id, A₂lc.TypeVar_open_id, A₃lc.TypeVar_open_id]
      apply Typing.lam <| xₑ :: Δ.termVarDom
      intro x xnin
      let xₑnex := List.ne_of_not_mem_cons xnin
      symm at xₑnex
      let Δxₑaxwf := Δxₑawf.termVarExt xnin <| .sum <| .listApp (.var .head) <|
        A₂ki.weakening Δxₑawf (Δ' := .typeExt (.termExt .empty ..) ..) (Δ'' := .empty)
      simp [Term.TermVar_open]
      rw [F₁₃ₛty.TermVarLocallyClosed_of.TermVar_open_id,
          F₂₀ₛty.TermVarLocallyClosed_of.TermVar_open_id]
      apply Typing.app
      · have := Typing.typeApp (B := .var a) <| F₁₃ₛty.weakening Δxₑaxwf
          (Δ' := .termExt (.typeExt (.termExt .empty ..) ..) ..) (Δ'' := .empty)
        simp [Type.Type_open] at this
        rw [A₁lc.Type_open_id, A₃lc.Type_open_id] at this
        apply this
        exact .var <| .termVarExt .head
      · apply Typing.app
        · rw [← Range.map_get!_eq (as := [_, _]), Range.map, ← List.map_singleton_flatten,
              ← Range.map] at Δxₑaxwf
          have := Typing.typeApp (B := .var a) <| .prodElim (n := 1)
            (.var Δxₑaxwf <| .termVarExt (.typeVarExt .head) xₑnex) ⟨by simp_arith, by simp_arith⟩
          simp only [Type.Type_open, if_pos] at this
          rw [ρ₀ke.soundness Γwe κe'.row |>.TypeVarLocallyClosed_of.Type_open_id,
              A₁lc.Type_open_id] at this
          rw [Range.map, List.map_singleton_flatten, ← Range.map, Range.map_get!_eq] at this
          apply this
          exact .var <| .termVarExt .head
        · apply Typing.app _ <| .var Δxₑaxwf .head
          have := Typing.typeApp (B := .var a) <| F₂₀ₛty.weakening Δxₑaxwf
            (Δ' := .termExt (.typeExt (.termExt .empty ..) ..) ..) (Δ'' := .empty)
          simp [Type.Type_open] at this
          rw [A₀lc.Type_open_id, A₂lc.Type_open_id] at this
          apply this
          exact .var <| .termVarExt .head
  | concat ρ₀₃ee ρ₁₄ee ρ₂₅ee ρ₃₀ee ρ₄₁ee ρ₅₂ee concatke ρ₀ke ρ₁ke ρ₂ke ρ₃ke ρ₄ke ρ₅ke κe'
      contain₀₂₃₅ee contain₁₂₄₅ee contain₀₂₃₅ih contain₁₂₄₅ih =>
    rename «F⊗⊕ω».Kind => K
    rcases σ₀ke.deterministic concatke with ⟨rfl, rfl⟩
    let σ₀ke'@(.concat μke ρ₀ke' ρ₁ke' ρ₂ke' κe'' contain₀₂ke contain₁₂ke) := σ₀ke
    rcases ρ₀ke.deterministic ρ₀ke' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₁ke.deterministic ρ₁ke' |>.right
    cases ρ₂ke.deterministic ρ₂ke' |>.right
    cases κe'.deterministic κe''
    let .contain _ ρ₀ke'' ρ₂ke'' κe''' := contain₀₂ke
    rcases ρ₀ke.deterministic ρ₀ke'' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₂ke.deterministic ρ₂ke'' |>.right
    cases κe'.deterministic κe'''
    let .contain _ ρ₁ke'' ρ₂ke''' κe'''' := contain₁₂ke
    rcases ρ₁ke.deterministic ρ₁ke'' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₂ke.deterministic ρ₂ke''' |>.right
    cases κe'.deterministic κe''''
    let .concat _ ρ₃ke' ρ₄ke' ρ₅ke' κe''''' contain₃₅ke contain₄₅ke := σ₁ke
    rcases ρ₃ke.deterministic ρ₃ke' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₄ke.deterministic ρ₄ke' |>.right
    cases ρ₅ke.deterministic ρ₅ke' |>.right
    cases κe'.deterministic κe'''''
    let .contain _ ρ₃ke'' ρ₅ke'' κe'''''' := contain₃₅ke
    rcases ρ₃ke.deterministic ρ₃ke'' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₅ke.deterministic ρ₅ke'' |>.right
    cases κe'.deterministic κe''''''
    let .contain _ ρ₄ke'' ρ₅ke''' κe''''''' := contain₄₅ke
    rcases ρ₄ke.deterministic ρ₄ke'' with ⟨κeq, rfl⟩
    cases κeq
    cases ρ₅ke.deterministic ρ₅ke''' |>.right
    cases κe'.deterministic κe'''''''
    apply Typing.lam Δ.termVarDom
    intro xₑ xₑnin
    let Δxₑwf := Γwe.soundness.termVarExt xₑnin <| σ₀ke'.soundness Γwe .constr
    simp [Term.TermVar_open]
    let ⟨_, F₀₃ₛty, _, F₀₃ₛlc⟩ := ρ₀₃ee.soundness Γwe ρ₀ke ρ₃ke κe'
    let ⟨_, F₁₄ₛty, _, F₁₄ₛlc⟩ := ρ₁₄ee.soundness Γwe ρ₁ke ρ₄ke κe'
    let ⟨F₂₅ₚty, _, F₂₅ₚlc, _⟩ := ρ₂₅ee.soundness Γwe ρ₂ke ρ₅ke κe'
    let ⟨F₃₀ₚty, _, F₃₀ₚlc, _⟩ := ρ₃₀ee.soundness Γwe ρ₃ke ρ₀ke κe'
    let ⟨F₄₁ₚty, _, F₄₁ₚlc, _⟩ := ρ₄₁ee.soundness Γwe ρ₄ke ρ₁ke κe'
    let ⟨_, F₅₂ₛty, _, F₅₂ₛlc⟩ := ρ₅₂ee.soundness Γwe ρ₅ke ρ₂ke κe'
    let F₀₂₃₅ty :=
      contain₀₂₃₅ih Γwe (.contain μke ρ₀ke ρ₂ke κe') (.contain μke ρ₃ke ρ₅ke κe') .constr
    let F₁₂₄₅ty :=
      contain₁₂₄₅ih Γwe (.contain μke ρ₁ke ρ₂ke κe') (.contain μke ρ₄ke ρ₅ke κe') .constr
    rw [F₂₅ₚty.TermVarLocallyClosed_of.weaken (n := 2).TermVar_open_id,
        F₄₁ₚty.TermVarLocallyClosed_of.weaken (n := 2).TermVar_open_id,
        F₃₀ₚty.TermVarLocallyClosed_of.weaken (n := 2).TermVar_open_id,
        F₀₃ₛty.TermVarLocallyClosed_of.weaken (n := 4).TermVar_open_id,
        F₁₄ₛty.TermVarLocallyClosed_of.weaken (n := 4).TermVar_open_id,
        F₅₂ₛty.TermVarLocallyClosed_of.weaken (n := 3).TermVar_open_id,
        F₀₂₃₅ty.TermVarLocallyClosed_of.TermVar_open_id,
        F₁₂₄₅ty.TermVarLocallyClosed_of.TermVar_open_id]
    let A₀ki := ρ₀ke.soundness Γwe κe'.row
    let A₀lc := A₀ki.TypeVarLocallyClosed_of
    let A₁ki := ρ₁ke.soundness Γwe κe'.row
    let A₁lc := A₁ki.TypeVarLocallyClosed_of
    let A₂lc := ρ₂ke.soundness Γwe κe'.row |>.TypeVarLocallyClosed_of
    let A₃ki := ρ₃ke.soundness Γwe κe'.row
    let A₄ki := ρ₄ke.soundness Γwe κe'.row
    let A₃lc := A₃ki.TypeVarLocallyClosed_of
    let A₄lc := A₄ki.TypeVarLocallyClosed_of
    let A₅ki := ρ₅ke.soundness Γwe κe'.row
    let A₅lc := A₅ki.TypeVarLocallyClosed_of
    apply Typing.prodIntro' _ <| by repeat rw [List.length_cons]; repeat rw [List.length_nil]
    intro _ mem
    cases mem
    · case head =>
      simp only
      apply Typing.typeLam Δ.typeVarDom
      intro a anin
      let Δxₑawf := Δxₑwf.typeVarExt anin (K := K.arr .star)
      simp [Term.TypeVar_open, Type.TypeVar_open]
      rw [F₂₅ₚlc.TypeVar_open_id, F₃₀ₚlc.TypeVar_open_id, F₄₁ₚlc.TypeVar_open_id,
          A₃lc.TypeVar_open_id, A₄lc.TypeVar_open_id, A₅lc.TypeVar_open_id]
      apply Typing.lam <| xₑ :: Δ.termVarDom
      intro xₗ xₗnin
      let xₑnexₗ := List.ne_of_not_mem_cons xₗnin
      symm at xₑnexₗ
      let Δxₑaxₗwf := Δxₑawf.termVarExt xₗnin <| .prod <| .listApp (.var .head) <|
        A₃ki.weakening Δxₑawf (Δ' := .typeExt (.termExt .empty ..) ..) (Δ'' := .empty)
      simp [Term.TermVar_open]
      rw [F₂₅ₚty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
          F₃₀ₚty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
          F₄₁ₚty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id]
      apply Typing.lam <| xₗ :: xₑ :: Δ.termVarDom
      intro xᵣ xᵣnin
      let xₗnexᵣ := List.ne_of_not_mem_cons xᵣnin
      let xₑnexᵣ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xᵣnin
      symm at xₗnexᵣ xₑnexᵣ
      let Δxₑaxₗxᵣwf := Δxₑaxₗwf.termVarExt xᵣnin <| .prod <| .listApp (.var <| .termVarExt .head) <|
        A₄ki.weakening Δxₑaxₗwf (Δ' := .termExt (.typeExt (.termExt .empty ..) ..) ..)
          (Δ'' := .empty)
      simp [Term.TermVar_open]
      rw [F₂₅ₚty.TermVarLocallyClosed_of.TermVar_open_id,
          F₃₀ₚty.TermVarLocallyClosed_of.TermVar_open_id,
          F₄₁ₚty.TermVarLocallyClosed_of.TermVar_open_id]
      let xₑty := by
        rw [← Range.map_get!_eq (as := [_, _, _, _]), Range.map, ← List.map_singleton_flatten,
            ← Range.map] at Δxₑaxₗxᵣwf
        exact Typing.var Δxₑaxₗxᵣwf (.termVarExt (.termVarExt (.typeVarExt .head) xₑnexₗ) xₑnexᵣ)
      apply Typing.app
      · have := Typing.typeApp (B := .var a) <| F₂₅ₚty.weakening Δxₑaxₗxᵣwf
          (Δ' := .termExt (.termExt (.typeExt (.termExt .empty ..) ..) ..) ..) (Δ'' := .empty)
        simp [Type.Type_open] at this
        rw [A₂lc.Type_open_id, A₅lc.Type_open_id] at this
        exact this <| .var <| .termVarExt <| .termVarExt .head
      · apply Typing.app
        · apply Typing.app
          · have := Typing.typeApp (B := .var a) <|
              .prodElim (n := 0) xₑty ⟨by simp_arith, by simp_arith⟩
            rw [Range.map, List.map_singleton_flatten, ← Range.map,
                Range.map_get!_eq (as := [_, _, _, _])] at this
            simp [Term.Type_open, Type.Type_open] at this
            rw [A₀lc.Type_open_id, A₁lc.Type_open_id, A₂lc.Type_open_id] at this
            exact this <| .var <| .termVarExt <| .termVarExt .head
          · apply Typing.app
            · have := Typing.typeApp (B := .var a) <| F₃₀ₚty.weakening Δxₑaxₗxᵣwf
                (Δ' := .termExt (.termExt (.typeExt (.termExt .empty ..) ..) ..) ..) (Δ'' := .empty)
              simp [Type.Type_open] at this
              rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at this
              exact this <| .var <| .termVarExt <| .termVarExt .head
            · exact .var Δxₑaxₗxᵣwf <| .termVarExt .head xₗnexᵣ
        · apply Typing.app
          · have := Typing.typeApp (B := .var a) <| F₄₁ₚty.weakening Δxₑaxₗxᵣwf
              (Δ' := .termExt (.termExt (.typeExt (.termExt .empty ..) ..) ..) ..) (Δ'' := .empty)
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at this
            exact this <| .var <| .termVarExt <| .termVarExt .head
          · exact .var Δxₑaxₗxᵣwf .head
    · case tail mem' =>
      cases mem'
      · case head =>
        simp only
        apply Typing.typeLam Δ.typeVarDom
        intro a anin
        let Δxₑawf := Δxₑwf.typeVarExt anin (K := K.arr .star)
        simp [Term.TypeVar_open, Type.TypeVar_open]
        rw [A₀lc.weaken (n := 1).TypeVar_open_id, A₁lc.weaken (n := 1).TypeVar_open_id,
            A₃lc.weaken (n := 1).TypeVar_open_id, A₄lc.weaken (n := 1).TypeVar_open_id,
            A₅lc.weaken (n := 1).TypeVar_open_id, F₀₃ₛlc.weaken (n := 1).TypeVar_open_id,
            F₁₄ₛlc.weaken (n := 1).TypeVar_open_id, F₅₂ₛlc.weaken (n := 1).TypeVar_open_id]
        apply Typing.typeLam <| a :: Δ.typeVarDom
        intro aₜ aₜnin
        let aneaₜ := List.ne_of_not_mem_cons aₜnin
        symm at aneaₜ
        let Δxₑaaₜwf := Δxₑawf.typeVarExt aₜnin (K := .star)
        simp [Term.TypeVar_open, Type.TypeVar_open]
        rw [A₀lc.TypeVar_open_id, A₁lc.TypeVar_open_id, A₃lc.TypeVar_open_id, A₄lc.TypeVar_open_id,
            A₅lc.TypeVar_open_id, F₀₃ₛlc.TypeVar_open_id, F₁₄ₛlc.TypeVar_open_id,
            F₅₂ₛlc.TypeVar_open_id]
        apply Typing.lam <| xₑ :: Δ.termVarDom
        intro xₗ xₗnin
        let xₑnexₗ := List.ne_of_not_mem_cons xₗnin
        symm at xₑnexₗ
        let Δxₑaaₜxₗwf := Δxₑaaₜwf.termVarExt xₗnin <| .arr
          (.sum <| .listApp (.var <| .typeVarExt .head aneaₜ) <| A₃ki.weakening Δxₑaaₜwf
            (Δ' := .typeExt (.typeExt (.termExt .empty ..) ..) ..) (Δ'' := .empty))
          (.var <| .head)
        simp [Term.TermVar_open]
        rw [F₀₃ₛty.TermVarLocallyClosed_of.weaken (n := 3).TermVar_open_id,
            F₁₄ₛty.TermVarLocallyClosed_of.weaken (n := 3).TermVar_open_id,
            F₅₂ₛty.TermVarLocallyClosed_of.weaken (n := 2).TermVar_open_id]
        apply Typing.lam <| xₗ :: xₑ :: Δ.termVarDom
        intro xᵣ xᵣnin
        let xₑnexᵣ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xᵣnin
        let xₗnexᵣ := List.ne_of_not_mem_cons xᵣnin
        symm at xₑnexᵣ xₗnexᵣ
        let Δxₑaaₜxₗxᵣwf := Δxₑaaₜxₗwf.termVarExt xᵣnin <| .arr
          (.sum <| .listApp (.var <| .termVarExt <| .typeVarExt .head aneaₜ) <| A₄ki.weakening
            Δxₑaaₜxₗwf (Δ' := .termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..)
            (Δ'' := .empty))
          (.var <| .termVarExt .head)
        simp [Term.TermVar_open]
        rw [F₀₃ₛty.TermVarLocallyClosed_of.weaken (n := 2).TermVar_open_id,
            F₁₄ₛty.TermVarLocallyClosed_of.weaken (n := 2).TermVar_open_id,
            F₅₂ₛty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id]
        apply Typing.lam <| xᵣ :: xₗ :: xₑ :: Δ.termVarDom
        intro x xnin
        let xₑnex := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
          List.not_mem_of_not_mem_cons xnin
        let xₗnex := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xnin
        let xᵣnex := List.ne_of_not_mem_cons xnin
        symm at xₑnex xₗnex xᵣnex
        let Δxₑaₜxₗxᵣxwf := Δxₑaaₜxₗxᵣwf.termVarExt xnin <| .sum <| .listApp
          (.var <| .termVarExt <| .termVarExt <| .typeVarExt .head aneaₜ) <|
            A₅ki.weakening Δxₑaaₜxₗxᵣwf
            (Δ' := .termExt (.termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..) ..)
            (Δ'' := .empty)
        simp [Term.TermVar_open]
        rw [F₀₃ₛty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
            F₁₄ₛty.TermVarLocallyClosed_of.weaken (n := 1).TermVar_open_id,
            F₅₂ₛty.TermVarLocallyClosed_of.TermVar_open_id]
        let xₑty := by
          rw [← Range.map_get!_eq (as := [_, _, _, _]), Range.map, ← List.map_singleton_flatten,
              ← Range.map] at Δxₑaₜxₗxᵣxwf
          exact Typing.var Δxₑaₜxₗxᵣxwf
            (.termVarExt (.termVarExt (.termVarExt (.typeVarExt <| .typeVarExt .head) xₑnexₗ) xₑnexᵣ)
              xₑnex)
        apply Typing.app
        · apply Typing.app
          · apply Typing.app
            · have := Typing.typeApp (B := .var a) <|
                .prodElim (n := 1) xₑty ⟨by simp_arith, by simp_arith⟩
              rw [Range.map, List.map_singleton_flatten, ← Range.map,
                  Range.map_get!_eq (as := [_, _, _, _])] at this
              simp [Term.Type_open, Type.Type_open] at this
              have := (Typing.typeApp (B := .var aₜ) <| this ·)
              simp [Term.Type_open, Type.Type_open] at this
              apply this
              · exact .var <| .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head aneaₜ
              · exact .var <| .termVarExt <| .termVarExt <| .termVarExt .head
            · rw [A₀lc.weaken (n := 1).Type_open_id, A₀lc.Type_open_id]
              apply Typing.lam <| x :: xᵣ :: xₗ :: xₑ :: Δ.termVarDom
              intro xₗ' xₗ'nin
              let xₗnexₗ' := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
                List.not_mem_of_not_mem_cons xₗ'nin
              symm at xₗnexₗ'
              let Δxₑaₜxₗxᵣxxₗ'wf := Δxₑaₜxₗxᵣxwf.termVarExt xₗ'nin <| .sum <| .listApp
                (.var <| .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head aneaₜ) <|
                A₀ki.weakening Δxₑaₜxₗxᵣxwf
                  (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..) ..) ..)
                  (Δ'' := .empty)
              simp [Term.TermVar_open]
              rw [F₀₃ₛty.TermVarLocallyClosed_of.TermVar_open_id]
              apply Typing.app <| .var Δxₑaₜxₗxᵣxxₗ'wf <|
                .termVarExt (.termVarExt (.termVarExt .head xₗnexᵣ) xₗnex) xₗnexₗ'
              apply Typing.app _ <| .var Δxₑaₜxₗxᵣxxₗ'wf .head
              have := Typing.typeApp (B := .var a) <| F₀₃ₛty.weakening Δxₑaₜxₗxᵣxxₗ'wf
                (Δ' := .termExt (.termExt (.termExt (.termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..) ..) ..) ..)
                (Δ'' := .empty)
              simp [Type.Type_open] at this
              rw [A₀lc.Type_open_id, A₃lc.Type_open_id] at this
              apply this
              exact .var <|
                .termVarExt <| .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head aneaₜ
          · rw [A₁lc.weaken (n := 1).Type_open_id, A₁lc.Type_open_id]
            apply Typing.lam <| x :: xᵣ :: xₗ :: xₑ :: Δ.termVarDom
            intro xᵣ' xᵣ'nin
            let xᵣnexᵣ' := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons xᵣ'nin
            symm at xᵣnexᵣ'
            let Δxₑaₜxₗxᵣxxᵣ'wf := Δxₑaₜxₗxᵣxwf.termVarExt xᵣ'nin <| .sum <| .listApp
              (.var <| .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head aneaₜ) <|
              A₁ki.weakening Δxₑaₜxₗxᵣxwf
                (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..) ..) ..)
                (Δ'' := .empty)
            simp [Term.TermVar_open]
            rw [F₁₄ₛty.TermVarLocallyClosed_of.TermVar_open_id]
            apply Typing.app <| .var Δxₑaₜxₗxᵣxxᵣ'wf <| .termVarExt (.termVarExt .head xᵣnex) xᵣnexᵣ'
            apply Typing.app _ <| .var Δxₑaₜxₗxᵣxxᵣ'wf .head
            have := Typing.typeApp (B := .var a) <| F₁₄ₛty.weakening Δxₑaₜxₗxᵣxxᵣ'wf
              (Δ' := .termExt (.termExt (.termExt (.termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..) ..) ..) ..)
              (Δ'' := .empty)
            simp [Type.Type_open] at this
            rw [A₁lc.Type_open_id, A₄lc.Type_open_id] at this
            apply this
            exact .var <|
              .termVarExt <| .termVarExt <| .termVarExt <| .termVarExt <| .typeVarExt .head aneaₜ
        · rw [A₂lc.weaken (n := 1).Type_open_id, A₂lc.Type_open_id]
          have := Typing.typeApp (B := .var a) <| F₅₂ₛty.weakening Δxₑaₜxₗxᵣxwf
            (Δ' := .termExt (.termExt (.termExt (.typeExt (.typeExt (.termExt .empty ..) ..) ..) ..) ..) ..)
            (Δ'' := .empty)
          simp [Type.Type_open] at this
          rw [A₂lc.Type_open_id, A₅lc.Type_open_id] at this
          apply Typing.app <| this <| .var <| .termVarExt <| .termVarExt <| .termVarExt <|
            .typeVarExt .head aneaₜ
          exact .var Δxₑaₜxₗxᵣxwf .head
      · case tail mem'' =>
        cases mem''
        · case head =>
          simp only
          apply Typing.app <| F₀₂₃₅ty.weakening Δxₑwf (Δ' := .termExt .empty ..) (Δ'' := .empty)
          rw [← Range.map_get!_eq (as := [_, _, _, _]), Range.map, ← List.map_singleton_flatten,
              ← Range.map] at Δxₑwf ⊢
          exact .prodElim (n := 2) (.var Δxₑwf .head) ⟨by simp_arith, by simp_arith⟩
        · case tail mem''' =>
          cases mem'''
          · case head =>
            simp only
            apply Typing.app <| F₁₂₄₅ty.weakening Δxₑwf (Δ' := .termExt .empty ..) (Δ'' := .empty)
            rw [← Range.map_get!_eq (as := [_, _, _, _]), Range.map, ← List.map_singleton_flatten,
                ← Range.map] at Δxₑwf ⊢
            exact .prodElim (n := 3) (.var Δxₑwf .head) ⟨by simp_arith, by simp_arith⟩
          · case tail mem'''' => nomatch mem''''
  | tc τ₀₁ee σ'op₀₁ee γcin TCₛee TCτ₀ke τ₀₁ih σ'op₀₁ih TCₛih => sorry
  | tcRow => sorry
  | allRow I ρ₀₁ee allke ψke κe' =>
    rename_i ψ _ B' K
    rcases σ₀ke.deterministic allke with ⟨rfl, rfl⟩
    let .all I' ψke' κ'e ρ₀ke := allke
    let .all _ ψke'' κ'e' ρ₁ke := σ₁ke
    cases κ'e.deterministic κ'e'
    cases κ'e.deterministic κe'
    let ⟨Fₚty, _⟩ := ρ₀₁ee.soundness Γwe ρ₀ke ρ₁ke κ'e
    have := Typing.typeApp Fₚty (B := [[λ a : K. B']])
    simp only [Type.Type_open, if_pos,
               ρ₀ke.soundness Γwe κ'e.row |>.TypeVarLocallyClosed_of.Type_open_id,
               ρ₁ke.soundness Γwe κ'e.row |>.TypeVarLocallyClosed_of.Type_open_id] at this
    cases KindingAndElaboration.TypeVar_open_deterministic (σ := .qual (.mono ψ)) ψke ψke' |>.right
    cases KindingAndElaboration.TypeVar_open_deterministic (σ := .qual (.mono ψ)) ψke ψke'' |>.right
    apply this
    rename TypeEnvironment => Γ
    apply Kinding.lam <| I ++ Γ.typeVarDom
    intro a anin
    let ⟨aninI, aninΓ⟩ := List.not_mem_append'.mp anin
    exact ψke a aninI |>.soundness (Γwe.typeExt aninΓ κe') .constr
  | split _ concatih =>
    let .split concatke := σ₀ke
    let .split concat'ke := σ₁ke
    exact concatih Γwe concatke concat'ke .constr

end TypeScheme.EquivalenceAndElaboration

end TabularTypeInterpreter
