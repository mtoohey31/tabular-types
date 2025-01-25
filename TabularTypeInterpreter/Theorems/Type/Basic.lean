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
          rw [Fₚ₀₁lc.TypeVar_open_eq, Fₚ₁₂lc.TypeVar_open_eq,
              Fₚ₀₁ty.TermVarLocallyClosed_of.TermVar_open_eq,
              Fₚ₁₂ty.TermVarLocallyClosed_of.TermVar_open_eq]
          rw [Alc.TypeVar_open_eq]
          let Δax := Δa.termExt x [[⊗ (a ⟦A⟧)]]
          let Δaxwf := Δawf.termVarExt xnin <| by
            rw [← Δa.empty_append] at Δawf ⊢
            exact .prod <| .listApp (.var .head) <| Aki.weakening Δawf (Δ'' := .typeExt .empty ..)
          apply Typing.app (A := [[⊗ (a ⟦A₁⟧)]])
          · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id (A := .arr ..) <| by
                  rw [Blc.TypeVar_open_eq]
                  exact .arr (.prod (.listApp .var_free A₁lc)) (.prod (.listApp .var_free Blc))]
            apply Typing.typeApp _ <| .var <| .termVarExt .head
            rw [← (Δa.termExt x ..).empty_append]
            simp only [Type.TypeVar_close, if_pos]
            rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁,
                Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninB]
            apply Fₚ₁₂ty.weakening _ (Δ'' := .termExt (.typeExt .empty ..) ..)
            rw [Environment.empty_append]
            exact Δaxwf
          · apply Typing.app (A := [[⊗ (a ⟦A⟧)]])
            · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id <|
                    .arr (.prod (.listApp .var_free Alc)) (.prod (.listApp .var_free A₁lc))]
              apply Typing.typeApp _ <| .var <| .termVarExt .head
              rw [← ((Δ.typeExt ..).termExt ..).empty_append]
              simp only [Type.TypeVar_close, if_pos]
              rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA,
                  Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁]
              apply Fₚ₀₁ty.weakening _ (Δ'' := .termExt (.typeExt .empty ..) ..)
              rw [Environment.empty_append]
              exact Δaxwf
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
          rw [Fₛ₀₁lc.TypeVar_open_eq, Fₛ₁₂lc.TypeVar_open_eq,
              Fₛ₀₁ty.TermVarLocallyClosed_of.TermVar_open_eq,
              Fₛ₁₂ty.TermVarLocallyClosed_of.TermVar_open_eq]
          rw [Alc.TypeVar_open_eq]
          let Δax := Δa.termExt x [[⊕ (a ⟦A⟧)]]
          let Δaxwf := Δawf.termVarExt xnin <| by
            rw [← Δa.empty_append] at Δawf ⊢
            exact .sum <| .listApp (.var .head) <| Aki.weakening Δawf (Δ'' := .typeExt .empty ..)
          apply Typing.app (A := [[⊕ (a ⟦A₁⟧)]])
          · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id (A := .arr ..) <| by
                  rw [Blc.TypeVar_open_eq]
                  exact .arr (.sum (.listApp .var_free A₁lc)) (.sum (.listApp .var_free Blc))]
            apply Typing.typeApp _ <| .var <| .termVarExt .head
            simp only [Type.TypeVar_close, if_pos]
            rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁,
                Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars aninB]
            rw [← (Δa.termExt x ..).empty_append] at Δaxwf ⊢
            exact Fₛ₁₂ty.weakening Δaxwf (Δ'' := .termExt (.typeExt .empty ..) ..)
          · apply Typing.app (A := [[⊕ (a ⟦A⟧)]])
            · rw [← Type.TypeVarLocallyClosed.Type_open_var_TypeVar_close_id <|
                    .arr (.sum (.listApp .var_free Alc)) (.sum (.listApp .var_free A₁lc))]
              apply Typing.typeApp _ <| .var <| .termVarExt .head
              simp only [Type.TypeVar_close, if_pos]
              rw [Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA,
                  Type.TypeVar_close_eq_of_not_mem_freeTypeVars aninA₁]
              rw [← ((Δ.typeExt ..).termExt ..).empty_append] at Δaxwf ⊢
              exact Fₛ₀₁ty.weakening Δaxwf (Δ'' := .termExt (.typeExt .empty ..) ..)
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
          rw [B'ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
          rw [← (Δ.typeExt ..).empty_append] at Δawf ⊢
          exact B'ki.weakening Δawf (Δ'' := .typeExt .empty ..),
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
            rw [← (Δ.typeExt ..).empty_append, A'ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
            apply A'ki.weakening (Δ'' := .typeExt .empty ..)
            rw [Environment.empty_append]
            exact Δawf
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
                rw [B'ki.TypeVarLocallyClosed_of.TypeVar_open_eq]
                rw [← (Δa.termExt ..).empty_append] at Δaxwf ⊢
                exact B'ki.weakening Δaxwf (Δ'' := .termExt (.typeExt .empty ..)  ..),
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
        rw [A''ilc.TypeVar_open_eq, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_eq,
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
        rw [A''ilc.TypeVar_open_eq, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_eq,
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
        rw [A''ilc.TypeVar_open_eq, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_eq,
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
        rw [A''ilc.TypeVar_open_eq, A'opslc (A'.Type_open (A'' i)) (Range.mem_map_of_mem imem)
              |>.weaken (n := 1) |>.Type_open_drop (n := 1) Nat.one_pos |>.TypeVar_open_eq,
            A''ilc.Type_open_TypeVar_open_eq]
        exact .refl,
      .prod_id Alc,
      .sum_id Alc
    ⟩

end Monotype.RowEquivalenceAndElaboration

end TabularTypeInterpreter
