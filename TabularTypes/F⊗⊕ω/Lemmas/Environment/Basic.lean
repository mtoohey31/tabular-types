import Aesop
import TabularTypes.«F⊗⊕ω».Lemmas.Type.Basic
import TabularTypes.«F⊗⊕ω».Semantics.Environment

namespace TabularTypes.«F⊗⊕ω»

namespace Environment

open Std

theorem append_empty (Δ : Environment) : Δ.append empty = Δ := rfl

theorem empty_append (Δ : Environment) : append empty Δ = Δ := by
  match Δ with
  | empty => rfl
  | typeExt Δ' .. | termExt Δ' .. => rw [append, Δ'.empty_append]

theorem typeVarDom_append : (append Δ Δ').typeVarDom = Δ'.typeVarDom ++ Δ.typeVarDom := by
  match Δ' with
  | empty => rw [append, typeVarDom, List.nil_append]
  | typeExt .. => rw [append, typeVarDom, typeVarDom_append, typeVarDom, List.cons_append]
  | termExt .. => rw [append, typeVarDom, typeVarDom_append, typeVarDom]

theorem termVarDom_append : (append Δ Δ').termVarDom = Δ'.termVarDom ++ Δ.termVarDom := by
  match Δ' with
  | empty => rw [append, termVarDom, List.nil_append]
  | typeExt .. => rw [append, termVarDom, termVarDom_append, termVarDom]
  | termExt .. => rw [append, termVarDom, termVarDom_append, termVarDom, List.cons_append]

theorem append_type_assoc {Δ Δ': Environment} : [[ (Δ , ((ε , a : K) , Δ')) ]] = [[ (Δ , a : K) , Δ' ]] := by
  induction Δ' generalizing Δ <;> simp_all [append]

theorem append_term_assoc {Δ Δ': Environment} : [[ (Δ , ((ε , x : T) , Δ')) ]] = [[ (Δ , x : T) , Δ' ]] := by
  induction Δ' generalizing Δ <;> simp_all [append]

theorem append_assoc {Δ Δ' Δ'': Environment} : [[ (Δ , (Δ', Δ'')) ]] = [[ (Δ , Δ'), Δ'' ]] := by
  induction Δ'' <;> simp_all [append]

theorem typeVarDom_TypeVar_subst {Δ: Environment} : (Δ.TypeVar_subst a A).typeVarDom = Δ.typeVarDom  := by
  induction Δ <;> simp_all [TypeVar_subst, typeVarDom]

theorem append_typeExt_assoc {Δ Δ': Environment} : [[ (Δ, Δ'), a: K ]] = [[ (Δ, (Δ', a: K)) ]] := by simp_all [append]

theorem append_termExt_assoc {Δ Δ': Environment} : [[ (Δ, Δ'), x: T ]] = [[ (Δ, (Δ', x: T)) ]] := by simp_all [append]

theorem typeExt_subst {Δ: Environment} : (Δ.TypeVar_subst a K).typeExt a' K' = (Δ.typeExt a' K').TypeVar_subst a K := by
  induction Δ <;> simp_all [TypeVar_subst, typeExt]

theorem TypeVar_multi_subst_snoc :
  TypeVar_multi_subst Δ (Aa ++ [(A, a)]) = TypeVar_multi_subst (TypeVar_subst Δ a A) Aa := by
  match Aa with
  | [] => rw [List.nil_append, TypeVar_multi_subst, TypeVar_multi_subst, TypeVar_multi_subst]
  | (A', a') :: Aa' =>
    rw [List.cons_append, TypeVar_multi_subst, TypeVar_multi_subst, TypeVar_multi_subst_snoc]

theorem TypeVar_multi_subst_empty : TypeVar_multi_subst empty Aa = empty := by
  match Aa with
  | [] => rw [TypeVar_multi_subst]
  | (A, a) :: Aa' => rw [TypeVar_multi_subst, TypeVar_multi_subst_empty, TypeVar_subst]

theorem typeExt_append_assoc : [[(Δ, a : K), Δ']] = [[Δ, (ε, a : K, Δ')]] := by
  match Δ' with
  | empty => rw [append, append, append, append]
  | [[Δ', a' : K']] | [[Δ', x : A]] => rw [append, typeExt_append_assoc, ← append, ← append]

theorem termExt_append_assoc : [[(Δ, x : A), Δ']] = [[Δ, (ε, x : A, Δ')]] := by
  match Δ' with
  | empty => rw [append, append, append, append]
  | [[Δ', a : K]] | [[Δ', x' : A']] => rw [append, termExt_append_assoc, ← append, ← append]

theorem multiTypeExt_snoc
  : multiTypeExt Δ (aKs ++ [(a, K)]) = (multiTypeExt Δ aKs).typeExt a K := by match aKs with
  | [] => rw [List.nil_append, multiTypeExt, multiTypeExt, multiTypeExt]
  | (_, _) :: _ => rw [List.cons_append, multiTypeExt, multiTypeExt, multiTypeExt_snoc]

theorem multiTermExt_snoc
  : multiTermExt Δ (xAs ++ [(x, A)]) = (multiTermExt Δ xAs).termExt x A := by match xAs with
  | [] => rw [List.nil_append, multiTermExt, multiTermExt, multiTermExt]
  | (_, _) :: _ => rw [List.cons_append, multiTermExt, multiTermExt, multiTermExt_snoc]

theorem multiTypeExt_eq_append
  : [[Δ,, </ a@i : K@i // i in [:n] />, Δ']] = [[Δ, ε,, </ a@i : K@i // i in [:n] />, Δ']] := by
  match n with
  | 0 => rw [Range.map_same_eq_nil, multiTypeExt, multiTypeExt, empty_append]
  | n' + 1 =>
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one, multiTypeExt_snoc,
        multiTypeExt_snoc, typeExt_append_assoc, typeExt_append_assoc (Δ := .multiTypeExt ..),
        multiTypeExt_eq_append]

theorem multiTermExt_eq_append
  : [[Δ,,, </ x@i : A@i // i in [:n] />, Δ']] = [[Δ, ε,,, </ x@i : A@i // i in [:n] />, Δ']] := by
  match n with
  | 0 => rw [Range.map_same_eq_nil, multiTermExt, multiTermExt, empty_append]
  | n' + 1 =>
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Nat.succ_sub_one, multiTermExt_snoc,
        multiTermExt_snoc, termExt_append_assoc, termExt_append_assoc (Δ := .multiTermExt ..),
        multiTermExt_eq_append]

theorem TypeVar_multi_subst_termExt (aninA : ∀ i < n, a i ∉ A.freeTypeVars)
  (aninB : ∀ i < n, ∀ j < n, a i ∉ (B j).freeTypeVars) (ainj : a.Injective')
  (Blc : ∀ i < n, (B i).TypeVarLocallyClosed)
  : [[(Δ, x : A^^^a#n) ! </ [B@i / a@i] // i in [:n] />]] =
    [[Δ ! </ [B@i / a@i] // i in [:n] />, x : A^^^^B@@i#n/a]] := by
  match n with
  | 0 =>
    rw [Range.map_same_eq_nil, TypeVar_multi_subst, TypeVar_multi_subst, Type.TypeVar_multi_open,
        Type.Type_multi_open]
  | n' + 1 =>
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), TypeVar_multi_subst_snoc,
        TypeVar_multi_subst_snoc, Type.TypeVar_multi_open, Nat.succ_sub_one, TypeVar_subst,
        Type.TypeVar_open_TypeVar_multi_open_comm Nat.le.refl,
        Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars
          (Type.not_mem_freeTypeVars_TypeVar_multi_open_intro (aninA _ Nat.le.refl)
            (fun _ lt eq => Nat.ne_of_lt lt <| ainj _ _ eq.symm)),
        ← Type.TypeVarLocallyClosed.Type_open_TypeVar_multi_open_comm (Blc _ Nat.le.refl)
          Nat.le.refl, TypeVar_multi_subst_termExt _ _ ainj _, Type.Type_multi_open]
    · intro i lt
      apply Type.not_mem_freeTypeVars_Type_open_intro <| aninA _ <| Nat.lt_add_right _ lt
      exact aninB _ (Nat.lt_add_right _ lt) _ Nat.le.refl
    · intro i ilt j jlt
      apply aninB _ (Nat.lt_add_right _ ilt) _ (Nat.lt_add_right _ jlt)
    · intro i lt
      exact Blc _ <| Nat.lt_add_right _ lt


run_cmd Lott.addNatAlias `m

theorem multiTermExt_Type_multi_open_TypeVar_multi_subst_TypeVar_multi_open
  (aninA : ∀ i < m, ∀ j < n, a i ∉ (A j).freeTypeVars)
  (aninB : ∀ i < m, ∀ j < m, a i ∉ (B j).freeTypeVars) (ainj : a.Injective')
  (Blc : ∀ i < m, (B i).TypeVarLocallyClosed)
  : [[ε,,, </ x@i : A@i^^^^B@@j#m/a // i in [:n] />]] =
    [[(ε,,, </ x@i : A@i^^^a#m // i in [:n] />) ! </ [B@j / a@j] // j in [:m] />]] := by
  match n with
  | 0 => rw [Range.map_same_eq_nil, Range.map_same_eq_nil, multiTermExt, TypeVar_multi_subst_empty]
  | n' + 1 =>
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), multiTermExt_snoc, Nat.succ_sub_one,
        Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), multiTermExt_snoc, Nat.succ_sub_one,
        TypeVar_multi_subst_termExt (aninA · · _ Nat.le.refl) aninB ainj Blc,
        multiTermExt_Type_multi_open_TypeVar_multi_subst_TypeVar_multi_open
          (aninA · · · <| Nat.lt_add_right _ ·) aninB ainj Blc]

end Environment

namespace TypeVarInDom

open Environment in
theorem TypeVarInEnvironment_of (aInDomΔ : [[a ∈ dom(Δ)]]) : ∃ K, [[a : K ∈ Δ]] := by
  induction Δ
  . case empty => simp_all [TypeVarInDom, typeVarDom]
  . case typeExt Δ a' K' ih =>
    simp_all [TypeVarInDom, typeVarDom]
    cases aInDomΔ
    . case inl eq =>
      exists K'
      subst a'
      constructor
    . case inr h =>
      obtain ⟨K, h⟩ := ih h
      by_cases (a = a')
      . case pos eq =>
        subst a'
        exists K'
        constructor
      . case neg neq =>
        exists K
        constructor <;> simp_all [TypeVarNe]
  . case termExt Δ a' T ih =>
    obtain ⟨K, ih⟩ := ih aInDomΔ
    exists K
    constructor
    exact ih

end TypeVarInDom

namespace TermVarInDom

open Environment in
theorem TermVarInEnvironment_of (xInDomΔ : [[x ∈ dom(Δ)]]) : ∃ T, [[x : T ∈ Δ]] := by
  induction Δ
  . case empty => simp_all [TermVarInDom, termVarDom]
  . case typeExt Δ a' K' ih =>
    obtain ⟨K, ih⟩ := ih xInDomΔ
    exists K
    constructor
    exact ih
  . case termExt Δ x' T' ih =>
    simp_all [TermVarInDom, termVarDom]
    cases xInDomΔ
    . case inl eq =>
      exists T'
      subst x'
      constructor
    . case inr h =>
      obtain ⟨T, h⟩ := ih h
      by_cases (x = x')
      . case pos eq =>
        subst x'
        exists T'
        constructor
      . case neg neq =>
        exists T
        constructor <;> simp_all [TermVarNe]

end TermVarInDom
namespace TypeVarInEnvironment

theorem deterministic (aK₁inΔ : [[a : K₁ ∈ Δ]]) (aK₂inΔ : [[a : K₂ ∈ Δ]]) : K₁ = K₂ :=
  match aK₁inΔ with
  | .head =>
    let .head := aK₂inΔ
    rfl
  | .typeVarExt aK₁inΔ' ne => match aK₂inΔ with
    | .head => nomatch ne
    | .typeVarExt aK₂inΔ' _ => aK₁inΔ'.deterministic aK₂inΔ'
  | .termVarExt aK₁inΔ' =>
    let .termVarExt aK₂inΔ' := aK₂inΔ
    aK₁inΔ'.deterministic aK₂inΔ'

theorem eq_of (aKinΔ : [[a : K ∈ Δ]]) : ∃ Δ' Δ'', Δ = [[(Δ', a : K, Δ'')]] := by
  match aKinΔ with
  | .head => exact ⟨_, .empty, rfl⟩
  | .typeVarExt aKinΔ' _ =>
    rcases aKinΔ'.eq_of with ⟨_, _, rfl⟩
    rw [← Environment.append]
    exact ⟨_, _, rfl⟩
  | .termVarExt aKinΔ' =>
    rcases aKinΔ'.eq_of with ⟨_, _, rfl⟩
    rw [← Environment.append]
    exact ⟨_, _, rfl⟩

theorem TypeVarInDom_of (aKinΔ : [[a : K ∈ Δ]]) : [[a ∈ dom(Δ)]] :=
  match aKinΔ with
  | .head => .head _
  | .typeVarExt aKinΔ' anea' => .tail _ aKinΔ'.TypeVarInDom_of
  | .termVarExt aKinΔ' => aKinΔ'.TypeVarInDom_of

theorem unique {Δ: Environment} {K K': Kind}: [[ a: K ∈ Δ ]] → [[ a: K' ∈ Δ ]] → K = K' := by
  intro aKIn aK'In
  induction Δ generalizing a K K'
  . case empty => cases aKIn
  . case typeExt Δ a_ K_ ih =>
    aesop (add norm TypeVarNe, unsafe cases TypeVarInEnvironment)
  . case termExt Δ a_ T ih =>
    aesop (add unsafe cases TypeVarInEnvironment)

theorem weakening_l : [[ a: K ∈ Δ' ]] → [[ a: K ∈ Δ, Δ' ]] := by
  intro h
  induction Δ' <;> aesop
    (add norm Environment.append,
      unsafe constructors TypeVarInEnvironment, safe cases TypeVarInEnvironment)

open Environment in
theorem weakening_r (fresh: [[ a ∉ dom(Δ') ]]): [[ a: K ∈ Δ ]] → [[ a: K ∈ Δ, Δ' ]] := by
  intro h
  induction Δ' <;> simp_all [append]
    <;> constructor <;> simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom, TypeVarNe]

open Environment in
theorem append_elim : [[ a: K ∈ Δ, Δ' ]] → ([[ a ∉ dom(Δ') ]] ∧ [[ a: K ∈ Δ ]]) ∨ [[ a: K ∈ Δ' ]] := by
  by_cases ([[ a ∈ dom(Δ') ]])
  . case pos hIn =>
    intro h
    right
    have ⟨K', hIn⟩ := TypeVarInDom.TypeVarInEnvironment_of hIn
    have h' := hIn.weakening_l (Δ:=Δ)
    have eq := unique h h'
    subst K'
    assumption
  . case neg hNotIn =>
    simp_all [TypeVarInDom, TypeVarNotInDom]
    intro hIn
    induction Δ'
    . case empty => simp_all [append]
    . case typeExt Δ' a' K' ih =>
      simp_all [Environment.append]
      specialize @ih (by simp_all [typeVarDom]) (by cases hIn <;> simp_all [typeVarDom])
      cases ih <;> aesop (add norm typeVarDom, safe constructors TypeVarInEnvironment)
    . case termExt Δ' a' T ih =>
      simp_all [Environment.append]
      specialize @ih (by simp_all [typeVarDom]) (by cases hIn; simp_all)
      cases ih <;> aesop (add safe constructors TypeVarInEnvironment)

open Environment in
theorem weakening (h: [[ a: K ∈ Δ, Δ'' ]]) (fresh: ∀a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom): [[ a: K ∈ Δ, Δ', Δ'' ]] := by
  induction Δ' generalizing Δ Δ''
  . case empty => simp_all [empty_append]
  . case typeExt Δ' a' K' ih =>
    specialize @ih Δ [[ (ε , a' : K') , Δ'' ]]
    simp_all [append_type_assoc]
    refine ih ?_ (by aesop (add norm typeVarDom))
    obtain h := h.append_elim
    cases h
    . case inl h =>
      apply weakening_r
      . simp_all
      . by_cases (a = a')
        . case pos eq =>
          -- contradiction
          aesop (add norm typeVarDom, norm TypeVarInDom, safe forward TypeVarInDom_of)
        . case neg neq =>
          constructor <;> simp_all [TypeVarNe]
    . case inr hIn =>
      simp_all [weakening_l]
  . case termExt Δ' x' T ih =>
    specialize @ih Δ [[ (ε , x' : T) , Δ'' ]]
    simp_all [append_term_assoc]
    refine ih ?_ (by aesop (add norm typeVarDom))
    obtain h := h.append_elim
    cases h
    . case inl h =>
      apply weakening_r
      . simp_all
      . constructor; simp_all
    . case inr h =>
      simp_all [weakening_l]

theorem TypeVar_subst: [[ a: K ∈ Δ[A/a'] ]] ↔ [[ a: K ∈ Δ ]] := by
  induction Δ <;>
    aesop (add norm Environment.TypeVar_subst, unsafe cases TypeVarInEnvironment, unsafe constructors TypeVarInEnvironment)

theorem TermVar_drop : [[ a: K ∈ Δ, x: T, Δ' ]] → [[ a: K ∈ Δ, Δ' ]] := by
  induction Δ' <;>
    aesop (add norm Environment.append, unsafe constructors TypeVarInEnvironment, safe cases TypeVarInEnvironment)

theorem TypeVar_drop : [[a : K ∈ Δ, a' : K', Δ']] → a ≠ a' → [[a : K ∈ Δ, Δ']] := by
  induction Δ' <;>
    aesop (add norm Environment.append, unsafe constructors TypeVarInEnvironment, safe cases TypeVarInEnvironment)

end TypeVarInEnvironment

namespace TermVarInEnvironment

theorem eq_of (xTinΔ : [[x : T ∈ Δ]]) : ∃ Δ' Δ'', Δ = [[(Δ', x : T, Δ'')]] := by
  match xTinΔ with
  | .head => exact ⟨_, .empty, rfl⟩
  | .typeVarExt aKinΔ' =>
    rcases aKinΔ'.eq_of with ⟨_, _, rfl⟩
    rw [← Environment.append]
    exact ⟨_, _, rfl⟩
  | .termVarExt aKinΔ' _ =>
    rcases aKinΔ'.eq_of with ⟨_, _, rfl⟩
    rw [← Environment.append]
    exact ⟨_, _, rfl⟩

theorem TermVarInDom_of (xTinΔ : [[x : T ∈ Δ]]) : [[x ∈ dom(Δ)]] :=
  match xTinΔ with
  | .head => .head _
  | .typeVarExt xTinΔ' => xTinΔ'.TermVarInDom_of
  | .termVarExt xTinΔ' xnex' => .tail _ xTinΔ'.TermVarInDom_of

open Environment in
theorem blabla (xninΔ: [[ x ∉ dom(Δ) ]]): ∀T, ¬[[ x : T ∈ Δ ]] := by
  intro T h
  have := h.TermVarInDom_of
  simp_all [TermVarNotInDom]

theorem unique: [[ x: T ∈ Δ ]] → [[ x: T' ∈ Δ ]] → T = T' := by
  intro xTIn xT'In
  induction Δ generalizing x T T'
  . case empty => rcases xTIn
  . case typeExt Δ x_ T_ ih =>
    aesop (add unsafe cases TermVarInEnvironment)
  . case termExt Δ a_ K ih =>
    aesop (add norm TermVarNe, unsafe cases TermVarInEnvironment)

theorem weakening_l : [[ x: T ∈ Δ' ]] → [[ x: T ∈ Δ, Δ' ]] := by
  intro h
  induction Δ' <;> aesop
    (add norm Environment.append,
      unsafe constructors TermVarInEnvironment, safe cases TermVarInEnvironment)

open Environment in
theorem weakening_r (fresh: [[ x ∉ dom(Δ') ]]): [[ x: T ∈ Δ ]] → [[ x: T ∈ Δ, Δ' ]] := by
  intro h
  induction Δ' <;> simp_all [append]
    <;> constructor <;> simp_all [TermVarNotInDom, TermVarInDom, termVarDom, TermVarNe]

open Environment in
theorem append_elim : [[ x: T ∈ Δ, Δ' ]] → ([[ x ∉ dom(Δ') ]] ∧ [[ x: T ∈ Δ ]]) ∨ [[ x: T ∈ Δ' ]] := by
  by_cases ([[ x ∈ dom(Δ') ]])
  . case pos hIn =>
    intro h
    right
    have ⟨T', hIn⟩ := TermVarInDom.TermVarInEnvironment_of hIn
    have h' := hIn.weakening_l (Δ:=Δ)
    have eq := unique h h'
    subst T'
    assumption
  . case neg hNotIn =>
    simp_all [TermVarInDom, TermVarNotInDom]
    intro hIn
    induction Δ'
    . case empty => simp_all [append]
    . case typeExt Δ' a' K' ih =>
      simp_all [Environment.append]
      specialize @ih (by simp_all [termVarDom]) (by cases hIn; simp_all)
      cases ih <;> aesop (add safe constructors TermVarInEnvironment)
    . case termExt Δ' a' T' ih =>
      simp_all [Environment.append]
      specialize @ih (by simp_all [termVarDom]) (by cases hIn <;> simp_all [termVarDom])
      cases ih <;> aesop (add norm termVarDom, safe constructors TermVarInEnvironment)

open Environment in
theorem weakening (h: [[ x: T ∈ Δ, Δ'' ]]) (fresh: ∀x ∈ Δ'.termVarDom, x ∉ Δ.termVarDom): [[ x: T ∈ Δ, Δ', Δ'' ]] := by
  induction Δ' generalizing Δ Δ''
  . case empty => simp_all [empty_append]
  . case typeExt Δ' a' K' ih =>
    specialize @ih Δ [[ (ε , a' : K') , Δ'' ]]
    simp_all [append_type_assoc]
    refine ih ?_ (by aesop (add norm typeVarDom))
    obtain h := h.append_elim
    cases h
    . case inl h =>
      apply weakening_r
      . simp_all
      . constructor; simp_all
    . case inr hIn =>
      simp_all [weakening_l]
  . case termExt Δ' x' T' ih =>
    specialize @ih Δ [[ (ε , x' : T') , Δ'' ]]
    simp_all [append_term_assoc]
    refine ih ?_ (by aesop (add norm termVarDom))
    obtain h := h.append_elim
    cases h
    . case inl h =>
      apply weakening_r
      . simp_all
      . by_cases (x = x')
        . case pos eq =>
          -- contradiction
          aesop (add norm termVarDom, norm TermVarInDom, safe forward TermVarInDom_of)
        . case neg neq =>
          constructor <;> simp_all [TermVarNe]
    . case inr hIn =>
      simp_all [weakening_l]

open Environment in
theorem append_intro_l (xinΔ: [[ x: T ∈ Δ ]]) (xninΔ': ([[ x ∉ dom(Δ') ]])): [[ x: T ∈ Δ, Δ' ]] := by
  induction Δ'
  . case empty => simp_all [append]
  . case typeExt Δ' a K ih =>
    refine .typeVarExt (ih ?_)
    simp_all [TermVarNotInDom, TermVarInDom, termVarDom]
  . case termExt Δ' x' T' ih =>
    refine .termVarExt (ih ?_) ?_
    . simp_all [TermVarNotInDom, TermVarInDom, termVarDom]
    . simp_all [TermVarNotInDom, TermVarInDom, termVarDom, TermVarNe]

open Environment in
theorem append_intro_r (xinΔ': [[ x: T ∈ Δ' ]]): [[ x: T ∈ Δ, Δ' ]] := by
  induction xinΔ' with
  | head => exact .head
  | typeVarExt _ ih => exact .typeVarExt ih
  | termVarExt _ neq ih => exact .termVarExt ih neq

end TermVarInEnvironment

namespace EnvironmentWellFormedness
open Environment in
theorem append_typeVar_fresh_r: [[ ⊢ Δ, Δ' ]] → ∀a ∈ Δ.typeVarDom, a ∉ Δ'.typeVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentWellFormedness, norm typeVarDom, norm typeVarDom_append, norm TypeVarNotInDom, norm TypeVarInDom)

open Environment in
theorem append_typeVar_fresh_l : [[ ⊢ Δ, Δ' ]] → ∀a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentWellFormedness, norm typeVarDom, norm typeVarDom_append, norm TypeVarNotInDom, norm TypeVarInDom)

open Environment in
theorem append_termVar_fresh_r: [[ ⊢ Δ, Δ' ]] → ∀a ∈ Δ.termVarDom, a ∉ Δ'.termVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentWellFormedness, norm termVarDom, norm termVarDom_append, norm TermVarNotInDom, norm TermVarInDom)

open Environment in
theorem append_termVar_fresh_l : [[ ⊢ Δ, Δ' ]] → ∀a ∈ Δ'.termVarDom, a ∉ Δ.termVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentWellFormedness, norm termVarDom, norm termVarDom_append, norm TermVarNotInDom, norm TermVarInDom)

def EnvironmentTypeWellFormedness_of : [[ ⊢ Δ ]] → [[ ⊢τ Δ ]]
  | .empty => .empty
  | .typeVarExt wf anin =>
    .typeVarExt (wf.EnvironmentTypeWellFormedness_of) anin
  | .termVarExt wf _ _ =>
    .termVarExt (wf.EnvironmentTypeWellFormedness_of)

open Environment in
theorem weakening (wf: [[ ⊢ Δ, Δ' ]]): [[ ⊢ Δ ]] := by
  induction Δ'
  . case empty => simp_all [append]
  . case typeExt Δ' a K ih => cases wf; simp_all
  . case termExt Δ' x' T' ih => cases wf; simp_all

end EnvironmentWellFormedness

namespace EnvironmentTypeWellFormedness

open Environment in
theorem TermVar_drop (wf: [[ ⊢τ Δ, x: T, Δ' ]]) : [[ ⊢τ Δ, Δ' ]] := by
  induction Δ'
  . case empty => cases wf; assumption
  . case typeExt Δ' a K ih =>
    cases wf; case typeVarExt wf anin =>
    exact .typeVarExt (ih wf) (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom_append, typeVarDom])
  . case termExt Δ' x' T' ih =>
    cases wf; case termVarExt wf =>
    exact .termVarExt (ih wf)

open Environment in
theorem TypeVar_drop (wf: [[ ⊢τ Δ, a: K, Δ'' ]]) : [[ ⊢τ Δ, Δ'' ]] := by
  induction Δ''
  . case empty => cases wf; assumption
  . case typeExt Δ'' a' K' ih =>
    cases wf; case typeVarExt wf anin =>
    exact .typeVarExt (ih wf) (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom_append, typeVarDom])
  . case termExt Δ'' x' T' ih =>
    cases wf; case termVarExt wf =>
    exact .termVarExt (ih wf)

open Environment in
theorem weakening (wf: [[ ⊢τ Δ, Δ', Δ'' ]]): [[ ⊢τ Δ, Δ'' ]] := by
  induction Δ' generalizing Δ''
  . case empty => simp_all [empty_append]
  . case typeExt Δ' a K ih =>
    rw [<- append_type_assoc] at wf
    specialize ih wf
    rw [append_type_assoc] at ih
    exact ih.TypeVar_drop
  . case termExt Δ' x' T' ih =>
    rw [<- append_term_assoc] at wf
    specialize ih wf
    rw [append_term_assoc] at ih
    exact ih.TermVar_drop

open Environment in
theorem append_typeVar_fresh_r: [[ ⊢τ Δ, Δ' ]] → ∀a ∈ Δ.typeVarDom, a ∉ Δ'.typeVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentTypeWellFormedness, norm typeVarDom, norm typeVarDom_append, norm TypeVarNotInDom, norm TypeVarInDom)

open Environment in
theorem append_typeVar_fresh_l : [[ ⊢τ Δ, Δ' ]] → ∀a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentTypeWellFormedness, norm typeVarDom, norm typeVarDom_append, norm TypeVarNotInDom, norm TypeVarInDom)

end EnvironmentTypeWellFormedness

end TabularTypes.«F⊗⊕ω»
