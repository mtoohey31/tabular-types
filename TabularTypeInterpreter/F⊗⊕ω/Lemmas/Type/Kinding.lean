import Mathlib.Tactic
import TabularTypeInterpreter.Data.Range
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Environment.Basic
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Basic

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace Kinding

theorem TypeVarLocallyClosed_of : [[Δ ⊢ A : K]] → A.TypeVarLocallyClosed 0 := fun Aki =>
  match A, Aki with
  | _, var .. => .var_free
  | .lam K A', .lam A'opki (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'opki a anin |>.TypeVarLocallyClosed_of
    exact .lam <| this.weaken.TypeVar_open_drop <| Nat.lt_succ_self _
  | .app A' B, .app A'opki Bopki =>
    .app A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .forall K A', .scheme A'opki (I := I) => by
    let ⟨a, anin⟩ := I.exists_fresh
    have := A'opki a anin |>.TypeVarLocallyClosed_of
    exact .forall <| this.weaken.TypeVar_open_drop <| Nat.lt_succ_self _
  | .arr A' B, .arr A'opki Bopki =>
    .arr A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .list A', Aki =>
    let .list A'opki (A := A'') := Aki
    .list fun A''' A'''in => by
      let ⟨i, mem, A'''eq⟩ := Std.Range.mem_of_mem_map A'''in
      cases A'''eq
      exact A'opki i mem |>.TypeVarLocallyClosed_of
  | .listApp A' B, .listApp A'opki Bopki =>
    .listApp A'opki.TypeVarLocallyClosed_of Bopki.TypeVarLocallyClosed_of
  | .prod A', .prod A'opki => .prod A'opki.TypeVarLocallyClosed_of
  | .sum A', .sum A'opki => .sum A'opki.TypeVarLocallyClosed_of
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  exact List.sizeOf_lt_of_mem A'''in

theorem not_mem_freeTypeVars_of (Aki : [[Δ ⊢ A : K]]) (aninΔ : [[a ∉ dom(Δ)]])
  : a ∉ A.freeTypeVars := by match Aki with
  | .var a'inΔ =>
    rw [Type.freeTypeVars]
    apply List.not_mem_singleton.mpr
    intro aeqa'
    cases aeqa'
    nomatch aninΔ a'inΔ.TypeVarInDom_of
  | .lam I A'opki | .scheme I A'opki =>
    let ⟨a', a'nin⟩ := a :: I |>.exists_fresh
    let ⟨a'nea, a'ninI⟩ := List.not_mem_cons.mp a'nin
    rw [Type.freeTypeVars]
    exact Type.not_mem_freeTypeVars_TypeVar_open_drop <|
      A'opki a' a'ninI |>.not_mem_freeTypeVars_of (List.not_mem_cons.mpr ⟨a'nea.symm, aninΔ⟩)
  | .app A'ki Bki | .arr A'ki Bki | .listApp A'ki Bki =>

    rw [Type.freeTypeVars]
    exact List.not_mem_append'.mpr ⟨
      A'ki.not_mem_freeTypeVars_of aninΔ,
      Bki.not_mem_freeTypeVars_of aninΔ
    ⟩
  | .list Aski =>
    rw [Type.freeTypeVars, List.mapMem_eq_map, List.map_map]
    apply List.not_mem_flatten.mpr
    intro as mem
    let ⟨i, mem', eq⟩ := Std.Range.mem_of_mem_map mem
    cases eq
    exact Aski i mem' |>.not_mem_freeTypeVars_of aninΔ
  | .prod A'ki | .sum A'ki =>
    rw [Type.freeTypeVars]
    exact A'ki.not_mem_freeTypeVars_of aninΔ
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  apply Nat.le_of_lt
  exact List.sizeOf_lt_of_mem <| Std.Range.mem_map_of_mem mem'

open Environment TypeVarInEnvironment in
theorem weakening_r' (kT: [[ Δ, Δ'' ⊢ T: K ]]) (fresh: ∀ a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom): [[ Δ, Δ', Δ'' ⊢ T: K ]] := by
  generalize Δ_eq: Δ.append Δ'' = Δ_ at kT
  induction kT generalizing Δ Δ' Δ''
  case var a K Δ_ hIn =>
    subst Δ_
    exact .var <| hIn.weakening fresh
  case lam Δ_ K1 T K2 I kT ih =>
    subst Δ_
    apply Kinding.lam (I := I ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom)
    intro a notIn
    specialize @ih a (by simp_all) Δ (Δ''.typeExt a K1)
    simp_all [append]
  case scheme Δ_ K1 T K2 I kT ih =>
    subst Δ_
    have ⟨a, notIn⟩ := (I ++ T.freeTypeVars ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom).exists_fresh
    apply Kinding.scheme (I := I ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom)
    intro a notIn
    specialize @ih a (by simp_all) Δ (Δ''.typeExt a K1)
    simp_all [append]
  all_goals aesop (add safe constructors Kinding) (config := { enableSimp := false })


theorem weakening_r (kT: [[ Δ ⊢ T: K ]]) (fresh: ∀ a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom): [[ Δ, Δ' ⊢ T: K ]] := by
  apply Kinding.weakening_r' (Δ'' := Environment.empty) <;> simp_all [Environment.append]

theorem weakening : [[Δ, Δ'' ⊢ A : K]] → [[⊢ Δ, Δ', Δ'']] → [[Δ, Δ', Δ'' ⊢ A : K]] :=
  λ h wf => .weakening_r' h <| Environment.append_assoc.subst wf |>.weakening.append_typeVar_fresh_l

open Environment TypeVarInEnvironment in
theorem TermVar_drop (kT: [[ Δ, x: T', Δ'' ⊢ T: K ]]): [[ Δ, Δ'' ⊢ T: K ]] := by
  generalize Δ_eq: [[ (Δ, x: T', Δ'') ]] = Δ_ at kT
  induction kT generalizing Δ Δ'' x T'
  case var a K Δ_ hIn =>
    subst Δ_
    exact .var hIn.TermVar_drop
  case lam Δ_ K1 T K2 I kT ih =>
    subst Δ_
    apply Kinding.lam (I := I ++ Δ.typeVarDom ++ Δ''.typeVarDom)
    intro a notIn
    specialize @ih a (by simp_all) Δ x T' (Δ''.typeExt a K1)
    simp_all [append]
  case scheme Δ_ K1 T K2 I kT ih =>
    subst Δ_
    have ⟨a, notIn⟩ := (I ++ T.freeTypeVars ++ Δ.typeVarDom ++ Δ''.typeVarDom).exists_fresh
    apply Kinding.scheme (I := I ++ Δ.typeVarDom ++ Δ''.typeVarDom)
    intro a notIn
    specialize @ih a (by simp_all) Δ x T' (Δ''.typeExt a K1)
    simp_all [append]
  all_goals aesop (add safe constructors Kinding) (config := { enableSimp := false })

open «Type» in
theorem TypeVar_drop_of_not_mem_freeTypeVars (Aki : [[Δ, a : K, Δ' ⊢ A : K']])
  (aninA : a ∉ A.freeTypeVars) : [[Δ, Δ' ⊢ A : K']] := by
  match Aki with
  | var aK'in =>
    rw [freeTypeVars] at aninA
    exact var <| aK'in.TypeVar_drop <| Ne.symm <| List.not_mem_singleton.mp aninA
  | lam I A'ki =>
    apply lam <| a :: I
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'ki a' a'ninI
    rw [← Environment.append] at A'ki ⊢
    rw [freeTypeVars] at aninA
    exact TypeVar_drop_of_not_mem_freeTypeVars A'ki <|
      not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  | app A'ki Bki =>
    rw [freeTypeVars] at aninA
    let ⟨aninA', aninB⟩ := List.not_mem_append'.mp aninA
    exact app (TypeVar_drop_of_not_mem_freeTypeVars A'ki aninA')
      (TypeVar_drop_of_not_mem_freeTypeVars Bki aninB)
  | scheme I A'ki =>
    apply scheme <| a :: I
    intro a' a'nin
    let ⟨ane, a'ninI⟩ := List.not_mem_cons.mp a'nin
    specialize A'ki a' a'ninI
    rw [← Environment.append] at A'ki ⊢
    rw [freeTypeVars] at aninA
    exact TypeVar_drop_of_not_mem_freeTypeVars A'ki <|
      not_mem_freeTypeVars_TypeVar_open_intro aninA ane.symm
  | arr A'ki Bki =>
    rw [freeTypeVars] at aninA
    let ⟨aninA', aninB⟩ := List.not_mem_append'.mp aninA
    exact arr (TypeVar_drop_of_not_mem_freeTypeVars A'ki aninA')
      (TypeVar_drop_of_not_mem_freeTypeVars Bki aninB)
  | list A'ki (A := A') =>
    rw [freeTypeVars, List.mapMem_eq_map] at aninA
    apply list
    intro i mem
    apply TypeVar_drop_of_not_mem_freeTypeVars <| A'ki i mem
    apply List.not_mem_flatten.mp aninA
    rw [List.map_map, ← Std.Range.map]
    exact Std.Range.mem_map_of_mem mem
  | listApp A'ki Bki =>
    rw [freeTypeVars] at aninA
    let ⟨aninA', aninB⟩ := List.not_mem_append'.mp aninA
    exact listApp (TypeVar_drop_of_not_mem_freeTypeVars A'ki aninA')
      (TypeVar_drop_of_not_mem_freeTypeVars Bki aninB)
  | prod A'ki =>
    rw [freeTypeVars] at aninA
    exact prod <| TypeVar_drop_of_not_mem_freeTypeVars A'ki aninA
  | sum A'ki =>
    rw [freeTypeVars] at aninA
    exact sum <| TypeVar_drop_of_not_mem_freeTypeVars A'ki aninA
termination_by sizeOf A
decreasing_by
  all_goals simp_arith
  exact Nat.le_of_lt <| List.sizeOf_lt_of_mem <| Std.Range.mem_map_of_mem mem

-- NOTE we could use a weaker wf: wfτ
theorem substAux (kT: [[ Δ, a: K, Δ' ⊢ T: K' ]]) (h1: a ∉ Δ'.typeVarDom) (h2: ∀a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom) (kA: [[ Δ ⊢ A: K ]]): [[ (Δ , Δ'[A/a]) ⊢ T[A/a] : K' ]] := by
  generalize Δ'eq: (Δ.typeExt a K).append Δ' = Δ_ at kT
  induction kT generalizing Δ' a <;> simp_all [Type.TypeVar_subst]
  case var a' K' Δ_ kIn =>
    subst Δ_
    by_cases (a = a')
    . case pos eq =>
      simp_all
      subst a'
      -- 1. by wf we know a ∉ Δ'.typeVarDom
      -- have fresh := wf.append_typeVar_fresh_r a (by constructor)
      -- 2. then by uniqueness we know from kIn that K' = K
      have eq := kIn.unique (K':=K) (by
        apply TypeVarInEnvironment.weakening_r h1
        constructor
      )
      subst K'
      -- 3. then wts Δ, Δ'[S] ⊢ A: K, by weakening kA we are done
      apply weakening_r
      . case kT => assumption
      . case fresh =>
        simp_all [Environment.typeVarDom_TypeVar_subst, Environment.typeVarDom]
    . case neg neq =>
      simp_all
      -- 1. by kIn we know a': K' is either in (Δ, a: K) or Δ'
      apply TypeVarInEnvironment.append_elim at kIn
      refine .var ?_
      cases kIn
      . case inl kIn =>
        -- 2a. If a': K' ∈ Δ, a: K, we also know that a': K' ∉ dom(Δ')
        obtain ⟨notInΔ', kIn⟩ := kIn
        -- 3a. and by a ≠ a' we know a': K' ∈ Δ.
        --     wts. a': K' ∈ Δ, Δ'[S], by weakening and subst_noop we are done
        apply TypeVarInEnvironment.weakening_r
        . simp_all [Environment.typeVarDom_TypeVar_subst, Environment.TypeVarNotInDom, Environment.TypeVarInDom, Environment.typeVarDom]
        . cases kIn <;> simp_all
      . case inr kIn =>
        -- 2b. If a': K' ∈ Δ', similarly by weakening and subst_noop we are done
        apply TypeVarInEnvironment.weakening_l
        simp_all [TypeVarInEnvironment.TypeVar_subst]
  case lam Δ_ K1 T K2 I kind ih =>
    subst Δ_
    refine .lam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom) (λ a' notIn => ?_)
    rw [<- kA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (by aesop)]
    refine ih a' (by simp_all) ?_ ?_ (by rw [Environment.append_typeExt_assoc])
    . aesop (add simp [Environment.typeVarDom])
    . simp_all [Environment.typeVarDom]
  case scheme Δ_ K1 T K2 I kind ih =>
    subst Δ_
    refine .scheme (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom) (λ a' notIn => ?_)
    rw [<- kA.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (by aesop)]
    refine ih a' (by simp_all) ?_ ?_ (by rw [Environment.append_typeExt_assoc])
    . aesop (add simp [Environment.typeVarDom])
    . simp_all [Environment.typeVarDom]
  case list n Δ_ T_i K_i kind ih =>
    subst Δ_
    constructor
    simp_all
  all_goals aesop (add safe constructors Kinding) (config := { enableSimp := false })

theorem subst' (kT: [[ Δ, a: K, Δ' ⊢ T: K' ]]) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kA: [[ Δ ⊢ A: K ]]): [[ (Δ , Δ'[A/a]) ⊢ T[A/a] : K' ]] := by
  refine substAux kT ?_ ?_ kA
  . exact wf.append_typeVar_fresh_r a (by constructor)
  . have := wf.append_typeVar_fresh_l
    simp_all [Environment.typeVarDom]

theorem subst (kT: [[ Δ, a: K ⊢ T: K' ]]) (wf: [[ ⊢ Δ, a: K ]]) (kA: [[ Δ ⊢ A: K ]]): [[ Δ ⊢ T[A/a]: K' ]] :=
 by apply subst' (Δ' := Environment.empty) <;> assumption

theorem Type_open_preservation' {A : «Type»}
  (Aki : Kinding [[(Δ, a : K, Δ')]] (A.TypeVar_open a n) K') (h1: a ∉ Δ'.typeVarDom) (h2: ∀a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom) (aninfvA : a ∉ A.freeTypeVars)
  (Bki : [[Δ ⊢ B : K]]) : Kinding [[(Δ, (Δ' [B / a]))]] (A.Type_open B n) K' := by
  rw [← Type.TypeVar_subst_intro_of_not_mem_freeTypeVars aninfvA]
  exact Aki.substAux h1 h2 Bki

theorem Type_open_preservation {A : «Type»}
  (Aki : Kinding [[(Δ, a : K)]] (A.TypeVar_open a n) K') (aninfvA : a ∉ A.freeTypeVars)
  (Bki : [[Δ ⊢ B : K]]) : Kinding Δ (A.Type_open B n) K' := Type_open_preservation' (Δ' := [[ ε ]]) Aki (by simp_all [Environment.typeVarDom]) nofun aninfvA Bki

end Kinding

namespace EnvironmentWellFormedness

open Environment in
theorem TermVar_drop (wf: [[ ⊢ Δ, x: T, Δ' ]]) : [[ ⊢ Δ, Δ' ]] := by
  induction Δ'
  . case empty => simp_all [append]; cases wf; assumption
  . case typeExt Δ' a K ih =>
    cases wf; case typeVarExt wf anin =>
    exact .typeVarExt (ih wf) (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom_append, typeVarDom])
  . case termExt Δ' x' T' ih =>
    cases wf; case termVarExt wf x'nin T'kiStar =>
    exact .termVarExt
      (ih wf)
      (by simp_all [TermVarNotInDom, TermVarInDom, termVarDom_append, termVarDom])
      T'kiStar.TermVar_drop

open Environment in
theorem TypeVar_subst (wf: [[ ⊢ Δ, a: K, Δ' ]]) (BkiK: [[ Δ ⊢ B: K ]]) : [[ ⊢ Δ, Δ'[B/a] ]] := by
  induction Δ' <;> simp_all [Environment.TypeVar_subst]
  . case empty => cases wf; assumption
  . case typeExt Δ' a' K' ih =>
    cases wf; case typeVarExt wf a'nin =>
    refine .typeVarExt (ih wf) ?_
    simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom_append, typeVarDom]
    obtain ⟨a'nin, _, _⟩ := a'nin
    clear * - a'nin
    induction Δ' <;> simp_all [TypeVar_subst, typeVarDom]
  . case termExt Δ' x T ih =>
    cases wf; case termVarExt wf xnin TkiStar =>
    refine .termVarExt (ih wf) ?_ (TkiStar.subst' wf BkiK)
    simp_all [TermVarNotInDom, TermVarInDom, termVarDom_append, termVarDom]
    obtain ⟨xnin, _⟩ := xnin
    clear * - xnin
    induction Δ' <;> simp_all [TypeVar_subst, termVarDom]

open Environment in
theorem strengthen_type (wf: [[ ⊢ Δ, Δ' ]]) (fresh: a ∉ Δ.typeVarDom ++ Δ'.typeVarDom): [[ ⊢ Δ, a: K, Δ' ]] := by
  induction Δ'
  . case empty =>
    simp_all [append]
    exact wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom])
  . case typeExt Δ' a' K' ih =>
    cases wf; case typeVarExt wf anin =>
    refine .typeVarExt ?_ ?_
    . simp_all [typeVarDom]
    . aesop (add simp [TypeVarNotInDom, TypeVarInDom, typeVarDom_append, typeVarDom])
  . case termExt Δ' x' T' ih =>
    cases wf; case termVarExt T'kiStar =>
    refine .termVarExt ?_ ?_ ?_
    . simp_all [typeVarDom]
    . aesop (add simp [TermVarNotInDom, TermVarInDom, termVarDom_append])
    . rw [← append_type_assoc]
      refine T'kiStar.weakening_r' ?_
      simp_all [typeVarDom]

end EnvironmentWellFormedness

namespace Kinding

open «Type» Environment in
theorem freeTypeVars_in_Δ (AkiK: [[ Δ ⊢ A: K ]]) (ainA: a ∈ A.freeTypeVars): a ∈ Δ.typeVarDom := by
  induction AkiK <;> try aesop (add simp [typeVarDom, freeTypeVars]); done
  . case var a' K' Δ a'in =>
    have := a'in.TypeVarInDom_of
    simp_all [freeTypeVars, TypeVarInDom]
  . case lam Δ K1 A K2 I AkiK2 ih =>
    have ⟨a', a'nin⟩ := (a :: I).exists_fresh
    simp_all [freeTypeVars]
    specialize AkiK2 a' (by simp_all)
    specialize ih a' (by simp_all) (Type.freeTypeVars_TypeVar_open ainA)
    aesop (add simp typeVarDom)
  . case scheme Δ K1 A K2 I AkiK2 ih =>
    have ⟨a', a'nin⟩ := (a :: I).exists_fresh
    simp_all [freeTypeVars]
    specialize AkiK2 a' (by simp_all)
    specialize ih a' (by simp_all) (Type.freeTypeVars_TypeVar_open ainA)
    aesop (add simp typeVarDom)
  . case list n Δ A K AkiK ih =>
    simp_all [freeTypeVars]
    obtain ⟨i, iRange, ainA⟩ := ainA
    exact ih i (Std.Range.mem_of_mem_toList iRange) ainA

end Kinding

namespace TermVarInEnvironment

open Environment in
theorem freeTypeVars_in_Δ
  (xAinΔ: [[x : A ∈ Δ]]) (wf: [[ ⊢ Δ ]]) a (anin: a ∈ A.freeTypeVars) : a ∈ Δ.typeVarDom := by
  induction wf
  . case empty => cases xAinΔ
  . case typeVarExt Δ a' K' wf a'nin ih =>
    cases xAinΔ; case typeVarExt xAinΔ =>
    specialize ih xAinΔ
    simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom]
  . case termVarExt Δ x' A' wf x'nin A'kiStar ih =>
    by_cases (x = x')
    . case pos eq =>
      subst x'
      have := xAinΔ.unique .head; subst A'
      simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom]
      exact A'kiStar.freeTypeVars_in_Δ anin
    . case neg neq =>
      specialize ih (by cases xAinΔ <;> simp_all)
      simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom]

end TermVarInEnvironment

namespace Kinding

theorem inv_list (k: [[ Δ ⊢ { </ A@i // i in [:n] /> } : L K ]]): ∀i ∈ [0:n], [[ Δ ⊢ A@i : K ]] := by
  generalize Teq : (Type.list ([0:n].map fun i => A i)) = T at k
  cases k <;> simp_all
  . case list n_ A_ k =>
    have neq: n = n_ := by
      apply congrArg (f:= List.length) at Teq
      simp_all [List.length_map, Std.Range.length_toList]
    simp_all [Std.Range.mem_toList_of_mem]


theorem inv_list' (k: [[ Δ ⊢ { </ A@i // i in [:n] /> } : K ]]): ∃ K', K = Kind.list K' ∧ ∀i ∈ [0:n], [[ Δ ⊢ A@i : K' ]] := by
  generalize Teq : (Type.list ([0:n].map fun i => A i)) = T at k
  cases k <;> simp_all
  . case list n_ A_ K_ k =>
    have neq: n = n_ := by
      apply congrArg (f:= List.length) at Teq
      simp_all [List.length_map, Std.Range.length_toList]
    simp_all [Std.Range.mem_toList_of_mem]

theorem singleton_list (Aki : [[Δ ⊢ A : K]]) : [[Δ ⊢ {A} : L K]] := by
  have := list (Δ := Δ) (A := fun _ => A) (K := K) (n := 1) <| by
    intro i mem
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    simp only
    exact Aki
  rw [Std.Range.map, Std.Range.toList, if_pos Nat.zero_lt_one, Std.Range.toList] at this
  exact this

theorem empty_list : [[Δ ⊢ { } : L K]] := by
  have := list (Δ := Δ) (A := fun _ => .list []) (K := K) (n := 0) (fun _ => nomatch ·)
  rw [Std.Range.map, Std.Range.toList, if_neg (Nat.not_lt_of_le (Nat.le_refl _))] at this
  exact this

theorem unit : [[Δ ⊢ ⊗ { } : *]] := prod empty_list

theorem never : [[Δ ⊢ ⊕ { } : *]] := sum empty_list

theorem prj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp [«Type».TypeVar_open]
  apply arr
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₀ki.weakening (Δwf.typeVarExt anin) (Δ' := .typeExt .empty a _) (Δ'' := .empty)

theorem inj_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply sum
    apply listApp
    · exact var .head
    · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem concat_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  (A₂ki : [[Δ ⊢ A₂ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧) : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp only [«Type».TypeVar_open]
  apply arr
  · apply prod
    apply listApp
    · exact var .head
    · rw [A₀ki.TypeVarLocallyClosed_of.TypeVar_open_id]
      exact A₀ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
  · apply arr
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₁ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        exact A₁ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin
    · apply prod
      apply listApp
      · exact var .head
      · rw [A₂ki.TypeVarLocallyClosed_of.TypeVar_open_id]
        exact A₂ki.weakening (Δ' := .typeExt .empty a _) (Δ'' := .empty) <| Δwf.typeVarExt anin

theorem elim_evidence (Δwf : [[⊢ Δ]]) (A₀ki : [[Δ ⊢ A₀ : L K]]) (A₁ki : [[Δ ⊢ A₁ : L K]])
  (A₂ki : [[Δ ⊢ A₂ : L K]])
  : [[Δ ⊢ ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0 : *]] := by
  apply scheme (I := Δ.typeVarDom)
  intro a anin
  simp [«Type».TypeVar_open]
  apply scheme (I := a :: Δ.typeVarDom)
  intro aₜ aₜnin
  let aₜnea := List.ne_of_not_mem_cons aₜnin
  simp [«Type».TypeVar_open]
  apply arr
  · apply arr
    · apply sum
      apply listApp
      · exact var <| .typeVarExt .head aₜnea.symm
      · let A₀lc := A₀ki.TypeVarLocallyClosed_of
        rw [A₀lc.weaken (n := 1) |>.TypeVar_open_id, A₀lc.TypeVar_open_id]
        exact A₀ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
          Δwf.typeVarExt anin |>.typeVarExt aₜnin
    · exact var .head
  · apply arr
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₁lc := A₁ki.TypeVarLocallyClosed_of
          rw [A₁lc.weaken (n := 1) |>.TypeVar_open_id, A₁lc.TypeVar_open_id]
          exact A₁ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
            Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head
    · apply arr
      · apply sum
        apply listApp
        · exact var <| .typeVarExt .head aₜnea.symm
        · let A₂lc := A₂ki.TypeVarLocallyClosed_of
          rw [A₂lc.weaken (n := 1) |>.TypeVar_open_id, A₂lc.TypeVar_open_id]
          exact A₂ki.weakening (Δ' := .typeExt (.typeExt .empty a _) aₜ _) (Δ'' := .empty) <|
            Δwf.typeVarExt anin |>.typeVarExt aₜnin
      · exact var .head

theorem ind_step (Δwf : [[⊢ Δ]]) (aₘinΔ : [[aₘ : (L K) ↦ * ∈ Δ]])
  (Bₗki : ∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀,
    [[Δ, aₗ : *, aₜ : K, aₚ : L K, aᵢ : L K, aₙ : L K ⊢ Bₗ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1^aₙ : *]])
  (Bᵣki : ∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, [[Δ, aᵢ : L K, aₙ : L K ⊢ Bᵣ^aᵢ#1^aₙ : *]])
  : [[Δ ⊢ ∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bₗ → Bᵣ → (⊗ { }) → (aₘ aₚ$2) → aₘ aᵢ$1 : *]] := by
  let ⟨aₗ, aₗnin⟩ := I₀.exists_fresh
  let ⟨aₜ, aₜnin⟩ := aₗ :: I₀ |>.exists_fresh
  let ⟨aₚ, aₚnin⟩ := aₜ :: aₗ :: I₀ |>.exists_fresh
  let ⟨aᵢ, aᵢnin⟩ := aₚ :: aₜ :: aₗ :: I₀ |>.exists_fresh
  let ⟨aₙ, aₙnin⟩ := aᵢ :: aₚ :: aₜ :: aₗ :: I₀ |>.exists_fresh
  let Bₗlc := Bₗki _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin
    |>.TypeVarLocallyClosed_of.weaken (n := 5)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.base _)
  let ⟨aᵢ, aᵢnin⟩ := I₁ |>.exists_fresh
  let ⟨aₙ, aₙnin⟩ := aᵢ :: I₁ |>.exists_fresh
  let Bᵣlc := Bᵣki _ aᵢnin _ aₙnin |>.TypeVarLocallyClosed_of.weaken (n := 2)
    |>.TypeVar_open_drop (Nat.lt.step <| .base _) |>.TypeVar_open_drop (Nat.lt.base _)
  apply scheme <| I₀ ++ Δ.typeVarDom
  intro aₗ aₗnin
  let ⟨aₗninI₀, aₗninΔ⟩ := List.not_mem_append'.mp aₗnin
  let Δaₗwf := Δwf.typeVarExt aₗninΔ (K := .star)
  let aₘneaₗ := ne_of_mem_of_not_mem aₘinΔ.TypeVarInDom_of aₗninΔ
  simp [Type.TypeVar_open]
  rw [Bᵣlc.weaken (n := 2).TypeVar_open_id]
  apply scheme <| aₗ :: I₀ ++ aₗ :: Δ.typeVarDom
  intro aₜ aₜnin
  let ⟨aₜninI₀, aₜninΔ⟩ := List.not_mem_append'.mp aₜnin
  let Δaₗaₜwf := Δaₗwf.typeVarExt aₜninΔ (K := K)
  let aₗneaₜ := List.ne_of_not_mem_cons aₜninI₀
  let aₘneaₜ := ne_of_mem_of_not_mem aₘinΔ.TypeVarInDom_of <| List.not_mem_of_not_mem_cons aₜninΔ
  simp [Type.TypeVar_open]
  rw [Bᵣlc.weaken (n := 1).TypeVar_open_id]
  apply scheme <| aₜ :: aₗ :: I₀ ++ aₜ :: aₗ :: Δ.typeVarDom
  intro aₚ aₚnin
  let ⟨aₚninI₀, aₚninΔ⟩ := List.not_mem_append'.mp aₚnin
  let Δaₗaₜaₚwf := Δaₗaₜwf.typeVarExt aₚninΔ (K := K.list)
  let aₗneaₚ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₚninI₀
  let aₘneaₚ := ne_of_mem_of_not_mem aₘinΔ.TypeVarInDom_of <| List.not_mem_of_not_mem_cons <|
    List.not_mem_of_not_mem_cons <| aₚninΔ
  symm at aₗneaₚ
  simp [Type.TypeVar_open]
  rw [Bᵣlc.TypeVar_open_id]
  apply scheme <| aₚ :: aₜ :: aₗ :: I₀ ++ I₁ ++ aₚ :: aₜ :: aₗ :: Δ.typeVarDom
  intro aᵢ aᵢnin
  let ⟨aᵢninI₀I₁, aᵢninΔ⟩ := List.not_mem_append'.mp aᵢnin
  let ⟨aᵢninI₀, aᵢninI₁⟩ := List.not_mem_append'.mp aᵢninI₀I₁
  let aₚneaᵢ := List.ne_of_not_mem_cons aᵢninI₀
  let Δaₗaₜaₚaᵢwf := Δaₗaₜaₚwf.typeVarExt aᵢninΔ (K := K.list)
  let aₗneaᵢ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
    List.not_mem_of_not_mem_cons <| aᵢninI₀
  let aₘneaᵢ := ne_of_mem_of_not_mem aₘinΔ.TypeVarInDom_of <| List.not_mem_of_not_mem_cons <|
    List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aᵢninΔ
  symm at aₚneaᵢ aₗneaᵢ
  simp [Type.TypeVar_open]
  apply scheme <| aᵢ :: aₚ :: aₜ :: aₗ :: I₀ ++ aᵢ :: I₁ ++ aᵢ :: aₚ :: aₜ :: aₗ :: Δ.typeVarDom
  intro aₙ aₙnin
  let ⟨aₙninI₀I₁, aₙninΔ⟩ := List.not_mem_append'.mp aₙnin
  let ⟨aₙninI₀, aₙninI₁⟩ := List.not_mem_append'.mp aₙninI₀I₁
  let Δaₗaₜaₚaᵢaₙwf := Δaₗaₜaₚaᵢwf.typeVarExt aₙninΔ (K := K.list)
  let aₚneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons aₙninI₀
  let aₗneaₙ := List.ne_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
    List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons <| aₙninI₀
  let aₘneaₙ := ne_of_mem_of_not_mem aₘinΔ.TypeVarInDom_of <| List.not_mem_of_not_mem_cons <|
    List.not_mem_of_not_mem_cons <| List.not_mem_of_not_mem_cons <|
    List.not_mem_of_not_mem_cons <| aₙninΔ
  let aᵢneaₙ := List.ne_of_not_mem_cons aₙninI₀
  symm at aᵢneaₙ aₚneaₙ aₗneaₙ
  simp [Type.TypeVar_open]
  apply arr <| Bₗki _ aₗninI₀ _ aₜninI₀ _ aₚninI₀ _ aᵢninI₀ _ aₙninI₀
  apply arr <| Bᵣki _ aᵢninI₁ _ aₙninI₁ |>.weakening Δaₗaₜaₚaᵢaₙwf
    (Δ := Δ)
    (Δ' := .typeExt (.typeExt (.typeExt .empty ..) ..) ..)
    (Δ'' := .typeExt (.typeExt .empty ..) ..)
  · apply arr .unit
    apply arr
    · apply app
      · exact var <| aₘinΔ.typeVarExt aₘneaₗ |>.typeVarExt aₘneaₜ |>.typeVarExt aₘneaₚ
          |>.typeVarExt aₘneaᵢ |>.typeVarExt aₘneaₙ
      · exact var <| .typeVarExt (.typeVarExt .head aₚneaᵢ) aₚneaₙ
    · apply app
      · exact var <| aₘinΔ.typeVarExt aₘneaₗ |>.typeVarExt aₘneaₜ |>.typeVarExt aₘneaₚ
          |>.typeVarExt aₘneaᵢ |>.typeVarExt aₘneaₙ
      · exact var <| .typeVarExt .head aᵢneaₙ

local instance : Inhabited «Type» where
  default := .list []
in
theorem ind_evidence (Δwf : [[⊢ Δ]]) (Aki : [[Δ ⊢ A : L K]])
  (Bₗki : ∀ aₗ ∉ I₀, ∀ aₜ ∉ aₗ :: I₀, ∀ aₚ ∉ aₜ :: aₗ :: I₀, ∀ aᵢ ∉ aₚ :: aₜ :: aₗ :: I₀, ∀ aₙ ∉ aᵢ :: aₚ :: aₜ :: aₗ :: I₀,
    [[Δ, aₗ : *, aₜ : K, aₚ : L K, aᵢ : L K, aₙ : L K ⊢ Bₗ^aₗ#4^aₜ#3^aₚ#2^aᵢ#1^aₙ : *]])
  (Bᵣki : ∀ aᵢ ∉ I₁, ∀ aₙ ∉ aᵢ :: I₁, [[Δ, aᵢ : L K, aₙ : L K ⊢ Bᵣ^aᵢ#1^aₙ : *]])
  : [[Δ ⊢ ∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bₗ → Bᵣ → (⊗ { }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1) → (aₘ$0 { }) → aₘ$0 A : *]] := by
  apply scheme Δ.typeVarDom
  intro aₘ aₘnin
  let Δaₘwf := Δwf.typeVarExt aₘnin (K := K.list.arr .star)
  simp [Type.TypeVar_open]
  let ⟨aₗ, aₗnin⟩ := I₀.exists_fresh
  let ⟨aₜ, aₜnin⟩ := aₗ :: I₀ |>.exists_fresh
  let ⟨aₚ, aₚnin⟩ := aₜ :: aₗ :: I₀ |>.exists_fresh
  let ⟨aᵢ, aᵢnin⟩ := aₚ :: aₜ :: aₗ :: I₀ |>.exists_fresh
  let ⟨aₙ, aₙnin⟩ := aᵢ :: aₚ :: aₜ :: aₗ :: I₀ |>.exists_fresh
  let Bₗlc := Bₗki _ aₗnin _ aₜnin _ aₚnin _ aᵢnin _ aₙnin
    |>.TypeVarLocallyClosed_of.weaken (n := 5)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.step <| .base _)
    |>.TypeVar_open_drop (Nat.lt.base _)
  let ⟨aᵢ, aᵢnin⟩ := I₁ |>.exists_fresh
  let ⟨aₙ, aₙnin⟩ := aᵢ :: I₁ |>.exists_fresh
  let Bᵣlc := Bᵣki _ aᵢnin _ aₙnin |>.TypeVarLocallyClosed_of.weaken (n := 2)
    |>.TypeVar_open_drop (Nat.lt.step <| .base _) |>.TypeVar_open_drop (Nat.lt.base _)
  rw [Aki.TypeVarLocallyClosed_of.TypeVar_open_id, Bₗlc.TypeVar_open_id,
      Bᵣlc.weaken (n := 3).TypeVar_open_id]
  apply arr
  · apply ind_step Δaₘwf .head (I₀ := I₀ ++ aₘ :: Δ.typeVarDom) (I₁ := I₁ ++ aₘ :: Δ.typeVarDom)
    · intro aₗ aₗnin
      let ⟨aₗninI, aₗninΔ⟩ := List.not_mem_append'.mp aₗnin
      intro aₜ aₜnin
      let ⟨aₜneaₗ, aₜnin'⟩ := List.not_mem_cons.mp aₜnin
      let ⟨aₜninI, aₜninΔ⟩ := List.not_mem_append'.mp aₜnin'
      let aₜninI := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninI⟩
      let aₜninΔ := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninΔ⟩
      intro aₚ aₚnin
      let ⟨aₚneaₜ, aₚnin'⟩ := List.not_mem_cons.mp aₚnin
      let ⟨aₚneaₗ, aₚnin''⟩ := List.not_mem_cons.mp aₚnin'
      let ⟨aₚninI, aₚninΔ⟩ := List.not_mem_append'.mp aₚnin''
      let aₚninI := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninI⟩⟩
      let aₚninΔ := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninΔ⟩⟩
      intro aᵢ aᵢnin
      let ⟨aᵢneaₚ, aᵢnin'⟩ := List.not_mem_cons.mp aᵢnin
      let ⟨aᵢneaₜ, aᵢnin''⟩ := List.not_mem_cons.mp aᵢnin'
      let ⟨aᵢneaₗ, aᵢnin'''⟩ := List.not_mem_cons.mp aᵢnin''
      let ⟨aᵢninI, aᵢninΔ⟩ := List.not_mem_append'.mp aᵢnin'''
      let aᵢninI := List.not_mem_cons.mpr
        ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninI⟩⟩⟩
      let aᵢninΔ := List.not_mem_cons.mpr
        ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninΔ⟩⟩⟩
      intro aₙ aₙnin
      let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
      let ⟨aₙneaₚ, aₙnin''⟩ := List.not_mem_cons.mp aₙnin'
      let ⟨aₙneaₜ, aₙnin'''⟩ := List.not_mem_cons.mp aₙnin''
      let ⟨aₙneaₗ, aₙnin''''⟩ := List.not_mem_cons.mp aₙnin'''
      let ⟨aₙninI, aₙninΔ⟩ := List.not_mem_append'.mp aₙnin''''
      let aₙninI := List.not_mem_cons.mpr ⟨
        aₙneaᵢ,
        List.not_mem_cons.mpr
          ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninI⟩⟩⟩
      ⟩
      let aₙninΔ := List.not_mem_cons.mpr ⟨
        aₙneaᵢ,
        List.not_mem_cons.mpr
          ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninΔ⟩⟩⟩
      ⟩
      let Δaₘaₗaₜaₚaᵢaₙwf := Δaₘwf.typeVarExt aₗninΔ (K := .star) |>.typeVarExt aₜninΔ (K := K)
        |>.typeVarExt aₚninΔ (K := K.list) |>.typeVarExt aᵢninΔ (K := K.list)
        |>.typeVarExt aₙninΔ (K := K.list)
      exact Bₗki _ aₗninI _ aₜninI _ aₚninI _ aᵢninI _ aₙninI |>.weakening Δaₘaₗaₜaₚaᵢaₙwf
        (Δ' := .typeExt .empty ..)
        (Δ'' := .typeExt (.typeExt (.typeExt (.typeExt (.typeExt .empty ..) ..) ..) ..) ..)
    · intro aᵢ aᵢnin
      let ⟨aᵢninI, aᵢninΔ⟩ := List.not_mem_append'.mp aᵢnin
      intro aₙ aₙnin
      let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
      let ⟨aₙninI, aₙninΔ⟩ := List.not_mem_append'.mp aₙnin'
      let aₙninI := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninI⟩
      let aₙninΔ := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninΔ⟩
      let Δaₘaᵢaₙwf := Δaₘwf.typeVarExt aᵢninΔ (K := K.list) |>.typeVarExt aₙninΔ (K := K.list)
      exact Bᵣki _ aᵢninI _ aₙninI |>.weakening Δaₘaᵢaₙwf
        (Δ' := .typeExt .empty ..) (Δ'' := .typeExt (.typeExt .empty ..) ..)
  · apply arr
    · apply app
      · exact var .head
      · rw [← Std.Range.map_get!_eq (as := [])]
        exact list nofun
    · apply app
      · exact var .head
      · exact Aki.weakening (Δ' := .typeExt .empty ..) (Δ'' := .empty) Δaₘwf

theorem id : [[Δ ⊢ λ a : K. a$0 : K ↦ K]] := by
  apply lam []
  intro a anin
  rw [Type.TypeVar_open, if_pos rfl]
  exact var .head

end Kinding

namespace EnvironmentWellFormedness

open Environment in
theorem subst (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kA: [[ Δ ⊢ A: K ]]): [[ ⊢ Δ, Δ'[A/a] ]] := by
  induction Δ' generalizing Δ a K A <;> simp_all [Environment.append]
  . case empty =>
    cases wf
    assumption
  . case typeExt Δ' a' K' ih =>
    cases wf
    case typeVarExt wf notIn =>
    constructor
    . case a => apply ih <;> assumption
    . case a =>
      clear ih K' kA
      simp_all [TypeVarNotInDom, TypeVarInDom]
      induction Δ' <;> simp_all [TypeVar_subst, Environment.TypeVar_subst, append, typeVarDom] <;> cases wf <;> simp_all
  . case termExt Δ' a' T ih =>
    cases wf
    case termVarExt wf notIn kind =>
    constructor
    . case a => apply ih <;> assumption
    . case a =>
      clear ih kind
      simp_all [TermVarNotInDom, TermVarInDom]
      induction Δ' <;> simp_all [TypeVar_subst, Environment.TypeVar_subst, append, typeVarDom, termVarDom] <;> cases wf <;> simp_all
    . case a => apply Kinding.subst' (K := K) <;> simp_all

end EnvironmentWellFormedness

end TabularTypeInterpreter.«F⊗⊕ω»
