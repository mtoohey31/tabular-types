import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Value
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Term
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Term

macro "rwomega" equality:term : tactic => `(tactic | (have _eq : $equality := (by omega); rw [_eq]; clear _eq))

namespace TabularTypeInterpreter.«F⊗⊕ω»

open Std

private
theorem _root_.Membership.mem.inc {r : Range} (h : i ∈ r) : i ∈ { r with stop := r.stop + 1 } :=
  ⟨h.lower, Nat.lt_add_right _ h.upper, h.step⟩

private
theorem progress.sandwich {f : Nat → α} (h : i < n) : [0:n].map (fun j => f j) =
  [:i].map (fun j => f j) ++
    f i :: [(i + 1) - (i + 1):n - (i + 1)].map (fun j => f (j + (i + 1))) := by
  rw [← List.singleton_append, Range.map_shift (Nat.le_refl _)]
  have : [f i] = List.map (fun j => f j) [i:i + 1] := by
    rw [Range.toList, if_pos (Nat.lt_succ_self _), Range.toList,
        if_neg (Nat.not_lt_of_le (Nat.le_refl _)), List.map, List.map]
  rw [this]
  rw [Range.map_append (Nat.le_succ _) (Nat.succ_le_of_lt h),
      Range.map_append (Nat.zero_le _) (Nat.le_of_lt h)]

private
theorem progress.fold {E : Nat → Term} (EtyA : ∀ i ∈ [0:n], [[ε ⊢ E@i : A@i]])
  (h : ∀ i ∈ [0:n], (∃ E', [[E@i -> E']]) ∨ (E i).IsValue) :
  (∃ i ∈ [0:n], (∀ j ∈ [0:i], (E j).IsValue) ∧ ∃ E', [[E@i -> E']]) ∨
    (∀ i ∈ [0:n], (E i).IsValue) := by
  induction n
  · case zero =>
    right
    intro _ ⟨_, lt_zero, _⟩
    contradiction
  · case succ j ih' => match ih' (fun j mem => EtyA j mem.inc) (fun j mem => h j mem.inc) with
    | .inl ⟨i, mem, ⟨E'', toE''⟩⟩ => exact .inl ⟨i, mem.inc, ⟨E'', toE''⟩⟩
    | .inr IsValue =>
      have jmem : j ∈ [0:j + 1] := ⟨Nat.zero_le _, Nat.lt_succ_self _, Nat.mod_one _⟩
      match h j jmem with
      | .inl ⟨E'', toE''⟩ => exact .inl ⟨j, jmem, ⟨IsValue, ⟨E'', toE''⟩⟩⟩
      | .inr jIsValue =>
        right
        intro i mem
        by_cases i = j
        · case pos h =>
          rw [h]
          exact jIsValue
        · case neg h =>
          exact IsValue i
            ⟨Nat.zero_le _, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ mem.upper) h, Nat.mod_one _⟩

local instance : Inhabited Value where
  default := ⟨.prodIntro [], .prodIntro nofun⟩
in
theorem progress (EtyA : [[ε ⊢ E : A]]) : (∃ E', [[E -> E']]) ∨ E.IsValue := by
  generalize Δeq : Environment.empty = Δ at EtyA
  induction EtyA <;> cases Δeq
  · case var xinε => cases xinε
  · case lam => exact .inr .lam
  · case app E' A' B F E'tyA'arrB _ ih₁ ih₂ => match ih₁ rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .appL E'toE''
    | .inr E'IsValue => match ih₂ rfl with
      | .inl ⟨F', FtoF'⟩ => exact .inl <| .intro _ <| .appR (V := ⟨E', E'IsValue⟩) FtoF'
      | .inr FIsValue =>
        let VE' : Value := ⟨E', E'IsValue⟩
        have : E' = VE'.1 := rfl
        have A'Blc := E'tyA'arrB.TypeVarLocallyClosed_of
        have ⟨_, _, VE'eq⟩ := VE'.canonical_form_of_arr E'tyA'arrB
        rw [this, VE'eq]
        exact .inl <| .intro _ <| .lamApp (V := ⟨F, FIsValue⟩)
  · case typeLam => exact .inr .typeLam
  · case typeApp E' K _ _ E'ty _ ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .typeApp E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, _, Veq⟩ := V.canonical_form_of_forall E'ty
      rw [this, Veq]
      exact .inl <| .intro _ <| .typeLamApp
  · case prodIntro n E' A b h wf E'ty ih => match progress.fold E'ty (fun i mem => ih i mem rfl) with
    | .inl ⟨i, ⟨_, iltn, _⟩, IsValue, E'', toE''⟩ =>
      let V j : Value := if h' : j < i then
          ⟨E' j, IsValue j ⟨Nat.zero_le _, h', Nat.mod_one _⟩⟩
        else
          default
      rw [progress.sandwich iltn, Range.map_eq_of_eq_of_mem'' (fun j jmem => by
          show E' j = (V j).val
          dsimp only [V]
          rw [dif_pos jmem.upper]
      ), Nat.sub_self]
      exact .inl <| .intro _ <| .prodIntro toE''
    | .inr IsValue =>
      exact .inr <| .prodIntro fun E Emem => by
        have ⟨i, imem, Eeq⟩ := Range.mem_of_mem_map Emem
        rw [Eeq]
        exact IsValue i imem
  · case prodElim E' n _ _ i mem E'ty ih => match ih rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .prodElim E'toE''
    | .inr E'IsValue =>
      let V : Value := ⟨E', E'IsValue⟩
      have : E' = V.1 := rfl
      have ⟨_, Veq, h⟩ := V.canonical_form_of_prod E'ty
      rw [this, Veq]
      exact .inl <| .intro _ <| .prodElimIntro mem
  · case sumIntro ih => match ih rfl with
    | .inl ⟨E', toE'⟩ => exact .inl <| .intro _ <| .sumIntro toE'
    | .inr E'IsValue => exact .inr <| .sumIntro E'IsValue
  · case sumElim E' n As _ F _ E'ty Fty Fki ih₁ ih₂ => match ih₁ rfl with
    | .inl ⟨E'', E'toE''⟩ => exact .inl <| .intro _ <| .sumElimL E'toE''
    | .inr E'IsValue =>
      let VE' : Value := ⟨E', E'IsValue⟩
      have ⟨n', mem, VE'', VE'_eq, _⟩ := VE'.canonical_form_of_sum E'ty
      cases VE'_eq
      match progress.fold Fty (fun i mem => ih₂ i mem rfl) with
      | .inl ⟨j, ⟨_, jltn, _⟩, IsValue, F', toF'⟩ =>
        let VF k : Value := if h' : k < j then
            ⟨F k, IsValue k ⟨Nat.zero_le _, h', Nat.mod_one _⟩⟩
          else
            default
        rw [progress.sandwich jltn, Range.map_eq_of_eq_of_mem'' (fun j jmem => by
          show F j = (VF j).val
          dsimp only [VF]
          rw [dif_pos jmem.upper]
        ), Nat.sub_self]
        exact .inl <| .intro _ <| .sumElimR (V := VE') toF'
      | .inr FIsValue =>
        let VF j : Value := if h : j < n then
            ⟨F j, FIsValue j ⟨Nat.zero_le _, h, Nat.mod_one _⟩⟩
          else
            default
        rw [Range.map_eq_of_eq_of_mem'' (fun i mem => by
          show F i = (VF i).val
          dsimp only [VF]
          rw [dif_pos mem.upper]
        )]
        exact .inl ⟨_, .sumElimIntro mem⟩
  · case equiv ih => exact ih rfl


namespace Typing

open Environment TermVarInEnvironment  in
theorem weakening_r' (EtyT: [[ Δ, Δ'' ⊢ E: T ]]) (wf: [[ ⊢ Δ, Δ', Δ'' ]]): [[ Δ, Δ', Δ'' ⊢ E: T ]] := by
  generalize Δ_eq : [[ (Δ, Δ'') ]] = Δ_ at EtyT
  induction EtyT generalizing Δ''
  case var Δ_ x T wf' xin =>
    subst Δ_
    refine .var wf ?_
    clear wf'
    induction Δ' generalizing Δ''
    . case empty => simp_all [empty_append]
    . case typeExt Δ' a K ih =>
      rw [<- append_type_assoc]
      apply ih
      . simp_all [append_type_assoc]
      . apply append_elim at xin
        cases xin
        . case inl xin =>
          apply TermVarInEnvironment.weakening_r
          . simp_all [TermVarNotInDom, TermVarInDom, termVarDom_append, termVarDom]
          . simp_all
        . case inr xin =>
          simp_all [TermVarInEnvironment.weakening_l]
    . case termExt _ Δ' x' T' ih =>
      rw [<- append_term_assoc]
      apply ih
      . simp_all [append_term_assoc]
      . rw [append_term_assoc]
        apply TermVarInEnvironment.append_elim at xin
        cases xin
        . case inl xin =>
          apply TermVarInEnvironment.weakening_r
          . simp_all
          . by_cases (x = x')
            . case pos eq =>
              -- contradiction
              subst x'
              rw [<- append_term_assoc, append_assoc] at wf
              have xinfv := wf.append_termVar_fresh_l x (by simp_all [termVarDom_append, termVarDom])
              rw [termVarDom_append] at xinfv
              aesop (add norm TermVarNotInDom, norm TermVarInDom, safe forward TermVarInDom_of)
            . case neg neq =>
              constructor <;> simp_all [TermVarNe]
        . case inr xin =>
          simp_all [TermVarInEnvironment.weakening_l]
  case lam Δ_ A E T I EtyT ih =>
    subst Δ_
    refine .lam (I := I ++ Δ.termVarDom ++ Δ'.termVarDom ++ Δ''.termVarDom) (λ x xnin => ?_)
    rw [append_termExt_assoc, append_termExt_assoc]
    refine ih x (by simp_all) ?_ (by rw [append_termExt_assoc])
    -- wts. ⊢ Δ, Δ', Δ'', x: A
    refine .termVarExt wf (by simp_all [TermVarNotInDom, TermVarInDom, termVarDom_append]) ?_
    -- wts. Δ, Δ', Δ'' ⊢ A: *
    have := EtyT x (by simp_all)
    have := this.WellFormedness_of
    cases this; case termVarExt h1 h2 AkiStar =>
    refine AkiStar.weakening_r' (λ a anin => ?_)
    exact wf.append_typeVar_fresh_l a (by simp_all [typeVarDom_append])
  case typeLam Δ_ A E T I EtyT ih =>
    subst Δ_
    refine .typeLam (I := I ++ Δ.typeVarDom ++ Δ'.typeVarDom ++ Δ''.typeVarDom) (λ a anin => ?_)
    rw [append_typeExt_assoc, append_typeExt_assoc]
    refine ih a (by simp_all) ?_ (by rw [append_typeExt_assoc])
    exact .typeVarExt wf (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom_append])
  case typeApp Δ_ E K T B EtyT BkiK ih =>
    subst Δ_
    refine .typeApp (ih wf rfl) ?_
    apply BkiK.weakening_r' (λ a anin => ?_)
    exact wf.append_typeVar_fresh_l a (by simp_all [typeVarDom_append])
  case sumIntro i n Δ_ _ T _ mem ty TkiStar h ih =>
    subst Δ_
    refine .sumIntro mem (ty.weakening wf) (λ x xin => ?_) h
    specialize TkiStar x xin
    refine TkiStar.weakening_r' (λ a anin => ?_)
    exact wf.append_typeVar_fresh_l a (by simp_all [typeVarDom_append])
  case sumElim Δ_ E n T _ F B EtyT FtyTB BkiStar ih1 ih2 =>
    subst Δ_
    refine .sumElim (ih1 wf rfl) (λ x xin => ih2 x xin wf rfl) ?_
    apply BkiStar.weakening_r' (λ a anin => ?_)
    exact wf.append_typeVar_fresh_l a (by simp_all [typeVarDom_append])
  case equiv Δ_ E T T' EtyT equiv ih =>
    subst Δ_
    refine .equiv (ih wf rfl) (equiv.weakening wf.EnvironmentTypeWellFormedness_of)

  all_goals aesop (add unsafe constructors Typing) (config := { enableSimp := false })

theorem weakening_r (EtyT: [[ Δ ⊢ E: T ]]) (wf: [[ ⊢ Δ, Δ' ]]): [[ Δ, Δ' ⊢ E: T ]] := by
  apply weakening_r' (Δ'' := Environment.empty) <;> simp_all [Environment.append]

theorem term_subst' (EtyA: [[ Δ, x: T, Δ' ⊢ E: A ]]) (FtyT : [[ Δ ⊢ F: T ]]): [[ Δ, Δ' ⊢ E[F/x] : A ]] := by
  generalize Δ_eq : [[ (Δ, x:T, Δ') ]] = Δ_ at EtyA
  induction EtyA generalizing Δ' <;> try simp_all [Term.TermVar_subst]
  . case var Δ_ x' A wf x'in =>
    subst Δ_
    by_cases (x = x')
    . case pos eq =>
      simp_all
      subst x'
      -- 1. by wf we know x ∉ Δ'.typeVarDom
      have fresh := wf.append_termVar_fresh_r x (by constructor)
      -- 2. then by uniqueness we know from x'In that A = T
      have eq := x'in.unique (T':=T) (by
        apply TermVarInEnvironment.weakening_r fresh
        constructor
      )
      subst A
      -- 3. then wts Δ, Δ' ⊢ F: T, by weakening FtyT we are done
      apply weakening_r FtyT wf.TermVar_drop
    . case neg neq =>
      simp_all
      -- 1. by x'in we know x': A is either in (Δ, x: T) or Δ'
      apply TermVarInEnvironment.append_elim at x'in
      refine .var wf.TermVar_drop ?_
      cases x'in
      . case inl x'in =>
        -- 2a. If x': A ∈ Δ, x: T, we also know that x': A ∉ dom(Δ')
        obtain ⟨notInΔ', x'in⟩ := x'in
        -- 3a. and by x ≠ x' we know x': A ∈ Δ.
        --     wts. x': A ∈ Δ, Δ', by weakening we are done
        exact TermVarInEnvironment.weakening_r notInΔ' (by cases x'in <;> simp_all)
      . case inr x'in =>
        -- 2b. If x': A ∈ Δ', similarly by weakening we are done
        exact TermVarInEnvironment.weakening_l x'in
  . case lam Δ_ A E B I EtyB ih =>
    subst Δ_
    refine .lam (I := x :: I) (λ x' x'nin => ?_)
    rw [<- FtyT.TermVarLocallyClosed_of.TermVar_open_TermVar_subst_comm (by aesop)]
    exact ih x' (by simp_all) (by rw [Environment.append_termExt_assoc])
  . case app Δ_ E1 A B E2 E1tyAB E2tyA ih1 ih2 =>
    subst Δ_
    exact .app (ih1 rfl) (ih2 rfl)
  . case typeLam Δ_ K E A I EtyA ih =>
    subst Δ_
    refine .typeLam (I := x :: (I ++ F.freeTypeVars)) (λ a' a'nin => ?_)
    rw [<- FtyT.TermTypeVarLocallyClosed_of.TermVar_open_TypeVar_subst_comm]
    exact ih a' (by simp_all) (by rw [Environment.append_typeExt_assoc])
  . case typeApp Δ_ E K A B EtyA BkiK ih =>
    subst Δ_
    exact .typeApp (ih rfl) BkiK.TermVar_drop
  . case prodIntro Δ_ _ _ _ _ wf _ h ih =>
    subst Δ_
    exact .prodIntro wf.TermVar_drop (ih · · rfl) h
  . case prodElim Δ_ _ n _ _ _ _ _ ih =>
    subst Δ_
    exact .prodElim (n := n) (ih rfl) (by simp_all)
  . case sumIntro _ n Δ_ _ _ _ mem EtyA AkiStar h ih =>
    subst Δ_
    exact .sumIntro (n := n) mem (ih rfl) (λ x xin => AkiStar x xin |>.TermVar_drop) h
  . case sumElim Δ_ _ n _ _ _ _ _ _ BkiStar ih1 ih2 =>
    subst Δ_
    exact .sumElim (n := n) (ih1 rfl) (λ x xin => ih2 x xin rfl) BkiStar.TermVar_drop
  . case equiv Δ_ E A B EtyA equiv ih =>
    subst Δ_
    exact .equiv (ih rfl) equiv.TermVar_drop

theorem term_subst (EtyA: [[ Δ, x: T ⊢ E: A ]]) (FtyT : [[ Δ ⊢ F: T ]]): [[ Δ ⊢ E[F/x] : A ]] :=
  Typing.term_subst' (Δ' := [[ ε ]]) EtyA FtyT

theorem Term_open (EtyA : Typing [[(Δ, x : B, Δ')]] (.TermVar_open E x n) A)
  (xnin : x ∉ E.freeTermVars) (FtyB : [[Δ ⊢ F : B]]) : Typing [[(Δ, Δ')]] (.Term_open E F n) A := by
  rw [← Term.TermVar_open_TermVar_subst_eq_Term_open_of_not_mem_freeTermVars xnin]
  exact EtyA.term_subst' FtyB

theorem Term_multi_open (EtyA : [[Δ,,, </ x@i : B@i // i in [:n] />, Δ' ⊢ E^^^x#n : A]])
  (xninE : ∀ i, x i ∉ E.freeTermVars) (xninF : ∀ i, ∀ j ∈ [:n], x i ∉ (F j).freeTermVars)
  (xinj : x.Injective') (FtyB : ∀ i ∈ [:n], [[Δ ⊢ F@i : B@i]])
  : [[Δ, Δ' ⊢ E^^^^F@@i#n/x : A]] := by match n with
  | 0 =>
    rw [Range.map_same_eq_nil, Environment.multiTermExt, Term.TermVar_multi_open] at EtyA
    exact EtyA
  | n' + 1 =>
    rw [Term.Term_multi_open]
    let mem : n' ∈ [:n'+1] := ⟨Nat.zero_le _, Nat.le.refl, Nat.mod_one _⟩
    apply Term_multi_open _ (Term.not_mem_freeTermVars_Term_open_intro (xninE _) <| xninF · _ mem)
      (by
        intro i j mem
        exact xninF i _ ⟨Nat.zero_le _, Nat.lt_add_right _ mem.upper, Nat.mod_one _⟩
      ) xinj (FtyB · ⟨Nat.zero_le _, Nat.lt_add_right _ ·.upper, Nat.mod_one _⟩)
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Environment.multiTermExt_snoc,
        Nat.succ_sub_one, Term.TermVar_multi_open, Term.TermVar_multi_open_comm Nat.le.refl] at EtyA
    rw [Term.Term_open_TermVar_multi_open_comm (FtyB _ mem |>.TermVarLocallyClosed_of) Nat.le.refl]
    let Δxwf := EtyA.WellFormedness_of.weakening.TermVar_drop (Δ' := .empty)
    apply EtyA.Term_open
    · apply Term.not_mem_freeTermVars_TermVar_multi_open_intro <| xninE n'
      intro i lt eq
      exact Nat.ne_of_lt lt <| xinj _ _ eq.symm
    · rw [← Environment.append_empty (Δ := .multiTermExt ..),
          Environment.multiTermExt_eq_append (Δ' := .empty), Environment.append_empty] at Δxwf ⊢
      exact FtyB _ mem |>.weakening Δxwf (Δ'' := .empty)

open Environment TermVarInEnvironment in
theorem type_subst' (EtyA: [[ Δ, a: K, Δ' ⊢ E: A ]]) (BkiK : [[ Δ ⊢ B: K ]]): [[ Δ, Δ'[B/a] ⊢ E[B/a] : A[B/a] ]] := by
  generalize Δ_eq : [[ (Δ, a:K, Δ') ]] = Δ_ at EtyA
  induction EtyA generalizing Δ' <;> try simp_all [Term.TypeVar_subst, Type.TypeVar_subst]
  . case var Δ_ x' A wf x'in =>
    subst Δ_
    refine .var (wf.TypeVar_subst BkiK) ?_
    obtain ⟨x'nin, x'in'⟩ | x'in' := x'in.append_elim
    . case inl.intro =>
      -- a) x': A ∈ Δ, wts. x': A[B/α] ∈ Δ
      refine append_intro_l ?_ (by
        clear * - x'nin
        simp_all [TermVarNotInDom, TermVarInDom]
        induction Δ' <;> simp_all [TypeVar_subst, termVarDom]
      )
      -- 1. by wf we know ∀x: A ∈ Δ, a ∉ A.freeTypeVars
      cases x'in'; case typeVarExt x'in' =>
      rw [<- append_type_assoc] at wf
      have anin := x'in'.freeTypeVars_in_Δ wf.weakening a
        |>.mt (wf.append_typeVar_fresh_l a (by simp_all [typeVarDom_append, typeVarDom]))
      -- 2. so a ∉ A, therefore A[B/a] = A, so x': A[B/α] ∈ Δ. Done.
      rw [Type.TypeVar_subst_id_of_not_mem_freeTypeVars anin]
      exact x'in'
    . case inr =>
      -- b) x': A ∈ Δ', by definition of Env.TypeVar_subst and Kind.TypeVar_subst we are done.
      clear * - x'in'
      induction x'in' <;> simp_all [TypeVar_subst] <;> constructor <;> simp_all
  . case lam Δ_ A1 E A2 I EtyA2 ih =>
    subst Δ_
    refine .lam (I := I ++ Δ.termVarDom ++ Δ'.termVarDom) (λ x xnin => ?_)
    rw [<- Term.TypeVar_open_TermVar_subst_comm]
    exact ih x (by simp_all) (by rw [append_termExt_assoc])
  . case app Δ_ E1 A B E2 E1tyAB E2tyA ih1 ih2 =>
    subst Δ_
    exact .app (ih1 rfl) (ih2 rfl)
  . case typeLam Δ_ K' E A I EtyA ih =>
    subst Δ_
    refine .typeLam (I := a :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom) (λ a' a'nin => ?_)
    rw [
      <- BkiK.TypeVarLocallyClosed_of.Term_TypeVar_open_TypeVar_subst_comm (by aesop),
      <- BkiK.TypeVarLocallyClosed_of.TypeVar_open_TypeVar_subst_comm (by aesop)
    ]
    exact ih a' (by simp_all) (by rw [append_typeExt_assoc])
  . case typeApp Δ_ E K2 A1 A2 EtyA1 A2kiK2 ih =>
    subst Δ_
    rw [BkiK.TypeVarLocallyClosed_of.Type_open_TypeVar_subst_dist]
    refine .typeApp (ih rfl) ?_
    exact A2kiK2.subst' EtyA1.WellFormedness_of BkiK
  . case prodIntro Δ_ _ _ _ _ wf _ h _ =>
    subst Δ_
    refine .prodIntro (wf.subst BkiK) (by simp_all) h
  . case prodElim Δ_ E n A _ i EtyA iRange ih =>
    subst Δ_
    specialize ih rfl
    unfold Function.comp at ih
    simp_all
    have ⟨A', A'eq⟩: ∃A': ℕ → «Type», ∀i, A' i = (A i).TypeVar_subst a B := ⟨λi => (A i).TypeVar_subst a B, λi => by simp⟩
    rw [<- A'eq i]; rw [<- funext (λi => A'eq i)] at ih
    refine .prodElim (n := n) ih iRange
  . case sumIntro _ n Δ_ _ _ _ _ EtyA A'kiStar h _ =>
    subst Δ_
    refine .sumIntro (n := n) (by simp_all) (by simp_all) (λ x xin => ?_) h
    exact A'kiStar x xin |>.subst' EtyA.WellFormedness_of BkiK
  . case sumElim Δ_ E n _ _ _ _ EtyA _ B'kiStar ih1 ih2 =>
    subst Δ_
    exact .sumElim (n := n) (ih1 rfl) (λ x xin => ih2 x xin rfl) (B'kiStar.subst' EtyA.WellFormedness_of BkiK)
  . case equiv Δ_ E A A' EtyA equiv ih =>
    subst Δ_
    refine .equiv (ih rfl) (equiv.subst' EtyA.TypeVarLocallyClosed_of EtyA.WellFormedness_of BkiK)

theorem type_subst (EtyA: [[ Δ, a: K ⊢ E: A ]]) (BkiK : [[ Δ ⊢ B: K ]]): [[ Δ ⊢ E[B/a] : A[B/a] ]] :=
  Typing.type_subst' (Δ' := [[ ε ]]) EtyA BkiK

theorem Type_open
  (EtyA : Typing [[(Δ, a : K, Δ')]] (.TypeVar_open E a n) (.TypeVar_open A a n))
  (aninE : a ∉ E.freeTypeVars) (aninA : a ∉ A.freeTypeVars) (Bki : [[Δ ⊢ B : K]])
  : Typing [[(Δ, Δ' [B / a])]] (.Type_open E B n) (.Type_open A B n) := by
  rw [← Term.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninE,
      ← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninA]
  exact EtyA.type_subst' Bki

theorem Type_open_Type_open
  (EtyA : Typing [[(Δ, a : K, Δ')]] (.TypeVar_open E a m) (.Type_open A (.TypeVar_open B a n) l))
  (aninE : a ∉ E.freeTypeVars) (aninA : a ∉ A.freeTypeVars) (aninB : a ∉ B.freeTypeVars)
  (B'ki : [[Δ ⊢ B' : K]])
  : Typing [[(Δ, Δ' [B' / a])]] (.Type_open E B' m) (.Type_open A (.Type_open B B' n) l) := by
  let B'lc := B'ki.TypeVarLocallyClosed_of.weaken (n := l)
  rw [Nat.zero_add] at B'lc
  rw [← Term.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninE,
      ← Type.TypeVar_open_TypeVar_subst_eq_Type_open_of_not_mem_freeTypeVars aninB,
      ← Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA, ← B'lc.Type_open_TypeVar_subst_dist]
  exact EtyA.type_subst' B'ki

theorem Type_open_Type_multi_open
  (EtyA : [[Δ,, </ a@i : K@i // i in [:n] />, Δ' ⊢ E^^^a#n : A^^(B^^^a#n)]])
  (aninE : ∀ i, a i ∉ E.freeTypeVars) (aninA : ∀ i, a i ∉ A.freeTypeVars)
  (aninB : ∀ i, a i ∉ B.freeTypeVars)
  (aninB' : ∀ i, ∀ j ∈ [:n], a i ∉ (B' j).freeTypeVars) (ainj : a.Injective')
  (B'ki : ∀ i ∈ [:n], [[Δ ⊢ B'@i : K@i]])
  : [[Δ, (Δ' ! </ [B'@i / a@i] // i in [:n] />) ⊢ E^^^^B'@@i#n/a : A^^(B^^^^B'@@i#n/a)]] := by
  match n with
  | 0 =>
    rw [Range.map_same_eq_nil, Environment.TypeVar_multi_subst]
    rw [Range.map_same_eq_nil, Environment.multiTypeExt, Term.TypeVar_multi_open,
        Type.TypeVar_multi_open] at EtyA
    exact EtyA
  | n' + 1 =>
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Environment.TypeVar_multi_subst_snoc,
        Nat.succ_sub_one, Term.Type_multi_open, Type.Type_multi_open]
    let mem : n' ∈ [:n'+1] := ⟨Nat.zero_le _, Nat.le.refl, Nat.mod_one _⟩
    apply Type_open_Type_multi_open _
      (Term.not_mem_freeTypeVars_Type_open_intro (aninE _) <| aninB' · _ mem) aninA
      (Type.not_mem_freeTypeVars_Type_open_intro (aninB _) <| aninB' · _ mem)
      (aninB' · · ⟨Nat.zero_le _, Nat.lt_add_right _ ·.upper, Nat.mod_one _⟩) ainj
      (B'ki · ⟨Nat.zero_le _, Nat.lt_add_right _ ·.upper, Nat.mod_one _⟩)
    rw [Range.map_eq_snoc_of_lt (Nat.zero_lt_succ _), Environment.multiTypeExt_snoc,
        Nat.succ_sub_one, Term.TypeVar_multi_open, Term.TypeVar_multi_open_comm Nat.le.refl,
        Type.TypeVar_multi_open, Type.TypeVar_open_TypeVar_multi_open_comm Nat.le.refl] at EtyA
    let Blc := B'ki _ mem |>.TypeVarLocallyClosed_of
    rw [Term.Type_open_TypeVar_multi_open_comm Blc Nat.le.refl,
        Blc.Type_open_TypeVar_multi_open_comm Nat.le.refl]
    let .typeVarExt Δawf .. := EtyA.WellFormedness_of.weakening
    apply EtyA.Type_open_Type_open
      (Term.not_mem_freeTypeVars_TypeVar_multi_open_intro (aninE _)
        fun _ lt eq => Nat.ne_of_lt lt <| ainj _ _ eq.symm) (aninA _)
      (Type.not_mem_freeTypeVars_TypeVar_multi_open_intro (aninB _)
        fun _ lt eq => Nat.ne_of_lt lt <| ainj _ _ eq.symm)
    specialize B'ki _ mem
    rw [← Environment.append_empty (Δ := .multiTypeExt ..),
        Environment.multiTypeExt_eq_append (Δ' := .empty)] at Δawf ⊢
    exact B'ki.weakening Δawf (Δ'' := .empty)

end Typing

theorem preservation.sandwich {α: Type} {nl nr : ℕ} {F1 F3: ℕ → α} {F2: α}:
  let G i := if i < nl then F1 i else if i = nl then F2 else F3 (i - nl - 1)
  [0:nl].map (λi => F1 i) ++ F2 :: [0:nr].map (λi => F3 i) = [0:nl + 1 + nr].map G := by
  intro G
  rw [progress.sandwich (n := nl + 1 + nr) (i := nl) (by omega)]
  simp_all
  refine List.append_eq_append ?_ ?_
  . exact Std.Range.map_eq_of_eq_of_mem (λ i iltnl => by simp_all [Membership.mem])
  . refine List.cons_eq_cons.mpr ⟨rfl, ?_⟩
    refine Std.Range.map_eq_of_eq_of_mem (λ i iltnl => ?_)
    repeat' rw [if_neg (by omega)]
    exact congrArg _ (by omega)

local instance : Inhabited Term where
  default := .prodIntro []
theorem preservation (EtyA: [[Δ ⊢ E : A]]) (EE': [[E -> E']]): [[Δ ⊢ E' : A]] := by
  induction EtyA generalizing E' <;> (try cases EE'; done) -- values can't step
  . case app Δ E A B F EtyAarrB FtyA ihE ihF =>
    cases EE'
    . case appL E' EE' => exact .app (ihE EE') FtyA
    . case appR F' E FF' => exact .app EtyAarrB (ihF FF')
    . case lamApp A' E F =>
      have ⟨eqA'A, I, EtyAarrB⟩ := EtyAarrB.inv_arr
      have ⟨x, notIn⟩ := (I ++ E.freeTermVars).exists_fresh
      rw [<- Term.TermVar_subst_intro_of_not_mem_freeTermVars (a := x) (by simp_all)]
      exact EtyAarrB x (by simp_all) |>.term_subst (.equiv FtyA eqA'A.symm)
  . case typeApp Δ E K A B EtyA BkiK ih =>
    cases EE'
    . case typeApp E' EE' => exact .typeApp (ih EE') BkiK
    . case typeLamApp K' E =>
      have ⟨Keq, I, EtyA⟩ := EtyA.inv_forall
      subst K'
      have ⟨a, notIn⟩ := (I ++ E.freeTypeVars ++ A.freeTypeVars).exists_fresh
      specialize EtyA a (by simp_all)
      rw [<- Term.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
      rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
      exact EtyA.type_subst BkiK
  . case prodIntro Δ n E A _ wf EtyA h ih =>
    generalize eqE_: Term.prodIntro ([0:n].map (λi => E i)) = E_ at EE'
    cases EE' <;> try cases eqE_
    . case prodIntro E_ E' nl V nr Er EE' =>
      injection eqE_ with eq
      have llt : nl < n := by
        have := congrArg List.length eq
        simp [List.length_append, List.length_cons, List.length_map, Std.Range.length_toList] at this
        omega
      rw [progress.sandwich llt] at eq
      have ⟨eql, eqr⟩ := List.append_inj eq (by simp_all [Std.Range.length_toList]); clear eq
      have eqEV := Std.Range.eq_of_mem_of_map_eq eql; clear eql
      injection eqr with eqEE_ eqr; simp at eqr; subst eqEE_
      have := Std.Range.length_eq_of_mem_eq eqr; subst this
      have eqEEr_shift := Std.Range.eq_of_mem_of_map_eq eqr; clear eqr
      rw [preservation.sandwich]
      simp_all; rwomega nl + 1 + (n - (nl + 1)) = n
      refine .prodIntro wf (λ i iltn => ?_) h
      repeat' split
      . case _ iltnl =>
        rw [← eqEV i (by simp_all [Membership.mem])]
        exact EtyA i (by simp_all [Membership.mem])
      . case _ igenl ieqnl =>
        subst i
        exact ih nl (by simp_all) EE'
      . case _ igenl inenl =>
        rw [← eqEEr_shift _ (by simp_all [Membership.mem]; omega)]
        rwomega i - nl - 1 + (nl + 1) = i
        exact EtyA i (by simp_all [Membership.mem])
  . case prodElim Δ E n A i EtyA iltn ih =>
    cases EE'
    . case prodElim E' EE' => exact .prodElim (ih EE') iltn
    . case prodElimIntro n' E iltn' =>
      clear ih
      have ⟨eqn'n, EtyA⟩ := EtyA.inv_prod
      simp_all [NatInZeroRange]
  . case sumIntro i n Δ E A ilen EtyA AkiStar ih => cases EE'; constructor <;> simp_all
  . case sumElim Δ E n A _ F B EtyA FtyAB BkiStar ih1 ih2 =>
    generalize eqEF: [[ case E {</ F@i // i in [:n] />} ]] = EF at EE'
    cases EE' <;> try cases eqEF
    . case sumElimL E_ E' n_ F_ EE' =>
      injection eqEF with eqEE_ eq; subst E_
      have eqnn_ := Std.Range.length_eq_of_mem_eq eq; subst eqnn_
      have eqFF_ := Std.Range.eq_of_mem_of_map_eq eq; clear eq
      refine .sumElim (ih1 EE') (λ x xin => by simp_all) BkiStar
    . case sumElimR F_ F' V nl V' nr Fr FF' =>
      -- TODO clean up
      simp_all
      obtain ⟨eqEV, eq⟩ := eqEF; subst E
      let G i := if i < nl then (V' i).val else if i = nl then F_ else Fr (i - nl - 1)
      let G' i := if i < nl then (V' i).val else if i = nl then F' else Fr (i - nl - 1)
      have Geq : [0:nl].map (λ i => (V' i).val) ++ F_ :: [0:nr].map (λ j => Fr j) = [0:nl + 1 + nr].map G := preservation.sandwich
      rw [Geq] at eq
      have G'eq : [0:nl].map (λ i => (V' i).val) ++ F' :: [0:nr].map (λ j => Fr j) = [0:nl + 1 + nr].map G' := preservation.sandwich
      rw [G'eq]
      have eqn := Std.Range.length_eq_of_mem_eq eq; subst eqn
      have : F nl = F_ := by
        clear * - Geq eq
        have eqFG : F nl = G nl := by
          clear * - eq
          have := congrArg (λ i => i.get! nl) eq
          simp only at this
          rw [
            Std.Range.get!_map (by omega),
            Std.Range.get!_map (by omega)] at this
          exact this
        clear eq
        have := congrArg (λ i => i.get! nl) Geq
        simp only at this
        rw [Std.Range.get!_map (by omega)] at this
        rw [List.get!_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_append,
          if_neg (by simp_all [Std.Range.length_toList]), List.length_map, Std.Range.length_toList] at this
        simp_all
      subst F_
      have F'tyAB := ih2 nl (by simp_all [Membership.mem]; omega) FF'
      refine .sumElim EtyA (λ i iltn => ?_) BkiStar
      simp_all
      split
      . case isTrue iltnl =>
        have eqFG := eq i (Std.Range.mem_toList_of_mem (by simp_all [Membership.mem]))
        specialize FtyAB i (by simp_all [Membership.mem])
        rw [eqFG] at FtyAB
        unfold G at FtyAB
        simp_all
      . case isFalse igenl =>
        split
        . case isTrue ieqnl =>
          subst i
          exact ih2 nl (by simp_all) FF'
        . case isFalse inenl =>
          have eqFG := eq i (Std.Range.mem_toList_of_mem (by simp_all [Membership.mem]))
          specialize FtyAB i (by simp_all [Membership.mem])
          rw [eqFG] at FtyAB
          unfold G at FtyAB
          rw [← ite_not] at FtyAB
          simp_all
    . case sumElimIntro i n_ V V' iltn_ =>
      injection eqEF with eqEV eq; subst E
      have eqnn_ := Std.Range.length_eq_of_mem_eq eq; subst eqnn_
      have eqFV' := Std.Range.eq_of_mem_of_map_eq eq; clear eq
      have ⟨_, VtyA, _⟩ := EtyA.inv_sum
      refine .app (by simp_all) VtyA
  . case equiv Δ E A B EtyA eq ih => exact .equiv (ih EE') eq

end TabularTypeInterpreter.«F⊗⊕ω»
