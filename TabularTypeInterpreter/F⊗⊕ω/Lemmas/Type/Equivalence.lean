import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type.Kinding

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace TypeEquivalenceI

local instance : Inhabited «Type» where
  default := .list []
in
def list' (As Bs: List «Type») (length_eq: As.length = Bs.length) (h : ∀A B, ⟨A, B⟩ ∈ As.zip Bs → [[ Δ ⊢ A ≡ᵢ B ]] )
  : TypeEquivalenceI Δ (.list As) (.list Bs) := by
  rw [← Std.Range.map_get!_eq (as := As), ← Std.Range.map_get!_eq (as := Bs), ← length_eq]
  apply list
  intro i mem
  apply h
  have := (As.zip Bs).get!_mem <| by
    rw [List.length_zip, ← length_eq, Nat.min_self]
    exact mem.upper
  rw [List.get!_zip length_eq mem.upper] at this
  exact this

open Environment in
theorem subst_rename' {a': TypeVarId}
  (h: [[ Δ, a: K, Δ' ⊢ A ≡ᵢ B ]])
  (wf: [[ ⊢ Δ, a: K, Δ' ]])
  (fresh: a' ∉ [[ (Δ, a: K, Δ') ]].typeVarDom):
  [[ Δ, a': K, Δ'[a'/a] ⊢ A[a'/a] ≡ᵢ B[a'/a] ]] := by
  have a'lc: [[ (a') ]].TypeVarLocallyClosed := by constructor
  generalize Δ_eq: [[ (Δ, a: K, Δ') ]] = Δ_ at h
  induction h generalizing Δ Δ' <;> (try simp_all [Type.TypeVar_subst]) <;> subst Δ_eq <;> try simp_all [Membership.mem]; aesop (add unsafe constructors TypeEquivalenceI)
  · case eta => sorry
  . case lamApp B K' A BkiK' =>
    rw [a'lc.Type_open_TypeVar_subst_dist]
    refine .lamApp ?_
    have BkiK': [[((Δ, a': K , a : K) , Δ') ⊢ B : K']] := by
      rw [← Environment.append_type_assoc] at BkiK'
      have := BkiK'.weakening_r' (Δ' := [[ ε, a': K ]]) (by simp_all [typeVarDom_append, typeVarDom])
      repeat1' rw [Environment.append_type_assoc] at this
      exact this
    have wf' : [[ ⊢ ((Δ, a': K , a : K) , Δ') ]] := by
      rw [← append_type_assoc] at wf ⊢
      refine wf.strengthen_type (by simp_all [typeVarDom, typeVarDom_append])
    exact BkiK'.subst' wf' (.var .head)
  . case listAppList A n B Alc =>
    unfold Function.comp
    simp_all [Type.TypeVar_subst]
    exact .listAppList (Alc.TypeVar_subst a'lc)
  . case listAppId A K' AkiLK =>
    refine .listAppId ?_
    have AkiLK': [[((Δ, a': K , a : K) , Δ') ⊢ A : L K']] := by
      rw [← Environment.append_type_assoc] at AkiLK
      have := AkiLK.weakening_r' (Δ' := [[ ε, a': K ]]) (by simp_all [typeVarDom_append, typeVarDom])
      repeat1' rw [Environment.append_type_assoc] at this
      exact this
    have wf' : [[ ⊢ ((Δ, a': K , a : K) , Δ') ]] := by
      rw [← append_type_assoc] at wf ⊢
      refine wf.strengthen_type (by simp_all [typeVarDom, typeVarDom_append])
    exact AkiLK'.subst' wf' (.var .head)
  . case listAppComp A₁ K₁ K₂ _ A₀lc A₁ki =>
    refine .listAppComp (A₀lc.TypeVar_subst a'lc) ?_ (K₁ := K₁) (K₂ := K₂) -- (A₁ki. a'lc)
    have A₁ki': [[((Δ, a': K , a : K) , Δ') ⊢ A₁ : K₁ ↦ K₂]] := by
      rw [← Environment.append_type_assoc] at A₁ki
      have := A₁ki.weakening_r' (Δ' := [[ ε, a': K ]]) (by simp_all [typeVarDom_append, typeVarDom])
      repeat1' rw [Environment.append_type_assoc] at this
      exact this
    have wf' : [[ ⊢ ((Δ, a': K , a : K) , Δ') ]] := by
      rw [← append_type_assoc] at wf ⊢
      refine wf.strengthen_type (by simp_all [typeVarDom, typeVarDom_append])
    exact A₁ki'.subst' wf' (.var .head)
  . case lam K' A B I AB ih =>
    apply TypeEquivalenceI.lam (I := a :: a' :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a'' nin
    repeat rw [<- a'lc.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . exact wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom, typeVarDom_append])
    . aesop (add simp typeVarDom)
  . case scheme K' A B I AB ih =>
    apply TypeEquivalenceI.scheme (I := a :: a' :: I ++ Δ.typeVarDom ++ Δ'.typeVarDom)
    intro a'' nin
    repeat rw [<- a'lc.TypeVar_open_TypeVar_subst_comm (neq := by aesop)]
    rw [Environment.append_typeExt_assoc, Environment.typeExt_subst]
    apply ih <;> simp_all [Environment.append]
    . exact wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom, typeVarDom, typeVarDom_append])
    . aesop (add simp typeVarDom)
  . case list n A B AB ih =>
    unfold Function.comp
    simp_all [Type.TypeVar_subst]
    refine .list (λ i iltn => by simp_all)

open Environment in
theorem subst_rename {a': TypeVarId} (h: [[ Δ, a: K ⊢ A ≡ᵢ B ]]) (wf: [[ ⊢ Δ, a: K ]]) (fresh: a' ∉ a :: Δ.typeVarDom): [[ Δ, a': K ⊢ A[a'/a] ≡ᵢ B[a'/a] ]] :=
  subst_rename' (Δ' := [[ ε ]]) h wf (by simp_all [typeVarDom, typeVarDom_append])

theorem weakening_type' (h: [[ Δ, Δ' ⊢ A ≡ᵢ B ]]) (fresh: a ∉ Δ.typeVarDom) : [[ Δ, a: K, Δ' ⊢ A ≡ᵢ B ]] := by
  generalize Δ_eq : [[ (Δ, Δ') ]] = Δ_ at h
  induction h generalizing Δ Δ' <;> subst Δ_eq <;> try aesop (add norm Type.freeTypeVars) (add unsafe constructors TypeEquivalenceI)
  . case lamApp B K' A BkiK' =>
    refine .lamApp ?_
    rw [← Environment.append_type_assoc]
    exact BkiK'.weakening_r' (by simp_all [Environment.typeVarDom])
  . case listAppId AkiLK =>
    refine .listAppId ?_
    . rw [<- Environment.append_type_assoc]; exact Kinding.weakening_r' (fresh := by simp_all [Environment.typeVarDom]) AkiLK
  · refine .listAppComp a_1 ?_ (K₁ := K₁) (K₂ := K₂)
    rw [← Environment.append_type_assoc]
    exact a_2.weakening_r' (by simp_all [Environment.typeVarDom])
  . case lam K' A B I AB ih =>
    apply TypeEquivalenceI.lam (I := a :: I ++ Δ.typeVarDom)
    intro a' nin
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K')
    simp_all [Environment.append]
  . case scheme K' A B I AB ih =>
    apply TypeEquivalenceI.scheme (I := a :: I ++ Δ.typeVarDom)
    intro a' nin
    specialize @ih a' (by simp_all) Δ (Δ'.typeExt a' K')
    simp_all [Environment.append]

theorem weakening_type (h: [[ Δ ⊢ A ≡ᵢ B ]]) (fresh: a ∉ Δ.typeVarDom) : [[ Δ, a: K ⊢ A ≡ᵢ B ]] := weakening_type' (Δ' := [[ ε ]]) h fresh

theorem lam_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ᵢ B^a ]])(wf: [[ ⊢ Δ, a: K ]]): [[ Δ ⊢ (λ a : K. A) ≡ᵢ (λ a : K. B) ]] := by
  refine .lam (I := a :: Δ.typeVarDom) ?_
  intro a' nin
  repeat1' rw [Type.TypeVar_open_eq_Type_open_var]
  repeat1' rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
  exact h.subst_rename wf nin

theorem scheme_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ᵢ B^a ]]) (wf: [[ ⊢ Δ, a: K ]]): [[ Δ ⊢ (∀ a : K. A) ≡ᵢ (∀ a : K. B) ]] := by
  refine .scheme (I := a :: Δ.typeVarDom) ?_
  intro a' nin
  repeat1' rw [Type.TypeVar_open_eq_Type_open_var]
  repeat1' rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)]
  exact h.subst_rename wf nin

open «Type» TypeVarLocallyClosed in
theorem preserve_lc (h: [[ Δ ⊢ A ≡ᵢ B ]]) (Alc: A.TypeVarLocallyClosed): B.TypeVarLocallyClosed := by
  induction h
  case lamApp => match Alc with | .app (.lam _) _ => apply Type_open_dec <;> simp_all
  case listAppList =>
    match Alc with
    | .listApp Alc (.list Blc) =>
      refine .list λ T Tin => ?_
      have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
      exact Alc.app <| Blc _ (Std.Range.mem_map_of_mem iltn)
  case listAppComp Alc =>
    let .listApp A₀lc (.listApp A₁lc B'lc) := Alc
    exact .listApp (.lam (.app A₀lc.weaken (.app A₁lc.weaken (.var_bound Nat.one_pos)))) B'lc
  all_goals
    set_option aesop.dev.statefulForward false in
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

open «Type» TypeVarLocallyClosed in
theorem preserve_lc_rev (h: [[ Δ ⊢ A ≡ᵢ B ]]) (Blc: B.TypeVarLocallyClosed): A.TypeVarLocallyClosed := by
  induction h
  case eta Alc => exact .lam <| Alc.weaken.app <| .var_bound Nat.one_pos
  case lamApp Δ B K A BkiK =>
    rename' Blc => ABlc
    have Blc := BkiK.TypeVarLocallyClosed_of
    have ⟨a, nin⟩ := A.freeTypeVars.exists_fresh
    rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)] at ABlc
    have Abody := ABlc.TypeVar_subst_drop
    apply TypeVar_close_inc (a := a) at Abody
    rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Abody
    exact Abody.lam.app Blc
  case listAppList A Δ n B Alc =>
    match Blc with
    | .list ABlc =>
      refine .listApp Alc (.list ?_)
      cases n
      . case zero => simp [Std.Range.map, Std.Range.toList]
      . case succ n _ =>
        simp_all [Std.Range.mem_map_of_mem, Std.Range.mem_of_mem_toList]
        intro i iltSn
        match ABlc i iltSn with | .app _ Blc => exact Blc
  case listAppComp A₀lc A₁ki => match Blc with | .listApp (.lam (.app _ bodyA₁)) Blc => exact A₀lc.listApp (A₁ki.TypeVarLocallyClosed_of.listApp Blc)
  all_goals
    set_option aesop.dev.statefulForward false in
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

end TypeEquivalenceI

namespace TypeEquivalenceS

theorem sym (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ B ≡ₛ A ]] := by
  induction h with
  | base h => exact .symm h
  | symm h => exact .base h
  | trans _ _ ih1 ih2 => exact ih2.trans ih1

theorem preserve_lc (h: [[ Δ ⊢ A ≡ₛ B ]]):  (A.TypeVarLocallyClosed → B.TypeVarLocallyClosed) ∧ (B.TypeVarLocallyClosed → A.TypeVarLocallyClosed) := by
  induction h with
  | base AB => exact ⟨λAlc => AB.preserve_lc Alc, λBlc => AB.preserve_lc_rev Blc⟩
  | symm AB => exact ⟨λBlc => AB.preserve_lc_rev Blc, λAlc => AB.preserve_lc Alc⟩
  | trans => simp_all

theorem lam_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ₛ B^a ]])(wf: [[ ⊢ Δ, a: K ]]) (Abody: A.TypeVarLocallyClosed 1): [[ Δ ⊢ (λ a : K. A) ≡ₛ (λ a : K. B) ]] := by
  generalize Aa_eq : [[ (A^a) ]] = Aa at h
  generalize Ba_eq : [[ (B^a) ]] = Ba at h
  induction h generalizing A B
  . case base h =>
    subst Aa_eq Ba_eq
    exact .base (TypeEquivalenceI.lam_intro_ex a fresh h wf)
  . case symm h =>
    subst Aa_eq Ba_eq
    exact .symm (TypeEquivalenceI.lam_intro_ex a (by simp_all) h wf)
  . case trans A_ B_ C_ AB BC ih1 ih2 =>
    subst Aa_eq Ba_eq
    have B_lc := AB.preserve_lc.1 Abody.strengthen

    specialize ih1 (B := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) Abody rfl (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id B_lc])
    specialize ih2 (A := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) B_lc.TypeVar_close_inc (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id B_lc]) rfl
    exact .trans ih1 ih2

theorem scheme_intro_ex a (fresh: a ∉ A.freeTypeVars ++ B.freeTypeVars ++ Δ.typeVarDom) (h: [[ Δ, a : K ⊢ A^a ≡ₛ B^a ]]) (wf: [[ ⊢ Δ, a: K ]]) (Abody: A.TypeVarLocallyClosed 1): [[ Δ ⊢ (∀ a : K. A) ≡ₛ (∀ a : K. B) ]] := by
  generalize Aa_eq : [[ (A^a) ]] = Aa at h
  generalize Ba_eq : [[ (B^a) ]] = Ba at h
  induction h generalizing A B
  . case base h =>
    subst Aa_eq Ba_eq
    exact .base (TypeEquivalenceI.scheme_intro_ex a fresh h wf)
  . case symm h =>
    subst Aa_eq Ba_eq
    exact .symm (TypeEquivalenceI.scheme_intro_ex a (by simp_all) h wf)
  . case trans A_ B_ C_ AB BC ih1 ih2 =>
    subst Aa_eq Ba_eq
    have B_lc := AB.preserve_lc.1 Abody.strengthen

    specialize ih1 (B := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) Abody rfl (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id B_lc])
    specialize ih2 (A := [[\a^B_]]) (by simp_all [Type.not_mem_freeTypeVars_TypeVar_close]) B_lc.TypeVar_close_inc (by rw [Type.TypeVarLocallyClosed.TypeVar_open_TypeVar_close_id B_lc]) rfl
    exact .trans ih1 ih2

private
theorem ctor1 {T: «Type» → «Type»} (h: [[ Δ ⊢ A ≡ₛ B ]]) (c: ∀{Δ A B}, [[ Δ ⊢ A ≡ᵢ B]] → TypeEquivalenceI Δ (T A) (T B) ) : TypeEquivalenceS Δ (T A) (T B) := by
  induction h with
  | base h => exact .base (c h)
  | symm h => exact .symm (c h)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem prod (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ ⊗ A ≡ₛ ⊗ B ]] := ctor1 h (.prod)
theorem sum (h: [[ Δ ⊢ A ≡ₛ B ]]) : [[ Δ ⊢ ⊕ A ≡ₛ ⊕ B ]] := ctor1 h (.sum)

private
theorem ctor2_left_refl {T: «Type» → «Type» → «Type»} (h: [[ Δ ⊢ A ≡ₛ A' ]]) (c: ∀{Δ A A' B B'}, [[ Δ ⊢ A ≡ᵢ A' ]] → [[ Δ ⊢ B ≡ᵢ B' ]] → TypeEquivalenceI Δ (T A B) (T A' B') ) : TypeEquivalenceS Δ (T C A) (T C A') := by
  induction h with
  | base h => exact .base (c .refl h)
  | symm h => exact .symm (c .refl h)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private
theorem ctor2 {T: «Type» → «Type» → «Type»} (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) (c: ∀{Δ A A' B B'}, [[ Δ ⊢ A ≡ᵢ A' ]] → [[ Δ ⊢ B ≡ᵢ B' ]] → TypeEquivalenceI Δ (T A B) (T A' B') ) : TypeEquivalenceS Δ (T A B) (T A' B') := by
  induction h1 <;> induction h2
  . case base.base h1 _ _ h2 => exact .base (c h1 h2)
  . case base.symm h1 _ _ h2 =>
    exact .trans
      (.symm (c .refl h2))
      (.base (c h1 .refl))
  . case base.trans h _ _ _ _ BC ih1 ih2 =>
    refine (.trans (.trans
      ih1
      (.symm (c h .refl)))
      ih2)
  . case symm.base h1 _ _ h2 =>
    exact .trans
      (.base (c .refl h2))
      (.symm (c h1 .refl))
  . case symm.symm h1 _ _ h2 =>
    exact .trans
      (.symm (c .refl h2))
      (.symm (c h1 .refl))
  . case symm.trans h _ _ _ _ BC ih1 ih2 =>
    exact (.trans (.trans
      ih1
      (.base (c h .refl)))
      ih2)
  . case trans.base BC _ _ h ih1 ih2 =>
    exact (.trans (.trans
      ih1
      (.symm (c .refl h)))
      ih2)
  . case trans.symm BC _ _ h ih1 ih2 =>
    exact (.trans (.trans
      ih1
      (.base (c .refl h)))
      ih2)
  . case trans.trans A T A' AT TA' B U B' BU UB' _ _ ih1 ih2 =>
    exact .trans (.trans
      ih1
      (ctor2_left_refl (BU.trans UB').sym c))
      ih2

theorem app (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) : [[ Δ ⊢ A B ≡ₛ A' B' ]] := ctor2 h1 h2 (.app)
theorem arr (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) : [[ Δ ⊢ A → B ≡ₛ A' → B' ]] := ctor2 h1 h2 (.arr)
theorem listApp (h1: [[ Δ ⊢ A ≡ₛ A' ]]) (h2: [[ Δ ⊢ B ≡ₛ B' ]]) : [[ Δ ⊢ A ⟦B⟧ ≡ₛ A' ⟦B'⟧ ]] := ctor2 h1 h2 (.listApp)

end TypeEquivalenceS

open «Type» TypeVarLocallyClosed Environment in
theorem TypeEquivalence.preserve_lc (h: [[ Δ ⊢ A ≡ B ]]): A.TypeVarLocallyClosed ↔ B.TypeVarLocallyClosed := by
  induction h
  case eta Alc => exact ⟨λ _ => Alc, λ _ => .lam <| .app Alc.weaken <| .var_bound Nat.one_pos⟩
  case lamApp Δ B K A BkiK =>
    refine ⟨λ (.app (.lam _) _) => ?_, λ A'B'lc => ?_⟩
    . apply Type_open_dec <;> simp_all
    . have Blc := BkiK.TypeVarLocallyClosed_of
      have ⟨a, nin⟩ := A.freeTypeVars.exists_fresh
      rw [<- Type.TypeVar_subst_intro_of_not_mem_freeTypeVars (a := a) (by simp_all)] at A'B'lc
      have Abody := A'B'lc.TypeVar_subst_drop
      apply TypeVar_close_inc (a := a) at Abody
      rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Abody
      exact Abody.lam.app Blc
  case listAppList A Δ n B Alc =>
    refine ⟨λ (.listApp Alc (.list Blc)) => .list λ T Tin => ?_, λ (.list ABlc) => .listApp Alc (.list ?_)⟩
    . have ⟨i, iltn, Teq⟩ := Std.Range.mem_of_mem_map Tin; subst Teq
      exact Alc.app <| Blc _ (Std.Range.mem_map_of_mem iltn)
    . cases n
      . case zero => simp [Std.Range.map, Std.Range.toList]
      . case succ n _ =>
        simp_all [Std.Range.mem_map_of_mem, Std.Range.mem_of_mem_toList]
        intro i iltSn
        match ABlc i iltSn with | .app _ Blc => exact Blc
  case listAppComp A₀lc A₁ki =>
    refine ⟨
      λ (.listApp A₀lc (.listApp A₁lc Blc)) =>
        A₀lc.weaken.app (A₁lc.weaken.app (.var_bound Nat.one_pos)) |>.lam |>.listApp Blc,
      λ (.listApp (.lam _) Blc) => A₀lc.listApp <| A₁ki.TypeVarLocallyClosed_of.listApp Blc
    ⟩
  case lam Δ K A B I AB ih =>
    refine ⟨λ (.lam Alc) => ?_, λ (.lam Blc) => ?_⟩
    . have ⟨a, nin⟩ := (I ++ B.freeTypeVars).exists_fresh
      have Bbody := ih a (by simp_all) |>.1 Alc.strengthen |>.TypeVar_close_inc (a := a)
      rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Bbody
      exact Bbody.lam
    . have ⟨a, nin⟩ := (I ++ A.freeTypeVars).exists_fresh
      have Abody := ih a (by simp_all) |>.2 Blc.strengthen |>.TypeVar_close_inc (a := a)
      rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Abody
      exact Abody.lam
  case scheme Δ K A B I AB ih =>
    refine ⟨λ (.forall Alc) => ?_, λ (.forall Blc) => ?_⟩
    . have ⟨a, nin⟩ := (I ++ B.freeTypeVars).exists_fresh
      have Bbody := ih a (by simp_all) |>.1 Alc.strengthen |>.TypeVar_close_inc (a := a)
      rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Bbody
      exact Bbody.forall
    . have ⟨a, nin⟩ := (I ++ A.freeTypeVars).exists_fresh
      have Abody := ih a (by simp_all) |>.2 Blc.strengthen |>.TypeVar_close_inc (a := a)
      rw [TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars (by simp_all)] at Abody
      exact Abody.forall
  case list ih =>
    constructor
    · intro Alc
      let .list Alc' := Alc
      apply TypeVarLocallyClosed.list
      intro A mem
      rcases Std.Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
      exact ih _ mem' |>.mp <| Alc' _ <| Std.Range.mem_map_of_mem mem'
    · intro Blc
      let .list Blc' := Blc
      apply TypeVarLocallyClosed.list
      intro A mem
      rcases Std.Range.mem_of_mem_map mem with ⟨_, mem', rfl⟩
      exact ih _ mem' |>.mpr <| Blc' _ <| Std.Range.mem_map_of_mem mem'
  all_goals
    set_option aesop.dev.statefulForward false in
    aesop (add safe forward modus_ponens_open, safe forward Std.Range.mem_of_mem_toList, safe TypeVarLocallyClosed, unsafe cases TypeVarLocallyClosed)

open Environment in
theorem TypeEquivalence.TypeEquivalenceS_of (h: [[Δ ⊢ A ≡ B]]) (Alc: A.TypeVarLocallyClosed) (wf: [[ ⊢ Δ ]]) : [[Δ ⊢ A ≡ₛ B]] := by
  induction h
  . case refl => exact .base .refl
  · case eta A'lc => exact .base <| .eta A'lc
  . case lamApp BkiK => exact .base (.lamApp BkiK)
  . case listAppList Alc_ => exact .base (.listAppList Alc_)
  . case listAppId Alc_ => exact .base (.listAppId Alc_)
  . case listAppComp A₀lc A₁lc => exact .base (.listAppComp A₀lc A₁lc)
  . case lam Δ K A B I h ih =>
    have ⟨a, nin⟩ := I ++ Δ.typeVarDom ++ A.freeTypeVars ++ B.freeTypeVars |>.exists_fresh
    have wf' : [[ ⊢ Δ, a:K ]] := wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom])
    have Abody := match Alc with | .lam Abody => Abody
    specialize ih a (by simp_all) Abody.strengthen wf'
    exact .lam_intro_ex a (by simp_all) ih wf' Abody
  . case app A1 A2 B1 B2 h1 h2 ih1 ih2 =>
    match Alc with | .app A1lc B1lc => exact ih1 A1lc wf |>.app <| ih2 B1lc wf
  . case scheme Δ K A B I h ih =>
    have ⟨a, nin⟩ := I ++ Δ.typeVarDom ++ A.freeTypeVars ++ B.freeTypeVars |>.exists_fresh
    have wf' : [[ ⊢ Δ, a:K ]] := wf.typeVarExt (by simp_all [TypeVarNotInDom, TypeVarInDom])
    have Abody := match Alc with | .forall Abody => Abody
    specialize ih a (by simp_all) Abody.strengthen wf'
    exact .scheme_intro_ex a (by simp_all) ih wf' Abody
  . case arr ih1 ih2 =>
    match Alc with | .arr A1lc B1lc => exact ih1 A1lc wf |>.arr <| ih2 B1lc wf
  . case list n Δ A B h ih =>
    clear h
    have : ([:n].map fun i => B i) = ([:n - n].map fun i => A i) ++ [n - n:n].map fun i => B i := by
      have : ([:0].map fun i => A i) = [] := by
        rw [Std.Range.map, Std.Range.toList, if_neg nofun, List.map_nil]
      rw [Nat.sub_self, this, List.nil_append]
    rw [this]
    generalize neqm : n = m
    let nlem := Nat.le_refl n
    rw (occs := .pos [3, 5]) [← neqm]
    rw [neqm] at ih Alc
    cases Alc; case list Alc =>
    rw (occs := .pos [2]) [neqm] at nlem
    clear neqm this
    induction n with
    | zero =>
      rw [Nat.sub_zero]
      rw (occs := .pos [3]) [Std.Range.map]
      rw [Std.Range.toList, if_neg (Nat.not_lt_of_le Nat.le.refl), List.map_nil, List.append_nil]
      exact .base <| .refl
    | succ i ih' =>
      generalize A'eq : A (m - (i + 1)) = A', B'eq : B (m - (i + 1)) = B' at *
      let ih'' := ih (m - (i + 1)) (by simp_all [Membership.mem]; omega)
        (Alc _ (Std.Range.mem_map_of_mem (i := m - (i + 1)) (by simp_all [Membership.mem]; omega)))
        wf
      specialize ih' <| Nat.le_of_add_right_le nlem
      rw [A'eq, B'eq] at ih''
      rw [Std.Range.map, ← Std.Range.map_append (Nat.zero_le _) (Nat.sub_le _ i),
          ← Std.Range.map, ← Std.Range.map, Std.Range.map_eq_snoc_of_lt (by omega), Nat.sub_sub,
          List.append_assoc, List.singleton_append, A'eq] at ih' ⊢
      rw [List.append_assoc, List.singleton_append] at ih'
      rw (occs := .pos [4]) [Std.Range.map_eq_cons_of_lt (by omega)]
      rw [B'eq]
      rw (occs := .pos [3]) [Nat.sub_add_eq]
      rw [Nat.sub_add_cancel (by omega)]
      clear A'eq B'eq
      apply TypeEquivalenceS.trans ih'
      clear ih'
      induction ih'' with
      | base h =>
        refine .base <| .list' _ _ (by simp_all) (λ _ _ mem => ?_)
        match Std.Range.mem_zip_map_append_cons mem with
        | .inl ⟨_, _, Aeq, Beq⟩ =>
          subst Aeq Beq
          refine .refl
        | .inr (.inl ⟨Aeq, Beq⟩) =>
          subst Aeq Beq
          exact h
        | .inr (.inr ⟨_, _, Aeq, Beq⟩) =>
          subst Aeq Beq
          refine .refl
      | symm h =>
        refine .symm <| .list' _ _ (by simp_all) (λ _ _ mem => ?_)
        match Std.Range.mem_zip_map_append_cons mem with
        | .inl ⟨_, _, Aeq, Beq⟩ =>
          subst Aeq Beq
          refine .refl
        | .inr (.inl ⟨Aeq, Beq⟩) =>
          subst Aeq Beq
          exact h
        | .inr (.inr ⟨_, _, Aeq, Beq⟩) =>
          subst Aeq Beq
          refine .refl
      | trans h h' ih'' ih''' =>
        exact .trans ih'' ih'''
  . case listApp ih1 ih2 =>
    match Alc with | .listApp A1lc B1lc => exact ih1 A1lc wf |>.listApp <| ih2 B1lc wf
  . case prod Δ A B h ih => match Alc with | .prod Alc => exact ih Alc wf |>.prod
  . case sum ih => match Alc with | .sum Alc => exact ih Alc wf |>.sum
  . case symm _ _ _ h ih => exact ih (h.preserve_lc.2 Alc) wf |>.sym
  . case trans _ _ _ _ AB BC ih1 ih2 =>
    exact ih1 Alc wf |>.trans <| ih2 (AB.preserve_lc.1 Alc) wf

namespace TypeEquivalence

-- theorem weakening (equiv: [[ Δ, Δ'' ⊢ A ≡ B ]]) (Alc: A.TypeVarLocallyClosed) (wf: [[ ⊢ Δ, Δ'' ]]) (wf': [[ ⊢ Δ, Δ', Δ'' ]]) : [[ Δ, Δ', Δ'' ⊢ A ≡ B ]] :=
--   equiv.EqParallelReduction_of Alc wf |>.weakening wf'.EnvironmentTypeWellFormedness_of |>.TypeEquivalence_of wf'

-- theorem subst' {A T T' : «Type»} (equiv : [[ Δ, a: K, Δ' ⊢ T ≡ T' ]]) (Tlc: T.TypeVarLocallyClosed) (wf: [[ ⊢ Δ, a: K, Δ' ]]) (kindA: [[ Δ ⊢ A: K ]]) : [[ Δ, Δ'[A/a] ⊢ T[A/a] ≡ T'[A/a] ]] :=
--   equiv.EqParallelReduction_of Tlc wf |>.subst_out' wf kindA |>.TypeEquivalence_of <| wf.TypeVar_subst kindA

-- TODO this is not dt so properties on typing apparently have nothing to do with terms in env
theorem TermVar_drop (equiv: [[ Δ, x: T, Δ'' ⊢ A ≡ B ]]): [[ Δ, Δ'' ⊢ A ≡ B ]] := by
  generalize Δ_eq : [[ (Δ, x: T, Δ'') ]] = Δ' at equiv
  induction equiv generalizing Δ'' <;> subst Δ_eq
  case lam K A B I AB ih =>
    refine .lam I (λ a nin => ?_)
    exact @ih a nin [[ Δ'', a: K ]] rfl
  case scheme K A B I AB ih =>
    refine .scheme I (λ a nin => ?_)
    exact @ih a nin [[ Δ'', a: K ]] rfl
  case listAppComp A₀lc A₁ki => exact .listAppComp A₀lc A₁ki.TermVar_drop
  all_goals aesop (add unsafe constructors TypeEquivalence, safe forward Kinding.TermVar_drop)

local instance : Inhabited «Type» where
  default := .list []

theorem listAppEmptyL (Alc : A.TypeVarLocallyClosed) : [[Δ ⊢ A ⟦{ }⟧ ≡ { }]] := by
  let B (i : Nat) := [[{ }]]
  rw [← Std.Range.map_get!_eq (as := []), List.length_nil]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B i
    nomatch mem
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B@i]]
    nomatch mem
  )]
  exact listAppList Alc

theorem listAppEmptyR (Alc : A.TypeVarLocallyClosed) : [[Δ ⊢ { } ≡ A ⟦{ }⟧]] := by
  let B (i : Nat) := [[{ }]]
  rw [← Std.Range.map_get!_eq (as := []), List.length_nil]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B@i]]
    nomatch mem
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B i
    nomatch mem
  )]
  exact symm <| listAppList Alc

theorem listAppSingletonL (Alc : A.TypeVarLocallyClosed) : [[Δ ⊢ A ⟦{B}⟧ ≡ {A B}]] := by
  let B' (i : Nat) := B
  rw [← Std.Range.map_get!_eq (as := [_]), ← Std.Range.map_get!_eq (as := [ [[A B]]])]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B' i
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B'@i]]
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  exact listAppList Alc

theorem listAppSingletonR (Alc: A.TypeVarLocallyClosed) : [[Δ ⊢ {A B} ≡ A ⟦{B}⟧]] := by
  let B' (i : Nat) := B
  rw [← Std.Range.map_get!_eq (as := [_]), ← Std.Range.map_get!_eq (as := [B])]
  rw (occs := .pos [1]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = [[A B'@i]]
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
    intro i mem
    show _ = B' i
    cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
    dsimp [B']
    rw [List.get!_cons_zero]
  )]
  exact symm <| listAppList Alc

theorem listSingleton (AequB : [[Δ ⊢ A ≡ B]]) : [[Δ ⊢ {A} ≡ {B}]] := by
  let A' (i : Nat) := A
  let B' (i : Nat) := B
  rw [← Std.Range.map_get!_eq (as := [_]), List.length_singleton,
      Std.Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = A' i
      cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
      dsimp [A']
      rw [List.get!_cons_zero]
  ), ← Std.Range.map_get!_eq (as := [_]), List.length_singleton]
  rw (occs := .pos [2]) [Std.Range.map_eq_of_eq_of_mem'' (by
      intro i mem
      show _ = B' i
      cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
      dsimp [B']
      rw [List.get!_cons_zero]
  )]
  apply list
  intro i mem
  cases Nat.eq_of_le_of_lt_succ mem.lower mem.upper
  dsimp [A', B']
  exact AequB

end TypeEquivalence

end TabularTypeInterpreter.«F⊗⊕ω»
