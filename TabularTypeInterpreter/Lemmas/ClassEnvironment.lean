import Aesop
import TabularTypeInterpreter.Semantics.ClassEnvironment
import TabularTypeInterpreter.Theorems.Kind

namespace TabularTypeInterpreter

open Std

namespace ClassEnvironment

theorem TCDom_append : (append Γc Γc').TCDom = Γc'.TCDom ++ Γc.TCDom := by
  match Γc' with
  | empty => rw [append, TCDom, List.nil_append]
  | ext .. => rw [append, TCDom, TCDom_append, TCDom, List.cons_append]

theorem methodDom_append : (append Γc Γc').methodDom = Γc'.methodDom ++ Γc.methodDom := by
  match Γc' with
  | empty => rw [append, methodDom, List.nil_append]
  | ext .. => rw [append, methodDom, methodDom_append, methodDom, List.cons_append]

namespace In

theorem ne_of_TCNotInDom {TC} (γcin : [[γc ∈ Γc]]) (TCnin : [[TC ∉ dom(Γc)]]) : TC ≠ γc.2 :=
  match γcin with
  | .head => List.ne_of_not_mem_cons TCnin
  | .ext γcin' .. => γcin'.ne_of_TCNotInDom <| List.not_mem_of_not_mem_cons TCnin

theorem ne_of_MethodNotInDom (γcin : [[γc ∈ Γc]]) (mnin : [[m ∉ dom(Γc)]]) : m ≠ γc.4 :=
  match γcin with
  | .head => List.ne_of_not_mem_cons mnin
  | .ext γcin' .. => γcin'.ne_of_MethodNotInDom <| List.not_mem_of_not_mem_cons mnin

theorem deterministic (γc₀in : [[γc₀ ∈ Γc]]) (γc₁in : [[γc₁ ∈ Γc]]) (eq : γc₀.2 = γc₁.2)
  : γc₀ = γc₁ := by
  cases γc₀in
  · case head =>
    cases γc₁in
    · case head => rfl
    · case ext ne _ _ =>
      cases eq
      nomatch ne
  · case ext TC' _ _ _ _ _ _ _ _ γc₀in' ne _ =>
    generalize γceq : ClassEnvironmentEntry.mk _ TC' .. = γc at *
    cases γc₁in
    · case head =>
      cases eq
      cases γceq
      nomatch ne
    · case ext γc₁in' =>
      exact γc₀in'.deterministic γc₁in' eq

end In

local instance : Inhabited TypeClass where
  default := .zero
in
local instance : Inhabited ClassEnvironmentEntrySuper where
  default := .mk default <| .list [] none
in
local instance : Inhabited «F⊗⊕ω».Type where
  default := .list [] none
in
theorem WellFormedness.In_append_inl (ΓcΓc'w : [[⊢c Γc, Γc']]) (γcin : [[γc ∈ Γc]])
  : [[γc ∈ Γc, Γc']] := by
  match Γc' with
  | .empty => exact γcin
  | .ext .. =>
    cases ΓcΓc'w
    case ext ΓcΓc''w TCnin mnin _ _ =>
    have := ΓcΓc''w.In_append_inl γcin
    let .mk TCₛAₛ .. := γc
    rw [← Range.map_get!_eq (as := TCₛAₛ)] at this ⊢
    rw [TCNotInDom, TCDom_append] at TCnin
    let ⟨_, TCninΓc⟩ := List.not_mem_append'.mp TCnin
    rw [MethodNotInDom, methodDom_append] at mnin
    let ⟨_, mninΓc⟩ := List.not_mem_append'.mp mnin
    exact this.ext (γcin.ne_of_TCNotInDom TCninΓc).symm (γcin.ne_of_MethodNotInDom mninΓc).symm

end ClassEnvironment

theorem TypeScheme.KindingAndElaboration.class_weakening (σke : [[Γc; Γ ⊢ σ : κ ⇝ A]])
  (ΓcΓc'w : [[⊢c Γc, Γc']]) : [[Γc, Γc'; Γ ⊢ σ : κ ⇝ A]] := by
  induction σke
  case scheme I _ κ₀e ih => exact scheme I (ih · · ΓcΓc'w) κ₀e
  case lift I _ κ₀e _ τih ρih => exact lift I (τih · · ΓcΓc'w) κ₀e (ρih ΓcΓc'w)
  case tc γcin _ ih => exact tc (ΓcΓc'w.In_append_inl γcin) (ih ΓcΓc'w)
  case all I _ κ₀e _ ψih ρih => exact all I (ψih · · ΓcΓc'w) κ₀e (ρih ΓcΓc'w)
  case ind I₀ I₁ _ κe _ _ ρih Bₗih Bᵣih =>
    exact ind I₀ I₁ (ρih ΓcΓc'w) κe (Bₗih · · · · · · · · ΓcΓc'w) (Bᵣih · · · · ΓcΓc'w)
  all_goals aesop (add safe constructors KindingAndElaboration)

namespace ClassEnvironment

namespace WellFormedness

theorem ext_eliml (Γcγcw : [[⊢c Γc, γc]]) : [[⊢c Γc]] :=
  let .ext Γcw .. := Γcγcw
  Γcw

theorem In_inversion {TC} (Γcw : [[⊢c Γc]])
  (γcin : [[(</ TC'@i a ⇝ A'@i // i in [:n] /> ⇒ TC a : κ) ↦ m : σ ⇝ A ∈ Γc]])
  : ∃ K, [[⊢ κ ⇝ K]] ∧ (∀ a, [[Γc; ε, a : κ ⊢ σ^a : * ⇝ A^a]]) ∧ (∀ a, [[ε, a : K ⊢ A^a : *]]) ∧
    (∀ a, ∀ i ∈ [:n], [[Γc; ε, a : κ ⊢ TC'@i a : C ⇝ A'@i^a]]) ∧
    (∀ a, ∀ i ∈ [:n], [[ε, a : K ⊢ A'@i^a : *]]) := by
  generalize γceq : ClassEnvironmentEntry.mk .. = γc at γcin
  match γcin with
  | .head =>
    let Γcw@(ext _ _ _ κe σke Ake TCₛke Aₛki) := Γcw
    injection γceq with TCₛAₛeq TCeq κeq meq σeq Aeq
    let length_eq : List.length (Range.map ..) = List.length _ := by rw [TCₛAₛeq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at length_eq
    cases length_eq
    cases κeq
    cases σeq
    cases Aeq
    apply Exists.intro _
    constructor
    · exact κe
    · constructor
      · exact (σke · |>.class_weakening Γcw (Γc' := .ext .empty _))
      · constructor
        · exact Ake
        · constructor
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := ClassEnvironmentEntrySuper.mk.inj <|
              Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [TCₛeq, Aₛeq]
            exact TCₛke i mem a |>.class_weakening Γcw (Γc' := .ext .empty _)
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := ClassEnvironmentEntrySuper.mk.inj <|
              Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [Aₛeq]
            exact Aₛki i mem a
  | .ext TCin' TCneTC' mnem' (TC'' := TC'') =>
    generalize ClassEnvironmentEntry.mk _ TC'' .. = γc at *
    let Γcw@(ext Γcw' ..) := Γcw
    let ⟨_, κe, σke, Aki, TCₛke, Aₛki⟩ := Γcw'.In_inversion TCin'
    injection γceq with TCₛAₛeq TCeq κeq meq σeq Aeq
    let length_eq : List.length (Range.map ..) = List.length _ := by rw [TCₛAₛeq]
    rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList] at length_eq
    cases length_eq
    cases κeq
    cases σeq
    cases Aeq
    apply Exists.intro _
    constructor
    · exact κe
    · constructor
      · exact (σke · |>.class_weakening Γcw (Γc' := .ext .empty _))
      · constructor
        · exact Aki
        · constructor
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := ClassEnvironmentEntrySuper.mk.inj <|
              Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [TCₛeq, Aₛeq]
            exact TCₛke a i mem |>.class_weakening Γcw (Γc' := .ext .empty _)
          · intro a i mem
            let ⟨TCₛeq, Aₛeq⟩ := ClassEnvironmentEntrySuper.mk.inj <|
              Range.eq_of_mem_of_map_eq TCₛAₛeq i mem
            rw [Aₛeq]
            exact Aₛki a i mem

end WellFormedness

end ClassEnvironment

end TabularTypeInterpreter
