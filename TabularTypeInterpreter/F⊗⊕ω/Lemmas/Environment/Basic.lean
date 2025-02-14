import Aesop
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment

namespace TabularTypeInterpreter.«F⊗⊕ω»

namespace Environment

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

theorem append_type_assoc {Δ Δ': Environment} : [[ (Δ , ((ε , a : K) , Δ')) ]] = [[ (Δ , a : K) , Δ' ]] := by
  induction Δ' generalizing Δ <;> simp_all [append]

theorem append_term_assoc {Δ Δ': Environment} : [[ (Δ , ((ε , x : T) , Δ')) ]] = [[ (Δ , x : T) , Δ' ]] := by
  induction Δ' generalizing Δ <;> simp_all [append]

theorem typeVarDom_TypeVar_subst {Δ: Environment} : (Δ.TypeVar_subst a A).typeVarDom = Δ.typeVarDom  := by
  induction Δ <;> simp_all [TypeVar_subst, typeVarDom]

theorem append_typeExt_assoc {Δ Δ': Environment} : [[ (Δ, Δ'), a: K ]] = [[ (Δ, (Δ', a: K)) ]] := by simp_all [append]

theorem append_termExt_assoc {Δ Δ': Environment} : [[ (Δ, Δ'), x: T ]] = [[ (Δ, (Δ', x: T)) ]] := by simp_all [append]

theorem typeExt_subst {Δ: Environment} : (Δ.TypeVar_subst a K).typeExt a' K' = (Δ.typeExt a' K').TypeVar_subst a K := by
  induction Δ <;> simp_all [TypeVar_subst, typeExt]

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
namespace TypeVarInEnvironment

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

theorem TypeVar_subst: [[ a: K ∈ Δ[A/a'] ]] ↔ [[ a: K ∈ Δ ]] := by
  induction Δ <;>
    aesop (add norm Environment.TypeVar_subst, unsafe cases TypeVarInEnvironment, unsafe constructors TypeVarInEnvironment)

end TypeVarInEnvironment

-- TODO I need these definitions to prove Type lemma
namespace EnvironmentWellFormedness
open Environment in
theorem append_typeVar_fresh_r: [[ ⊢ Δ, Δ' ]] → a ∈ Δ.typeVarDom → a ∉ Δ'.typeVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentWellFormedness, norm typeVarDom, norm typeVarDom_append, norm TypeVarNotInDom, norm TypeVarInDom)

open Environment in
theorem append_typeVar_fresh_l : [[ ⊢ Δ, Δ' ]] → ∀a ∈ Δ'.typeVarDom, a ∉ Δ.typeVarDom := by
  intro wf
  induction Δ' <;> aesop (add safe cases EnvironmentWellFormedness, norm typeVarDom, norm typeVarDom_append, norm TypeVarNotInDom, norm TypeVarInDom)
end EnvironmentWellFormedness

end TabularTypeInterpreter.«F⊗⊕ω»
