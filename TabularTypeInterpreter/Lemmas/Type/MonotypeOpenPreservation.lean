import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.Lemmas.TypeEnvironment
import TabularTypeInterpreter.Theorems.Kind
import TabularTypeInterpreter.Theorems.Type.KindingAndElaboration

namespace TabularTypeInterpreter

open Std

namespace «F⊗⊕ω».Type

private
theorem contain_evidence_eq_inversion (aninA : a ∉ A.freeTypeVars)
  (eq : A.TypeVar_open a n = [[⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₀⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀⟧)) → ⊕ (a$0 ⟦A₁⟧)}]])
  : ∃ A₀' A₁', A₀ = A₀'.TypeVar_open a (n + 1) ∧ A₁ = A₁'.TypeVar_open a (n + 1) ∧
    A = [[⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₁'⟧)) → ⊗ (a$0 ⟦A₀'⟧), ∀ a : K ↦ *. (⊕ (a$0 ⟦A₀'⟧)) → ⊕ (a$0 ⟦A₁'⟧)}]] := by
  cases A <;> rw [TypeVar_open] at *
  case prod =>
    rename «Type» => A
    let eq' := prod.inj eq
    cases A <;> rw [TypeVar_open] at *
    case list =>
      let eq'' := list.inj eq'
      rw [List.mapMem_eq_map] at *
      rename List _ => As
      match As with
      | [] => nomatch eq''
      | A₀' :: As' =>
        rw [List.map_cons] at *
        match As' with
        | [] =>
          generalize A₀'.TypeVar_open a n = A₀'' at *
          nomatch eq''
        | A₁' :: As'' =>
          rw [List.map_cons] at *
          match As'' with
          | A₂' :: _ =>
            generalize A₀'.TypeVar_open a n = A₀'' at *
            generalize A₁'.TypeVar_open a n = A₁'' at *
            generalize A₂'.TypeVar_open a n = A₂'' at *
            nomatch eq''
          | [] =>
            rw [List.map_nil] at *
            let ⟨eq₀, eq'''⟩ := List.cons_eq_cons.mp eq''
            let eq₁ := List.singleton_inj.mp eq'''
            cases A₀' <;> rw [TypeVar_open] at *
            case «forall» =>
              let ⟨Keq, eq₀'⟩ := forall.inj eq₀
              cases Keq
              rename «Type» => A₀'
              cases A₀' <;> rw [Type.TypeVar_open] at *
              case arr =>
                rename_i A₀₀' A₀₁'
                cases A₀₀' <;> rw [Type.TypeVar_open] at *
                case prod =>
                  rename «Type» => A₀₀'
                  cases A₀₀' <;> rw [Type.TypeVar_open] at *
                  case listApp =>
                    rename_i A₀₀₀' A₀₀₁'
                    cases A₀₀₀' <;> rw [Type.TypeVar_open] at *
                    case var =>
                      rename «F⊗⊕ω».TypeVar => a'
                      cases a'
                      case bound =>
                        rename Nat => n'
                        match n' with
                        | 0 =>
                          rw [if_neg (nomatch ·)] at *
                          cases A₀₁' <;> rw [Type.TypeVar_open] at *
                          case prod =>
                            rename «Type» => A₀₀'
                            cases A₀₀' <;> rw [Type.TypeVar_open] at *
                            case listApp =>
                              rename_i A₀₁₀' A₀₁₁'
                              cases A₀₁₀' <;> rw [Type.TypeVar_open] at *
                              case var =>
                                rename «F⊗⊕ω».TypeVar => a'
                                cases a'
                                case bound =>
                                  rename Nat => n'
                                  match n' with
                                  | 0 =>
                                    rw [if_neg (nomatch ·)] at *
                                    cases A₁' <;> rw [TypeVar_open] at *
                                    case «forall» =>
                                      let ⟨Keq, eq₁'⟩ := forall.inj eq₁
                                      cases Keq
                                      rename «Type» => A₁'
                                      cases A₁' <;> rw [Type.TypeVar_open] at *
                                      case arr =>
                                        rename_i A₁₀' A₁₁'
                                        cases A₁₀' <;> rw [Type.TypeVar_open] at *
                                        case sum =>
                                          rename «Type» => A₁₀'
                                          cases A₁₀' <;> rw [Type.TypeVar_open] at *
                                          case listApp =>
                                            rename_i A₁₀₀' A₁₀₁'
                                            cases A₁₀₀' <;> rw [Type.TypeVar_open] at *
                                            case var =>
                                              rename «F⊗⊕ω».TypeVar => a'
                                              cases a'
                                              case bound =>
                                                rename Nat => n'
                                                match n' with
                                                | 0 =>
                                                  rw [if_neg (nomatch ·)] at *
                                                  cases A₁₁' <;> rw [Type.TypeVar_open] at *
                                                  case sum =>
                                                    rename «Type» => A₁₀'
                                                    cases A₁₀' <;> rw [Type.TypeVar_open] at *
                                                    case listApp =>
                                                      rename_i A₁₁₀' A₁₁₁'
                                                      cases A₁₁₀' <;> rw [Type.TypeVar_open] at *
                                                      case var =>
                                                        rename «F⊗⊕ω».TypeVar => a'
                                                        cases a'
                                                        case bound =>
                                                          rename Nat => n'
                                                          match n' with
                                                          | 0 =>
                                                            rw [if_neg (nomatch ·)] at *
                                                            cases eq₀'
                                                            let ⟨eq₁₀, eq₁₁⟩ := arr.inj eq₁'
                                                            simp [freeTypeVars] at aninA
                                                            let ⟨
                                                              aninA₀₀₁',
                                                              aninA₀₁₁',
                                                              aninA₁₀₁',
                                                              aninA₁₁₁'
                                                            ⟩ := aninA
                                                            cases
                                                              TypeVar_open_inj_of_not_mem_freeTypeVars
                                                              aninA₁₀₁' aninA₀₁₁' <| And.right <|
                                                              listApp.inj <| sum.inj eq₁₀
                                                            cases
                                                              TypeVar_open_inj_of_not_mem_freeTypeVars
                                                              aninA₁₁₁' aninA₀₀₁' <| And.right <|
                                                              listApp.inj <| sum.inj eq₁₁
                                                            exact ⟨_, _, rfl, rfl, rfl⟩
                                                          | _ + 1 => split at eq₁' <;> nomatch eq₁'
                                                        all_goals nomatch eq₁'
                                                      all_goals nomatch eq₁'
                                                    all_goals nomatch eq₁'
                                                  all_goals nomatch eq₁'
                                                | _ + 1 => split at eq₁' <;> nomatch eq₁'
                                              all_goals nomatch eq₁'
                                            all_goals nomatch eq₁'
                                          all_goals nomatch eq₁'
                                        all_goals nomatch eq₁'
                                      all_goals nomatch eq₁'
                                    all_goals nomatch eq₁
                                  | _ + 1 => split at eq₀' <;> nomatch eq₀'
                                all_goals nomatch eq₀'
                              all_goals nomatch eq₀'
                            all_goals nomatch eq₀'
                          all_goals nomatch eq₀'
                        | _ + 1 => split at eq₀' <;> nomatch eq₀'
                      all_goals nomatch eq₀'
                    all_goals nomatch eq₀'
                  all_goals nomatch eq₀'
                all_goals nomatch eq₀'
              all_goals nomatch eq₀'
            all_goals nomatch eq₀
    all_goals nomatch eq
  all_goals nomatch eq

private
theorem concat_evidence_eq_inversion (aninA : a ∉ A.freeTypeVars)
  (eq : A.TypeVar_open a n = [[⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0, Bₗ, Bᵣ}]])
  : ∃ A₀' A₁' A₂' Bₗ' Bᵣ', A₀ = A₀'.TypeVar_open a (n + 1) ∧ A₁ = A₁'.TypeVar_open a (n + 1) ∧
    A₂ = A₂'.TypeVar_open a (n + 1) ∧
    Bₗ = Bₗ'.TypeVar_open a n ∧ Bᵣ = Bᵣ'.TypeVar_open a n ∧
    A = [[⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀'⟧)) → (⊗ (a$0 ⟦A₁'⟧)) → ⊗ (a$0 ⟦A₂'⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀'⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁'⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂'⟧)) → aₜ$0, Bₗ', Bᵣ'}]] := by
  cases A <;> rw [TypeVar_open] at *
  case prod =>
    rename «Type» => A
    let eq' := prod.inj eq
    cases A <;> rw [TypeVar_open] at *
    case list =>
      let eq'' := list.inj eq'
      rw [List.mapMem_eq_map] at *
      rename List _ => As
      match As with
      | [] => nomatch eq''
      | A₀' :: As' =>
        rw [List.map_cons] at *
        match As' with
        | [] =>
          generalize A₀'.TypeVar_open a n = A₀'' at *
          nomatch eq''
        | A₁' :: As'' =>
          rw [List.map_cons] at *
          match As'' with
          | [] =>
            generalize A₀'.TypeVar_open a n = A₀'' at *
            generalize A₁'.TypeVar_open a n = A₁'' at *
            nomatch eq''
          | Bₗ' :: As'' =>
            rw [List.map_cons] at *
            match As'' with
            | [] =>
              generalize A₀'.TypeVar_open a n = A₀'' at *
              generalize A₁'.TypeVar_open a n = A₁'' at *
              generalize Bₗ'.TypeVar_open a n = Bₗ'' at *
              nomatch eq''
            | Bᵣ' :: As'' =>
              rw [List.map_cons] at *
              match As'' with
              | A₅' :: As'' =>
                generalize A₀'.TypeVar_open a n = A₀'' at *
                generalize A₁'.TypeVar_open a n = A₁'' at *
                generalize Bₗ'.TypeVar_open a n = Bₗ'' at *
                generalize Bᵣ'.TypeVar_open a n = Bᵣ'' at *
                generalize A₅'.TypeVar_open a n = A₅'' at *
                nomatch eq''
              | [] =>
                rw [List.map_nil] at *
                let ⟨eq₀, eq'''⟩ := List.cons_eq_cons.mp eq''
                let ⟨eq₁, eq''''⟩ := List.cons_eq_cons.mp eq'''
                cases A₀' <;> rw [TypeVar_open] at *
                case «forall» =>
                  let ⟨Keq, eq₀'⟩ := forall.inj eq₀
                  cases Keq
                  rename «Type» => A₀'
                  cases A₀' <;> rw [TypeVar_open] at *
                  case arr =>
                    rename_i A₀₀' A₀₁'
                    cases A₀₀' <;> rw [Type.TypeVar_open] at *
                    case prod =>
                      rename «Type» => A₀₀'
                      cases A₀₀' <;> rw [Type.TypeVar_open] at *
                      case listApp =>
                        rename_i A₀₀₀' A₀₀₁'
                        cases A₀₀₀' <;> rw [Type.TypeVar_open] at *
                        case var =>
                          rename «F⊗⊕ω».TypeVar => a'
                          cases a'
                          case bound =>
                            rename Nat => n'
                            match n' with
                            | 0 =>
                              rw [if_neg (nomatch ·)] at *
                              cases A₀₁' <;> rw [Type.TypeVar_open] at *
                              case arr =>
                                rename_i A₀₁₀' A₀₁₁'
                                cases A₀₁₀' <;> rw [Type.TypeVar_open] at *
                                case prod =>
                                  rename «Type» => A₀₁₀'
                                  cases A₀₁₀' <;> rw [Type.TypeVar_open] at *
                                  case listApp =>
                                    rename_i A₀₁₀₀' A₀₁₀₁'
                                    cases A₀₁₀₀' <;> rw [Type.TypeVar_open] at *
                                    case var =>
                                      rename «F⊗⊕ω».TypeVar => a'
                                      cases a'
                                      case bound =>
                                        rename Nat => n'
                                        match n' with
                                        | 0 =>
                                          rw [if_neg (nomatch ·)] at *
                                          cases A₀₁₁' <;> rw [Type.TypeVar_open] at *
                                          case prod =>
                                            rename «Type» => A₀₁₁'
                                            cases A₀₁₁' <;> rw [Type.TypeVar_open] at *
                                            case listApp =>
                                              rename_i A₀₁₁₀' A₀₁₁₁'
                                              cases A₀₁₁₀' <;> rw [Type.TypeVar_open] at *
                                              case var =>
                                                rename «F⊗⊕ω».TypeVar => a'
                                                cases a'
                                                case bound =>
                                                  rename Nat => n'
                                                  match n' with
                                                  | 0 =>
                                                    rw [if_neg (nomatch ·)] at *
                                                    cases A₁' <;> rw [TypeVar_open] at *
                                                    case «forall» =>
                                                      let ⟨Keq, eq₁'⟩ := forall.inj eq₁
                                                      cases Keq
                                                      rename «Type» => A₁'
                                                      cases A₁' <;> rw [TypeVar_open] at *
                                                      case «forall» =>
                                                        let ⟨Keq, eq₁''⟩ := forall.inj eq₁'
                                                        cases Keq
                                                        rename «Type» => A₁'
                                                        cases A₁' <;> rw [TypeVar_open] at *
                                                        case arr =>
                                                          rename_i A₁₀' A₁₁'
                                                          cases A₁₀' <;> rw [TypeVar_open] at *
                                                          case arr =>
                                                            rename_i A₁₀₀' A₁₀₁'
                                                            cases A₁₀₀' <;> rw [TypeVar_open] at *
                                                            case sum =>
                                                              rename «Type» => A₁₀₀'
                                                              cases A₁₀₀' <;> rw [TypeVar_open] at *
                                                              case listApp =>
                                                                rename_i A₁₀₀₀' A₁₀₀₁'
                                                                cases A₁₀₀₀' <;> rw [Type.TypeVar_open] at *
                                                                case var =>
                                                                  rename «F⊗⊕ω».TypeVar => a'
                                                                  cases a'
                                                                  case bound =>
                                                                    rename Nat => n'
                                                                    match n' with
                                                                    | 1 =>
                                                                      rw [if_neg (nomatch ·)] at *
                                                                      cases A₁₀₁' <;> rw [Type.TypeVar_open] at *
                                                                      case var =>
                                                                        rename «F⊗⊕ω».TypeVar => a'
                                                                        cases a'
                                                                        case bound =>
                                                                          rename Nat => n'
                                                                          match n' with
                                                                          | 0 =>
                                                                            rw [if_neg (nomatch ·)] at *
                                                                            cases A₁₁' <;> rw [Type.TypeVar_open] at *
                                                                            case arr =>
                                                                              rename_i A₁₁₀' A₁₁₁'
                                                                              cases A₁₁₀' <;> rw [TypeVar_open] at *
                                                                              case arr =>
                                                                                rename_i A₁₁₀₀' A₁₁₀₁'
                                                                                cases A₁₁₀₀' <;> rw [TypeVar_open] at *
                                                                                case sum =>
                                                                                  rename «Type» => A₁₁₀₀'
                                                                                  cases A₁₁₀₀' <;> rw [TypeVar_open] at *
                                                                                  case listApp =>
                                                                                    rename_i A₁₁₀₀₀' A₁₁₀₀₁'
                                                                                    cases A₁₁₀₀₀' <;> rw [Type.TypeVar_open] at *
                                                                                    case var =>
                                                                                      rename «F⊗⊕ω».TypeVar => a'
                                                                                      cases a'
                                                                                      case bound =>
                                                                                        rename Nat => n'
                                                                                        match n' with
                                                                                        | 1 =>
                                                                                          rw [if_neg (nomatch ·)] at *
                                                                                          cases A₁₁₀₁' <;> rw [Type.TypeVar_open] at *
                                                                                          case var =>
                                                                                            rename «F⊗⊕ω».TypeVar => a'
                                                                                            cases a'
                                                                                            case bound =>
                                                                                              rename Nat => n'
                                                                                              match n' with
                                                                                              | 0 =>
                                                                                                rw [if_neg (nomatch ·)] at *
                                                                                                cases A₁₁₁' <;> rw [TypeVar_open] at *
                                                                                                case arr =>
                                                                                                  rename_i A₁₁₁₀' A₁₁₁₁'
                                                                                                  cases A₁₁₁₀' <;> rw [TypeVar_open] at *
                                                                                                  case sum =>
                                                                                                    rename «Type» => A₁₁₁₀'
                                                                                                    cases A₁₁₁₀' <;> rw [TypeVar_open] at *
                                                                                                    case listApp =>
                                                                                                      rename_i A₁₁₁₀₀' A₁₁₁₀₁'
                                                                                                      cases A₁₁₁₀₀' <;> rw [Type.TypeVar_open] at *
                                                                                                      case var =>
                                                                                                        rename «F⊗⊕ω».TypeVar => a'
                                                                                                        cases a'
                                                                                                        case bound =>
                                                                                                          rename Nat => n'
                                                                                                          match n' with
                                                                                                          | 1 =>
                                                                                                            rw [if_neg (nomatch ·)] at *
                                                                                                            cases A₁₁₁₁' <;> rw [Type.TypeVar_open] at *
                                                                                                            case var =>
                                                                                                              rename «F⊗⊕ω».TypeVar => a'
                                                                                                              cases a'
                                                                                                              case bound =>
                                                                                                                rename Nat => n'
                                                                                                                match n' with
                                                                                                                | 0 =>
                                                                                                                  rw [if_neg (nomatch ·)] at *
                                                                                                                  cases eq₀'
                                                                                                                  let ⟨eq₁₀, eq₁₁⟩ := arr.inj eq₁''
                                                                                                                  let ⟨eq₁₁₀, eq₁₁₁⟩ := arr.inj eq₁₁
                                                                                                                  simp [freeTypeVars] at aninA
                                                                                                                  let ⟨
                                                                                                                    aninA₀₀₁',
                                                                                                                    aninA₀₁₀₁',
                                                                                                                    aninA₀₁₁₁',
                                                                                                                    aninA₁₀₀₁',
                                                                                                                    aninA₁₁₀₀₁',
                                                                                                                    aninA₁₁₁₀₁',
                                                                                                                    aninBₗ,
                                                                                                                    aninBᵣ
                                                                                                                  ⟩ := aninA
                                                                                                                  let f := And.right <| listApp.inj <| sum.inj <| And.left <| arr.inj eq₁₀
                                                                                                                  sorry
                                                                                                                | _ + 1 => split at eq₁'' <;> nomatch eq₁''
                                                                                                              all_goals nomatch eq₁''
                                                                                                            all_goals nomatch eq₁''
                                                                                                          | 0 | _ + 2 => split at eq₁'' <;> nomatch eq₁''
                                                                                                        all_goals nomatch eq₁''
                                                                                                      all_goals nomatch eq₁''
                                                                                                    all_goals nomatch eq₁''
                                                                                                  all_goals nomatch eq₁''
                                                                                                all_goals nomatch eq₁''
                                                                                              | _ + 1 => split at eq₁'' <;> nomatch eq₁''
                                                                                            all_goals nomatch eq₁''
                                                                                          all_goals nomatch eq₁''
                                                                                        | 0 | _ + 2 => split at eq₁'' <;> nomatch eq₁''
                                                                                      all_goals nomatch eq₁''
                                                                                    all_goals nomatch eq₁''
                                                                                  all_goals nomatch eq₁''
                                                                                all_goals nomatch eq₁''
                                                                              all_goals nomatch eq₁''
                                                                            all_goals nomatch eq₁''
                                                                          | _ + 1 => split at eq₁'' <;> nomatch eq₁''
                                                                        all_goals nomatch eq₁''
                                                                      all_goals nomatch eq₁''
                                                                    | 0 | _ + 2 => split at eq₁'' <;> nomatch eq₁''
                                                                  all_goals nomatch eq₁''
                                                                all_goals nomatch eq₁''
                                                              all_goals nomatch eq₁''
                                                            all_goals nomatch eq₁''
                                                          all_goals nomatch eq₁''
                                                        all_goals nomatch eq₁''
                                                      all_goals nomatch eq₁'
                                                    all_goals nomatch eq₁
                                                  | _ + 1 => split at eq₀' <;> nomatch eq₀'
                                                all_goals nomatch eq₀'
                                              all_goals nomatch eq₀'
                                            all_goals nomatch eq₀'
                                          all_goals nomatch eq₀'
                                        | _ + 1 => split at eq₀' <;> nomatch eq₀'
                                      all_goals nomatch eq₀'
                                    all_goals nomatch eq₀'
                                  all_goals nomatch eq₀'
                                all_goals nomatch eq₀'
                              all_goals nomatch eq₀'
                            | _ + 1 => split at eq₀' <;> nomatch eq₀'
                          all_goals nomatch eq₀'
                        all_goals nomatch eq₀'
                      all_goals nomatch eq₀'
                    all_goals nomatch eq₀'
                  all_goals nomatch eq₀'
                all_goals nomatch eq₀
    all_goals nomatch eq
  all_goals nomatch eq

local instance : Inhabited «Type» where
  default := .list []
in
private
theorem tc_evidence_eq_inversion (aninA : a ∉ A.freeTypeVars)
  (A'oplc : (A'.TypeVar_open a).TypeVarLocallyClosed)
  (Aₛoplc : ∀ i ∈ [:n'], ((Aₛ i).TypeVar_open a).TypeVarLocallyClosed)
  (Blc : B.TypeVarLocallyClosed)
  (eq : A.TypeVar_open a n = [[⊗ {A'^^B, </ Aₛ@i^^B // i in [:n'] />}]])
  : ∃ A'', A' = A''.TypeVar_open a (n + 1) ∧ A = [[⊗ {A''^^B, </ Aₛ@i^^B // i in [:n'] />}]] := by
  cases A <;> rw [TypeVar_open] at *
  case prod =>
    rename «Type» => A
    let eq' := prod.inj eq
    cases A <;> rw [TypeVar_open] at *
    case list =>
      let eq'' := list.inj eq'
      rw [List.mapMem_eq_map] at *
      rename List _ => As
      match As with
      | [] => nomatch eq''
      | A'' :: As' =>
        rw [List.map_cons] at *
        let ⟨eq₀, eq₁⟩ := List.cons_eq_cons.mp eq''
        rw [← Range.map_get!_eq (as := As'), Range.map, List.map_map,
            List.map_singleton_flatten] at eq₁
        let length_eq : List.length (List.map ..) = List.length _ :=  by rw [eq₁]
        rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList,
            Nat.sub_zero, Nat.sub_zero] at length_eq
        cases length_eq
        rw [freeTypeVars, freeTypeVars, List.mapMem_eq_map] at aninA
        sorry
        -- let f := List.not_mem_flatten.mp aninA A''.freeTypeVars <| .head _
        -- let f := Range.eq_of_mem_of_map_eq eq₁
    all_goals nomatch eq
  all_goals nomatch eq

end «F⊗⊕ω».Type

open «F⊗⊕ω»

namespace TypeScheme.KindingAndElaboration

theorem weakening : [[Γc; Γ, Γ'' ⊢ σ : κ ⇝ A]] → [[Γc ⊢ Γ, Γ', Γ'' ⇝ Δ]] → [[Γc; Γ, Γ', Γ'' ⊢ σ : κ ⇝ A]] := sorry

local instance : Inhabited Monotype where
  default := .row [] none
in
local instance : Inhabited «Type» where
  default := .list []
in
set_option maxHeartbeats 2000000 in
theorem Monotype_open_preservation
  (σke : KindingAndElaboration Γc [[(Γ, a : κ₀, Γ')]] (TypeVar_open σ a m) κ₁
    (Type.TypeVar_open A a n)) (ΓaΓ'we : [[Γc ⊢ Γ, a : κ₀, Γ' ⇝ Δ]]) (aninΓ' : [[a ∉ dom(Γ')]])
  (aninσ : a ∉ σ.freeTypeVars) (aninA : a ∉ A.freeTypeVars) (τke : [[Γc; Γ ⊢ τ : κ₀ ⇝ B]])
  : KindingAndElaboration Γc [[(Γ, (Γ' [τ / a]))]] (σ.Monotype_open τ m) κ₁ (A.Type_open B n) := by
  let .qual (.mono τlc) := τke.TypeVarLocallyClosed_of
  match σ with
  | .qual γ =>
    rw [Monotype_open]
    rw [TypeVar_open] at σke
    rw [freeTypeVars] at aninσ
    match h : γ with
    | .mono τ' =>
      rw [QualifiedType.Monotype_open]
      rw [QualifiedType.TypeVar_open] at σke
      rw [QualifiedType.freeTypeVars] at aninσ
      match τ' with
      | .var _ =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case var =>
          split at σke
          · case isTrue h =>
            cases h
            split at σke
            · case isTrue h =>
              cases h
              rw [Monotype.Monotype_open, if_pos rfl, Type.Type_open, if_pos rfl]
              let .var ain := σke
              let .head := ain.append_elim_left aninΓ'
              exact τke.weakening sorry (Γ'' := .empty) (Δ := .empty)
            · case isFalse h =>
              let .var .. := σke
              rw [Type.freeTypeVars] at aninA
              nomatch List.not_mem_singleton.mp aninA
          · case isFalse h =>
            split at σke
            · case isTrue h' =>
              cases h'
              let .var .. := σke
              rw [Monotype.freeTypeVars] at aninσ
              nomatch List.not_mem_singleton.mp aninσ
            · case isFalse h' =>
              rw [Monotype.Monotype_open, if_neg h, Type.Type_open, if_neg h']
              let .var a'in := σke
              rw [Type.freeTypeVars] at aninA
              exact var <| match a'in.append_elim with
              | .inl ⟨a'inΓa, a'ninΓ'⟩ => match a'inΓa with
                | .head => nomatch List.not_mem_singleton.mp aninA
                | .typeExt _ a'inΓ => a'inΓ.append_inl a'ninΓ'.TypeVar_subst_preservation
              | .inr a'inΓ' => a'inΓ'.TypeVar_subst_preservation.append_inr
        all_goals split at σke <;> nomatch σke
      | .app φ τ'' =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case app =>
          let .app φke τ''ke := σke
          rw [Monotype.Monotype_open, Type.Type_open]
          rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at φke τ''ke
          rw [Monotype.freeTypeVars] at aninσ
          rw [Type.freeTypeVars] at aninA
          let φke' := φke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) (aninA <| List.mem_append_left _ ·) τke
          let τ''ke' := τ''ke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_right _ ·) (aninA <| List.mem_append_right _ ·) τke
          rw [Monotype_open, QualifiedType.Monotype_open] at φke' τ''ke'
          exact app φke' τ''ke'
        all_goals nomatch σke
      | .arr τ₀ τ₁ =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case arr =>
          let .arr τ₀ke τ₁ke := σke
          rw [Monotype.Monotype_open, Type.Type_open]
          rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at τ₀ke τ₁ke
          rw [Monotype.freeTypeVars] at aninσ
          rw [Type.freeTypeVars] at aninA
          let τ₀ke' := τ₀ke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) (aninA <| List.mem_append_left _ ·) τke
          let τ₁ke' := τ₁ke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_right _ ·) (aninA <| List.mem_append_right _ ·) τke
          rw [Monotype_open, QualifiedType.Monotype_open] at τ₀ke' τ₁ke'
          exact arr τ₀ke' τ₁ke'
        all_goals nomatch σke
      | .label _ =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case prod =>
          rw [Monotype.Monotype_open, Type.Type_open]
          rename «Type» => A
          cases A <;> rw [Type.TypeVar_open] at σke
          case list =>
            rw [Type.Type_open]
            rw [List.mapMem_eq_map] at σke ⊢
            rename List _ => As
            match As with
            | _ :: _ => nomatch σke
            | [] =>
              rw [List.map_nil] at σke ⊢
              let .label := σke
              exact label
          all_goals nomatch σke
        all_goals nomatch σke
      | .comm _ =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case prod =>
          rw [Monotype.Monotype_open, Type.Type_open]
          rename «Type» => A
          cases A <;> rw [Type.TypeVar_open] at σke
          case list =>
            rw [Type.Type_open]
            rw [List.mapMem_eq_map] at σke ⊢
            rename List _ => As
            match As with
            | _ :: _ => nomatch σke
            | [] =>
              rw [List.map_nil] at σke ⊢
              let .comm := σke
              exact comm
          all_goals nomatch σke
        all_goals nomatch σke
      | .row ξτs .. =>
        rw [Monotype.TypeVar_open, List.mapMem_eq_map] at σke
        generalize ξτs'eq
          : (ξτs.map fun (ξ, τ) => (ξ.TypeVar_open a m, τ.TypeVar_open a m)) = ξτs' at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .row ξ'ke uni τ'ke h' (B := B') := σke
        rw [List.map_singleton_flatten] at ξτs'eq
        cases A <;> rw [Type.TypeVar_open] at A'eq
        case list =>
          rename List _ => A
          rw [List.mapMem_eq_map, List.map_singleton_flatten] at A'eq
          let A'eq := Type.list.inj A'eq
          let ξτslength_eq : List.length (List.map ..) = List.length _ := by rw [ξτs'eq]
          let Alength_eq : List.length (List.map ..) = List.length _ := by rw [A'eq]
          rw [List.length_map, List.length_map, Range.length_toList,
              Nat.sub_zero] at ξτslength_eq Alength_eq
          let ξ' i := ξτs.get! i |>.fst.Monotype_open τ m
          let τ' i := ξτs.get! i |>.snd.Monotype_open τ m
          let A'' i := A.get! i |>.Type_open B n
          rw [Monotype.Monotype_open, List.mapMem_eq_map, ← Range.map_get!_eq (as := ξτs),
              ξτslength_eq, Range.map, List.map_map, Type.Type_open, List.mapMem_eq_map,
              ← Range.map_get!_eq (as := A), Alength_eq, Range.map, List.map_map,
              Range.map_eq_of_eq_of_mem (by
                intro i _
                show _ = (ξ' i, τ' i)
                simp only [Function.comp]
              ), ← List.map_singleton_flatten, ← Range.map,
              Range.map_eq_of_eq_of_mem (by
                intro i _
                show _ = A'' i
                simp only [Function.comp]
              ), ← List.map_singleton_flatten, ← Range.map]
          rw [← Range.map_get!_eq (as := ξτs), ξτslength_eq, Range.map, List.map_map] at ξτs'eq
          rw [Monotype.freeTypeVars, List.mapMem_eq_map] at aninσ
          let aninξ i ilt : a ∉ (ξτs.get! i).fst.freeTypeVars := by
            apply (List.not_mem_append' (xs := (ξτs.get! i).snd.freeTypeVars)).mp _ |>.right
            apply List.not_mem_flatten.mp aninσ
            apply List.mem_map.mpr
            exact ⟨_, List.get!_mem ilt, rfl⟩
          let aninτ i ilt : a ∉ (ξτs.get! i).snd.freeTypeVars := by
            apply (List.not_mem_append' (ys := (ξτs.get! i).fst.freeTypeVars)).mp _ |>.left
            apply List.not_mem_flatten.mp aninσ
            apply List.mem_map.mpr
            exact ⟨_, List.get!_mem ilt, rfl⟩
          apply row (B := fun i => ((B' i).TypeVar_close a m).Type_open B m) _ _ _ h'
          · intro i mem
            dsimp only [ξ']
            let ξike := ξ'ke i mem
            simp only at ξike
            have := Range.eq_of_mem_of_map_eq ξτs'eq i mem
            simp only [Function.comp] at this
            rw [← Prod.mk.inj this |>.left, ← QualifiedType.TypeVar_open, ← TypeVar_open] at ξike
            let Bki := ξike.soundness ΓaΓ'we .label |>.TypeVarLocallyClosed_of.weaken (n := m)
            rw [Nat.zero_add] at Bki
            rw [← Bki.TypeVar_open_TypeVar_close_id (a := a)] at ξike
            let ilt : i < ξτs.length := by rw [ξτslength_eq]; exact mem.right
            have := ξike.Monotype_open_preservation ΓaΓ'we aninΓ' (aninξ i ilt)
              Type.not_mem_freeTypeVars_TypeVar_close τke
            rw [Monotype_open, QualifiedType.Monotype_open] at this
            exact this
          · rw [List.map_singleton_flatten, funext (f := ξ') (by
              intro i
              show _ = ((fun x => x.Monotype_open τ m) ∘ (fun i => ξτs.get! i |>.fst)) i
              simp only [ξ', Function.comp]
            ), ← List.map_map]
            apply Monotype.label.Uniqueness.Monotype_open_preservation (a := a)
            rw [Range.map, List.map_singleton_flatten, Range.map_eq_of_eq_of_mem (by
              intro i mem
              have := Range.eq_of_mem_of_map_eq ξτs'eq i mem
              simp only [Function.comp] at this
              rw [← Prod.mk.inj this |>.left]
            )] at uni
            rw [List.map_map, ← Range.map, Range.map, Range.map_eq_of_eq_of_mem (by
              intro i mem
              show _ = (ξτs.get! i).fst.TypeVar_open a m
              simp only [Function.comp]
            )]
            exact uni
          · intro i mem
            dsimp only [τ', A'']
            let τike := τ'ke i mem
            simp only at τike
            have := Range.eq_of_mem_of_map_eq ξτs'eq i mem
            simp only [Function.comp] at this
            rw [← Prod.mk.inj this |>.right, ← QualifiedType.TypeVar_open, ← TypeVar_open] at τike
            rw [← Range.map_get!_eq (as := A), Range.map, List.map_map, Alength_eq] at A'eq
            have := Range.eq_of_mem_of_map_eq A'eq i mem
            simp only [Function.comp] at this
            rw [← this] at τike
            rw [Type.freeTypeVars, List.mapMem_eq_map] at aninA
            have iltAlength : i < A.length := by
              rw [Alength_eq]
              exact mem.right
            let aninAi := List.not_mem_flatten.mp aninA (A.get! i).freeTypeVars
              (List.mem_map.mpr ⟨_, List.get!_mem iltAlength, rfl⟩)
            let ilt : i < ξτs.length := by rw [ξτslength_eq]; exact mem.right
            have := τike.Monotype_open_preservation ΓaΓ'we aninΓ' (aninτ i ilt) aninAi τke
            rw [Monotype_open, QualifiedType.Monotype_open] at this
            exact this
        all_goals nomatch A'eq
      | .floor _ =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case prod =>
          rw [Monotype.Monotype_open, Type.Type_open]
          rename «Type» => A
          cases A <;> rw [Type.TypeVar_open] at σke
          case list =>
            rw [Type.Type_open]
            rw [List.mapMem_eq_map] at σke ⊢
            rename List _ => As
            match As with
            | _ :: _ => nomatch σke
            | [] =>
              rw [List.map_nil] at σke ⊢
              let .floor ξke := σke
              rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at ξke
              let Alc := ξke.soundness ΓaΓ'we .label |>.TypeVarLocallyClosed_of.weaken (n := n)
              rw [Nat.zero_add] at Alc
              rw [← Alc.TypeVar_open_TypeVar_close_id (a := a)] at ξke
              rw [Monotype.freeTypeVars] at aninσ
              exact floor <| ξke.Monotype_open_preservation ΓaΓ'we aninΓ' aninσ
                Type.not_mem_freeTypeVars_TypeVar_close τke
          all_goals nomatch σke
        all_goals nomatch σke
      | .prodOrSum .prod .. =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case prod =>
          let .prod μke ρke := σke
          rw [Monotype.Monotype_open, Type.Type_open]
          rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at μke ρke
          rw [Monotype.freeTypeVars] at aninσ
          rw [Type.freeTypeVars] at aninA
          let Blc := μke.soundness ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
          rw [Nat.zero_add] at Blc
          rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
          let μke' := μke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) Type.not_mem_freeTypeVars_TypeVar_close τke
          let ρke' := ρke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_right _ ·) aninA τke
          rw [Monotype_open, QualifiedType.Monotype_open] at μke' ρke'
          exact prod μke' ρke'
        all_goals nomatch σke
      | .prodOrSum .sum .. =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case sum =>
          let .sum μke ρke := σke
          rw [Monotype.Monotype_open, Type.Type_open]
          rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at μke ρke
          rw [Monotype.freeTypeVars] at aninσ
          rw [Type.freeTypeVars] at aninA
          let Blc := μke.soundness ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
          rw [Nat.zero_add] at Blc
          rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
          let μke' := μke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) Type.not_mem_freeTypeVars_TypeVar_close τke
          let ρke' := ρke.Monotype_open_preservation ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_right _ ·) aninA τke
          rw [Monotype_open, QualifiedType.Monotype_open] at μke' ρke'
          exact sum μke' ρke'
        all_goals nomatch σke
      | .lift .. =>
        rename TypeLambda => «λτ»
        let .mk _ τ'' := «λτ»
        rw [Monotype.TypeVar_open, TypeLambda.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case listApp =>
          rename_i A _
          cases A <;> rw [Type.TypeVar_open] at σke
          case lam =>
            rename «Type» => A
            let .lift I τ''ke κ₀'e ρke := σke
            rw [Monotype.Monotype_open, TypeLambda.Monotype_open, Type.Type_open, Type.Type_open]
            rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at ρke
            rw [Monotype.freeTypeVars, TypeLambda.freeTypeVars] at aninσ
            rw [Type.freeTypeVars, Type.freeTypeVars] at aninA
            let ρke' := ρke.Monotype_open_preservation ΓaΓ'we aninΓ'
              (aninσ <| List.mem_append_right _ ·) (aninA <| List.mem_append_right _ ·) τke
            rw [Monotype_open, QualifiedType.Monotype_open] at ρke'
            apply lift ([[(Γ, a : κ₀, Γ')]].typeVarDom ++ I) _ κ₀'e ρke'
            intro a' a'nin
            let ⟨a'ninΓaΓ'', a'ninI⟩ := List.not_mem_append'.mp a'nin
            have a'ninΓa : [[a' ∉ dom(Γ, a : κ₀)]] := by
              rw [TypeEnvironment.typeVarDom_append] at a'ninΓaΓ''
              exact List.not_mem_append'.mp a'ninΓaΓ'' |>.right
            let ne := List.ne_of_not_mem_cons a'ninΓa
            symm at ne
            let ⟨_, .typeExt Γwe ..⟩ := ΓaΓ'we.append_left_elim
            let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
            let Blc := τke.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
            rw [Blc.Type_open_TypeVar_open_comm <| Nat.succ_ne_zero _]
            have := τ''ke a' a'ninI
            rw [τ''.TypeVar_open_comm <| Nat.succ_ne_zero _,
                ← QualifiedType.TypeVar_open, ← TypeVar_open,
                A.TypeVar_open_comm <| Nat.succ_ne_zero _, ← TypeEnvironment.append] at this
            have := this.Monotype_open_preservation (ΓaΓ'we.typeExt a'ninΓaΓ'' κ₀'e)
               (List.not_mem_cons.mpr ⟨ne, aninΓ'⟩)
               (Monotype.not_mem_freeTypeVars_TypeVar_open_intro
                 (aninσ <| List.mem_append_left _ ·) ne)
               (Type.not_mem_freeTypeVars_TypeVar_open_intro
                 (aninA <| List.mem_append_left _ ·) ne) τke
            rw [← TypeEnvironment.append, ← TypeEnvironment.TypeVar_subst,
                ← τ''.TypeVar_open_Monotype_open_comm τlc <| Nat.zero_ne_add_one _,
                ← QualifiedType.Monotype_open, ← Monotype_open]
            exact this
          all_goals nomatch σke
        all_goals nomatch σke
      | .contain .. =>
        rw [Monotype.TypeVar_open] at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .contain μke ρ₀ke ρ₁ke κe := σke
        let ⟨A₀, A₁, eq₀, eq₁, eq₂⟩ := Type.contain_evidence_eq_inversion aninA A'eq
        cases eq₀
        cases eq₁
        cases eq₂
        clear A'eq
        rw [Monotype.Monotype_open, Type.Type_open, Type.Type_open, List.mapMem_eq_map,
            List.map_cons, List.map_singleton]
        repeat rw [Type.Type_open]
        rw [if_neg (nomatch ·)]
        rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at μke ρ₀ke ρ₁ke
        rw [Monotype.freeTypeVars] at aninσ
        let ⟨aninρ₀μ, aninρ₁⟩ := List.not_mem_append'.mp aninσ
        let ⟨aninρ₀, aninμ⟩ := List.not_mem_append'.mp aninρ₀μ
        simp [Type.freeTypeVars] at aninA
        let ⟨_, aninA₀, aninA₁⟩ := aninA
        let Blc := μke.soundness ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
        rw [Nat.zero_add] at Blc
        rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
        let μke' := μke.Monotype_open_preservation ΓaΓ'we aninΓ' aninμ
          Type.not_mem_freeTypeVars_TypeVar_close τke
        let ρ₀ke' := ρ₀ke.Monotype_open_preservation ΓaΓ'we aninΓ' aninρ₀ aninA₀ τke
        let ρ₁ke' := ρ₁ke.Monotype_open_preservation ΓaΓ'we aninΓ' aninρ₁ aninA₁ τke
        rw [Monotype_open, QualifiedType.Monotype_open] at ρ₀ke' ρ₁ke'
        exact contain μke' ρ₀ke' ρ₁ke' κe
      | .concat .. =>
        rw [Monotype.TypeVar_open] at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .concat μke ρ₀ke ρ₁ke ρ₂ke κe _ _ := σke
        let foo := Type.concat_evidence_eq_inversion aninA A'eq
        sorry
        -- cases eq₀
        -- cases eq₁
        -- cases eq₂
        -- clear A'eq
        -- rw [Monotype.Monotype_open, Type.Type_open, Type.Type_open, List.mapMem_eq_map,
        --     List.map_cons, List.map_singleton]
        -- repeat rw [Type.Type_open]
        -- rw [if_neg (nomatch ·)]
        -- rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at μke ρ₀ke ρ₁ke
        -- rw [Monotype.freeTypeVars] at aninσ
        -- let ⟨aninρ₀μ, aninρ₁⟩ := List.not_mem_append'.mp aninσ
        -- let ⟨aninρ₀, aninμ⟩ := List.not_mem_append'.mp aninρ₀μ
        -- simp [Type.freeTypeVars] at aninA
        -- let ⟨_, aninA₀, aninA₁⟩ := aninA
        -- let Blc := μke.soundness ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
        -- rw [Nat.zero_add] at Blc
        -- rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
        -- let μke' := μke.Monotype_open_preservation ΓaΓ'we aninΓ' aninμ
        --   Type.not_mem_freeTypeVars_TypeVar_close τke
        -- let ρ₀ke' := ρ₀ke.Monotype_open_preservation ΓaΓ'we aninΓ' aninρ₀ aninA₀ τke
        -- let ρ₁ke' := ρ₁ke.Monotype_open_preservation ΓaΓ'we aninΓ' aninρ₁ aninA₁ τke
        -- rw [Monotype_open, QualifiedType.Monotype_open] at ρ₀ke' ρ₁ke'
        -- exact contain μke' ρ₀ke' ρ₁ke' κe
      | .typeClass .. =>
        rw [Monotype.TypeVar_open] at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .tc Γcw inΓc τ'ke (κ := κ) := σke
        let ⟨_, κe⟩ := κ.Elaboration_total
        let ⟨_, κe', _, Aki, _, Aₛki⟩ := Γcw.of_ClassEnvironment_in inΓc
        cases κe.deterministic κe'
        let B'lc := τ'ke.soundness ΓaΓ'we κe |>.TypeVarLocallyClosed_of
        let ⟨_, eq⟩ := Type.tc_evidence_eq_inversion aninA (Aki a |>.TypeVarLocallyClosed_of)
          (Aₛki a · · |>.TypeVarLocallyClosed_of) B'lc A'eq
        sorry
      | .all .. =>
        rename TypeLambda => «λτ»
        let .mk _ ψ := «λτ»
        rw [Monotype.TypeVar_open, TypeLambda.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case prod =>
          rename «Type» => A
          cases A <;> rw [Type.TypeVar_open] at σke
          case listApp =>
            rename_i A _
            cases A <;> rw [Type.TypeVar_open] at σke
            case lam =>
              rename «Type» => A
              let .all I ψke κe ρke := σke
              rw [Monotype.Monotype_open, TypeLambda.Monotype_open, Type.Type_open, Type.Type_open,
                  Type.Type_open]
              rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at ρke
              rw [Monotype.freeTypeVars, TypeLambda.freeTypeVars] at aninσ
              rw [Type.freeTypeVars, Type.freeTypeVars, Type.freeTypeVars] at aninA
              let ρke' := ρke.Monotype_open_preservation ΓaΓ'we aninΓ'
                (aninσ <| List.mem_append_right _ ·) (aninA <| List.mem_append_right _ ·) τke
              rw [Monotype_open, QualifiedType.Monotype_open] at ρke'
              apply all ([[(Γ, a : κ₀, Γ')]].typeVarDom ++ I) _ κe ρke'
              intro a' a'nin
              let ⟨a'ninΓaΓ'', a'ninI⟩ := List.not_mem_append'.mp a'nin
              have a'ninΓa : [[a' ∉ dom(Γ, a : κ₀)]] := by
                rw [TypeEnvironment.typeVarDom_append] at a'ninΓaΓ''
                exact List.not_mem_append'.mp a'ninΓaΓ'' |>.right
              let ne := List.ne_of_not_mem_cons a'ninΓa
              symm at ne
              let ⟨_, .typeExt Γwe ..⟩ := ΓaΓ'we.append_left_elim
              let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
              let Blc := τke.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
              rw [Blc.Type_open_TypeVar_open_comm <| Nat.succ_ne_zero _]
              have := ψke a' a'ninI
              rw [ψ.TypeVar_open_comm <| Nat.succ_ne_zero _,
                  ← QualifiedType.TypeVar_open, ← TypeVar_open,
                  A.TypeVar_open_comm <| Nat.succ_ne_zero _, ← TypeEnvironment.append] at this
              have := this.Monotype_open_preservation (ΓaΓ'we.typeExt a'ninΓaΓ'' κe)
                (List.not_mem_cons.mpr ⟨ne, aninΓ'⟩)
                (Monotype.not_mem_freeTypeVars_TypeVar_open_intro
                  (aninσ <| List.mem_append_left _ ·) ne)
                (Type.not_mem_freeTypeVars_TypeVar_open_intro
                  (aninA <| List.mem_append_left _ ·) ne) τke
              rw [← TypeEnvironment.append, ← TypeEnvironment.TypeVar_subst,
                  ← ψ.TypeVar_open_Monotype_open_comm τlc <| Nat.zero_ne_add_one _,
                  ← QualifiedType.Monotype_open, ← Monotype_open]
              exact this
            all_goals nomatch σke
          all_goals nomatch σke
        all_goals nomatch σke
      | .ind .. => sorry
      | .split (.mk κ τ'') ρ₀ ρ₁ ρ₂ =>
        rw [Monotype.TypeVar_open, TypeLambda.TypeVar_open] at σke
        let .split concatke := σke
        rw [Monotype.Monotype_open, TypeLambda.Monotype_open]
        let concatke' : KindingAndElaboration _ _ (TypeVar_open
            (.qual (.mono (.concat (.lift (.mk _ τ'') ρ₀) (.comm .comm) ρ₁ ρ₂))) a m) .. := by
          rw [TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
              Monotype.TypeVar_open, Monotype.TypeVar_open, TypeLambda.TypeVar_open]
          exact concatke
        rw [Monotype.freeTypeVars] at aninσ
        let concatke'' := concatke'.Monotype_open_preservation ΓaΓ'we aninΓ' (by
            rw [freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars,
                Monotype.freeTypeVars, Monotype.freeTypeVars, List.append_nil]
            exact aninσ
          ) aninA τke
        rw [Monotype_open, QualifiedType.Monotype_open, Monotype.Monotype_open,
            Monotype.Monotype_open, Monotype.Monotype_open, TypeLambda.Monotype_open] at concatke''
        exact split concatke''
    | .qual ψ γ' =>
      rw [QualifiedType.TypeVar_open] at σke
      cases A <;> rw [Type.TypeVar_open] at σke
      case arr =>
        let .qual ψke γ'ke κ₁e := σke
        rw [QualifiedType.Monotype_open, Type.Type_open]
        rw [← QualifiedType.TypeVar_open] at ψke
        rw [← TypeVar_open] at ψke γ'ke
        rw [Type.freeTypeVars] at aninA
        let ψke' := ψke.Monotype_open_preservation ΓaΓ'we aninΓ' (aninσ <| List.mem_append_left _ ·)
          (aninA <| List.mem_append_left _ ·) τke
        let γ'ke' := γ'ke.Monotype_open_preservation ΓaΓ'we aninΓ'
          (aninσ <| List.mem_append_right _ ·) (aninA <| List.mem_append_right _ ·) τke
        rw [Monotype_open] at ψke' γ'ke'
        rw [QualifiedType.Monotype_open] at ψke'
        exact qual ψke' γ'ke' κ₁e
      all_goals nomatch σke
  | .quant κ σ' =>
    rw [TypeVar_open] at σke
    cases A <;> rw [Type.TypeVar_open] at σke
    case var => split at σke <;> nomatch σke
    case «forall» K A =>
      let .scheme I σ'ke κe := σke
      rw [Monotype_open, Type.Type_open]
      apply scheme ([[(Γ, a : κ₀, Γ')]].typeVarDom ++ I) _ κe
      intro a' a'nin
      let ⟨a'ninΓaΓ'', a'ninI⟩ := List.not_mem_append'.mp a'nin
      have a'ninΓa : [[a' ∉ dom(Γ, a : κ₀)]] := by
        rw [TypeEnvironment.typeVarDom_append] at a'ninΓaΓ''
        exact List.not_mem_append'.mp a'ninΓaΓ'' |>.right
      let ne := List.ne_of_not_mem_cons a'ninΓa
      symm at ne
      let ⟨_, .typeExt Γwe ..⟩ := ΓaΓ'we.append_left_elim
      let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
      let Blc := τke.soundness Γwe κ₀e |>.TypeVarLocallyClosed_of
      rw [Blc.Type_open_TypeVar_open_comm <| Nat.succ_ne_zero _]
      have := σ'ke a' a'ninI
      rw [σ'.TypeVar_open_comm <| Nat.succ_ne_zero _,
          A.TypeVar_open_comm <| Nat.succ_ne_zero _, ← TypeEnvironment.append] at this
      rw [freeTypeVars] at aninσ
      rw [Type.freeTypeVars] at aninA
      have := this.Monotype_open_preservation (ΓaΓ'we.typeExt a'ninΓaΓ'' κe)
        (List.not_mem_cons.mpr ⟨ne, aninΓ'⟩) (not_mem_freeTypeVars_TypeVar_open_intro aninσ ne)
        (Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ne) τke
      rw [← TypeEnvironment.append, ← TypeEnvironment.TypeVar_subst,
          ← σ'.TypeVar_open_Monotype_open_comm τlc <| Nat.zero_ne_add_one _]
      exact this
    all_goals nomatch σke
termination_by σ.sizeOf'
decreasing_by
  all_goals simp_arith; try simp_arith [h]
  · rw [← List.get!_eq_getElem!]
    apply Nat.le_add_right_of_le
    apply Nat.le_of_add_right_le (k := (ξτs.get! i).snd.sizeOf')
    apply List.le_sum_of_mem'
    apply List.mem_map.mpr
    exact ⟨_, List.get!_mem ilt, rfl⟩
  · rw [← List.get!_eq_getElem!]
    apply Nat.le_add_right_of_le
    apply Nat.le_of_add_right_le (k := (ξτs.get! i).fst.sizeOf')
    rw [Nat.add_comm]
    apply List.le_sum_of_mem'
    apply List.mem_map.mpr
    exact ⟨_, List.get!_mem ilt, rfl⟩
  · exact Nat.succ_le_of_lt <| QualifiedType.sizeOf'_pos _

end TypeScheme.KindingAndElaboration

end TabularTypeInterpreter
