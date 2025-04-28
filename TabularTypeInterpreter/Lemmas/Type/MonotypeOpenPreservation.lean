import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Type
import TabularTypeInterpreter.Lemmas.TypeEnvironment.Basic
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
                          rw [if_neg nofun] at *
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
                                    rw [if_neg nofun] at *
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
                                                  rw [if_neg nofun] at *
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
                                                            rw [if_neg nofun] at *
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

set_option maxHeartbeats 2000000 in
private
theorem concat_evidence_eq_inversion
  (eq : A.TypeVar_open a n = [[⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀⟧)) → (⊗ (a$0 ⟦A₁⟧)) → ⊗ (a$0 ⟦A₂⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂⟧)) → aₜ$0, Bₗ, Bᵣ}]])
  : ∃ A₀' A₀'' A₁' A₁'' A₂' A₂'' Bₗ' Bᵣ',
    A₀ = A₀'.TypeVar_open a (n + 1) ∧
    A₀ = A₀''.TypeVar_open a (n + 2) ∧
    A₁ = A₁'.TypeVar_open a (n + 1) ∧
    A₁ = A₁''.TypeVar_open a (n + 2) ∧
    A₂ = A₂'.TypeVar_open a (n + 1) ∧
    A₂ = A₂''.TypeVar_open a (n + 2) ∧
    Bₗ = Bₗ'.TypeVar_open a n ∧ Bᵣ = Bᵣ'.TypeVar_open a n ∧
    A = [[⊗ {∀ a : K ↦ *. (⊗ (a$0 ⟦A₀'⟧)) → (⊗ (a$0 ⟦A₁'⟧)) → ⊗ (a$0 ⟦A₂'⟧), ∀ a : K ↦ *. ∀ aₜ : *. ((⊕ (a$1 ⟦A₀''⟧)) → aₜ$0) → ((⊕ (a$1 ⟦A₁''⟧)) → aₜ$0) → (⊕ (a$1 ⟦A₂''⟧)) → aₜ$0, Bₗ', Bᵣ'}]] := by
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
                let ⟨eq₂, eq'''''⟩ := List.cons_eq_cons.mp eq''''
                let ⟨eq₃, _⟩ := List.cons_eq_cons.mp eq'''''
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
                              rw [if_neg nofun] at *
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
                                          rw [if_neg nofun] at *
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
                                                    rw [if_neg nofun] at *
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
                                                                      rw [if_neg nofun] at *
                                                                      cases A₁₀₁' <;> rw [Type.TypeVar_open] at *
                                                                      case var =>
                                                                        rename «F⊗⊕ω».TypeVar => a'
                                                                        cases a'
                                                                        case bound =>
                                                                          rename Nat => n'
                                                                          match n' with
                                                                          | 0 =>
                                                                            rw [if_neg nofun] at *
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
                                                                                          rw [if_neg nofun] at *
                                                                                          cases A₁₁₀₁' <;> rw [Type.TypeVar_open] at *
                                                                                          case var =>
                                                                                            rename «F⊗⊕ω».TypeVar => a'
                                                                                            cases a'
                                                                                            case bound =>
                                                                                              rename Nat => n'
                                                                                              match n' with
                                                                                              | 0 =>
                                                                                                rw [if_neg nofun] at *
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
                                                                                                            rw [if_neg nofun] at *
                                                                                                            cases A₁₁₁₁' <;> rw [Type.TypeVar_open] at *
                                                                                                            case var =>
                                                                                                              rename «F⊗⊕ω».TypeVar => a'
                                                                                                              cases a'
                                                                                                              case bound =>
                                                                                                                rename Nat => n'
                                                                                                                match n' with
                                                                                                                | 0 =>
                                                                                                                  rw [if_neg nofun] at *
                                                                                                                  cases eq₀'
                                                                                                                  let ⟨eq₁₀, eq₁₁⟩ := arr.inj eq₁''
                                                                                                                  let ⟨eq₁₁₀, eq₁₁₁⟩ := arr.inj eq₁₁
                                                                                                                  exact ⟨
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    _,
                                                                                                                    rfl,
                                                                                                                    And.right <| listApp.inj <| sum.inj <| And.left <| arr.inj eq₁₀.symm,
                                                                                                                    rfl,
                                                                                                                    And.right <| listApp.inj <| sum.inj <| And.left <| arr.inj eq₁₁₀.symm,
                                                                                                                    rfl,
                                                                                                                    And.right <| listApp.inj <| sum.inj <| And.left <| arr.inj eq₁₁₁.symm,
                                                                                                                    eq₂.symm,
                                                                                                                    eq₃.symm,
                                                                                                                    rfl
                                                                                                                  ⟩
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
theorem tc_evidence_eq_inversion (aninA : a ∉ A.freeTypeVars)
  (A'oplc : (A'.TypeVar_open a').TypeVarLocallyClosed)
  (Aₛoplc : ∀ i ∈ [:n'], ((Aₛ i).TypeVar_open a').TypeVarLocallyClosed)
  (Blc : B.TypeVarLocallyClosed)
  (eq : A.TypeVar_open a n = [[⊗ {A'^^B, </ Aₛ@i^^B // i in [:n'] />}]])
  : ∃ A'' Aₛ', A'.Type_open B = A''.TypeVar_open a n ∧
    (∀ i ∈ [:n'], (Aₛ i).Type_open B = (Aₛ' i).TypeVar_open a n) ∧
    A = [[⊗ {A'', </ Aₛ'@i // i in [:n'] />}]] := by
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
      | A'' :: Aₛ' =>
        rw [List.map_cons] at *
        let ⟨eq₀, eq₁⟩ := List.cons_eq_cons.mp eq''
        rw [← Range.map_get!_eq (as := Aₛ'), Range.map, List.map_map, ← Range.map] at eq₁
        let length_eq : List.length (Range.map ..) = List.length _ :=  by rw [eq₁]
        rw [List.length_map, List.length_map, Range.length_toList, Range.length_toList,
            Nat.sub_zero, Nat.sub_zero] at length_eq
        cases length_eq
        rw [freeTypeVars, freeTypeVars, List.mapMem_eq_map, List.map_cons, List.flatten] at aninA
        let ⟨aninA'', aninAₛ'⟩ := List.not_mem_append'.mp aninA
        let A'lc := A'oplc.weaken (n := 1).TypeVar_open_drop <| Nat.lt.base _
        let A'opBlc := A'lc.Type_open_dec Blc |>.weaken (n := n)
        rw [Nat.zero_add] at A'opBlc
        rw [← A'opBlc.TypeVar_open_TypeVar_close_id (a := a)] at eq₀
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars aninA''
          Type.not_mem_freeTypeVars_TypeVar_close eq₀
        let A'lc' := A'lc.weaken (n := n)
        rw [Nat.add_comm] at A'lc'
        apply Exists.intro <| (A'.Type_open B).TypeVar_close a n
        apply Exists.intro fun i => ((Aₛ'.get! i).TypeVar_open a n).TypeVar_close a n
        constructor
        · exact A'opBlc.TypeVar_open_TypeVar_close_id (a := a).symm
        · constructor
          · intro i mem
            let Aₛeq := Range.eq_of_mem_of_map_eq eq₁ i mem
            simp only [Function.comp] at Aₛeq ⊢
            let Aₛoplc' := Aₛoplc i mem |>.weaken (n := 1).TypeVar_open_drop <| Nat.lt.base _
            let AₛopBlc := Aₛoplc'.Type_open_dec Blc |>.weaken (n := n)
            rw [Nat.zero_add] at AₛopBlc
            rw [← AₛopBlc.TypeVar_open_TypeVar_close_id (a := a), Aₛeq]
          · congr
            rw (occs := .pos [1]) [← Range.map_get!_eq (as := Aₛ')]
            apply Range.map_eq_of_eq_of_mem
            intro i mem
            symm
            apply Type.TypeVar_close_TypeVar_open_eq_of_not_mem_freeTypeVars
            exact List.not_mem_flatten.mp aninAₛ' (Aₛ'.get! i).freeTypeVars <|
              List.mem_map.mpr ⟨_, List.get!_mem mem.upper, rfl⟩
    all_goals nomatch eq
  all_goals nomatch eq

private
theorem ind_evidence_inversion
  (eq : A.TypeVar_open a n = [[∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ → Bₗ → (⊗ { }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1) → (aₘ$0 { }) → aₘ$0 A']])
  : ∃ Bᵣ' Bₗ' A'',
    Bᵣ = Bᵣ'.TypeVar_open a (n + 6) ∧ Bₗ = Bₗ'.TypeVar_open a (n + 6) ∧
    A' = A''.TypeVar_open a (n + 1) ∧
    A = [[∀ aₘ : (L K) ↦ *. (∀ aₗ : *. ∀ aₜ : K. ∀ aₚ : L K. ∀ aᵢ : L K. ∀ aₙ : L K. Bᵣ' → Bₗ' → (⊗ { }) → (aₘ$5 aₚ$2) → aₘ$5 aᵢ$1) → (aₘ$0 { }) → aₘ$0 A'']] := by
  cases A <;> rw [TypeVar_open] at eq
  case «forall» A =>
    rcases forall.inj eq with ⟨rfl, eq'⟩
    cases A <;> rw [TypeVar_open] at eq'
    case arr A₀ A₁ =>
      let ⟨eq₀, eq₁⟩ := arr.inj eq'
      cases A₀ <;> rw [TypeVar_open] at eq₀
      case «forall» A₀ =>
        rcases forall.inj eq₀ with ⟨rfl, eq₀'⟩
        cases A₀ <;> rw [TypeVar_open] at eq₀'
        case «forall» A₀ =>
          rcases forall.inj eq₀' with ⟨rfl, eq₀''⟩
          cases A₀ <;> rw [TypeVar_open] at eq₀''
          case «forall» A₀ =>
            rcases forall.inj eq₀'' with ⟨rfl, eq₀'''⟩
            cases A₀ <;> rw [TypeVar_open] at eq₀'''
            case «forall» A₀ =>
              rcases forall.inj eq₀''' with ⟨rfl, eq₀''''⟩
              cases A₀ <;> rw [TypeVar_open] at eq₀''''
              case «forall» A₀ =>
                rcases forall.inj eq₀'''' with ⟨rfl, eq₀'''''⟩
                cases A₀ <;> rw [TypeVar_open] at eq₀'''''
                case arr Bᵣ' A₀ =>
                  let ⟨Bᵣeq, eq₀''''''⟩ := arr.inj eq₀'''''
                  cases A₀ <;> rw [TypeVar_open] at eq₀''''''
                  case arr Bₗ' A₀ =>
                    let ⟨Bₗeq, eq₀'''''''⟩ := arr.inj eq₀''''''
                    cases A₀ <;> rw [TypeVar_open] at eq₀'''''''
                    case arr A₀₀ A₀₁ =>
                      let ⟨eq₀₀, eq₀₁⟩ := arr.inj eq₀'''''''
                      cases A₀₀ <;> rw [TypeVar_open] at eq₀₀
                      case prod A₀₀ =>
                        let eq₀₀' := prod.inj eq₀₀
                        cases A₀₀ <;> rw [TypeVar_open] at eq₀₀'
                        case list =>
                          let eq₀₀'' := list.inj eq₀₀'
                          rw [List.mapMem_eq_map] at eq₀₀''
                          cases List.map_eq_nil_iff.mp eq₀₀''
                          cases A₀₁ <;> rw [TypeVar_open] at eq₀₁
                          case arr A₀₁₀ A₀₁₁ =>
                            let ⟨eq₀₁₀, eq₀₁₁⟩ := arr.inj eq₀₁
                            cases A₀₁₀ <;> rw [TypeVar_open] at eq₀₁₀
                            case app A₀₁₀₀ A₀₁₀₁ =>
                              let ⟨eq₀₁₀₀, eq₀₁₀₁⟩ := app.inj eq₀₁₀
                              cases A₀₁₀₀ <;> rw [TypeVar_open] at eq₀₁₀₀
                              case var a' =>
                                match a' with
                                | .bound n' =>
                                  split at eq₀₁₀₀
                                  · case isTrue => nomatch eq₀₁₀₀
                                  · case isFalse =>
                                    cases eq₀₁₀₀
                                    cases A₀₁₀₁ <;> rw [TypeVar_open] at eq₀₁₀₁
                                    case var a' =>
                                      match a' with
                                      | .bound n' =>
                                        split at eq₀₁₀₁
                                        · case isTrue => nomatch eq₀₁₀₁
                                        · case isFalse =>
                                          cases eq₀₁₀₁
                                          cases A₀₁₁ <;> rw [TypeVar_open] at eq₀₁₁
                                          case app A₀₁₁₀ A₀₁₁₁ =>
                                            let ⟨eq₀₁₁₀, eq₀₁₁₁⟩ := app.inj eq₀₁₁
                                            cases A₀₁₁₀ <;> rw [TypeVar_open] at eq₀₁₁₀
                                            case var a' =>
                                              match a' with
                                              | .bound n' =>
                                                split at eq₀₁₁₀
                                                · case isTrue => nomatch eq₀₁₁₀
                                                · case isFalse =>
                                                  cases eq₀₁₁₀
                                                  cases A₀₁₁₁ <;> rw [TypeVar_open] at eq₀₁₁₁
                                                  case var a' =>
                                                    match a' with
                                                    | .bound n' =>
                                                      split at eq₀₁₁₁
                                                      · case isTrue => nomatch eq₀₁₁₁
                                                      · case isFalse =>
                                                        cases eq₀₁₁₁
                                                        cases A₁ <;> rw [TypeVar_open] at eq₁
                                                        case arr A₁₀ A₁₁ =>
                                                          let ⟨eq₁₀, eq₁₁⟩ := arr.inj eq₁
                                                          cases A₁₀ <;> rw [TypeVar_open] at eq₁₀
                                                          case app A₁₀₀ A₁₀₁ =>
                                                            let ⟨eq₁₀₀, eq₁₀₁⟩ := app.inj eq₁₀
                                                            cases A₁₀₀ <;> rw [TypeVar_open] at eq₁₀₀
                                                            case var a' =>
                                                              match a' with
                                                              | .bound n' =>
                                                                split at eq₁₀₀
                                                                · case isTrue => nomatch eq₁₀₀
                                                                · case isFalse =>
                                                                  cases eq₁₀₀
                                                                  cases A₁₀₁ <;> rw [TypeVar_open] at eq₁₀₁
                                                                  case list A₁₀₁ =>
                                                                    let eq₁₀₁' := list.inj eq₁₀₁
                                                                    rw [List.mapMem_eq_map] at eq₁₀₁'
                                                                    cases List.map_eq_nil_iff.mp eq₁₀₁'
                                                                    cases A₁₁ <;> rw [TypeVar_open] at eq₁₁
                                                                    case app A₁₁₀ A'' =>
                                                                      let ⟨eq₁₁₀, A'eq⟩ := app.inj eq₁₁
                                                                      cases A₁₁₀ <;> rw [TypeVar_open] at eq₁₁₀
                                                                      case var a' =>
                                                                        match a' with
                                                                        | .bound n' =>
                                                                          split at eq₁₁₀
                                                                          · case isTrue => nomatch eq₁₁₀
                                                                          · case isFalse =>
                                                                            cases eq₁₁₀
                                                                            exact ⟨_, _, _, Bᵣeq.symm, Bₗeq.symm, A'eq.symm, rfl⟩
                                                                        | .free _ => split at eq₁₁₀ <;> nomatch eq₁₁₀
                                                                      all_goals nomatch eq₁₁₀
                                                                    all_goals nomatch eq₁₁
                                                                  all_goals nomatch eq₁₀₁
                                                              | .free _ => split at eq₁₀₀ <;> nomatch eq₁₀₀
                                                            all_goals nomatch eq₁₀₀
                                                          all_goals nomatch eq₁₀
                                                        all_goals nomatch eq₁
                                                    | .free _ => split at eq₀₁₁₁ <;> nomatch eq₀₁₁₁
                                                  all_goals nomatch eq₀₁₁₁
                                              | .free _ => split at eq₀₁₁₀ <;> nomatch eq₀₁₁₀
                                            all_goals nomatch eq₀₁₁₀
                                          all_goals nomatch eq₀₁₁
                                      | .free _ => split at eq₀₁₀₁ <;> nomatch eq₀₁₀₁
                                    all_goals nomatch eq₀₁₀₁
                                | .free _ => split at eq₀₁₀₀ <;> nomatch eq₀₁₀₀
                              all_goals nomatch eq₀₁₀₀
                            all_goals nomatch eq₀₁₀
                          all_goals nomatch eq₀₁
                        all_goals nomatch eq₀₀'
                      all_goals nomatch eq₀₀
                    all_goals nomatch eq₀'''''''
                  all_goals nomatch eq₀''''''
                all_goals nomatch eq₀'''''
              all_goals nomatch eq₀''''
            all_goals nomatch eq₀'''
          all_goals nomatch eq₀''
        all_goals nomatch eq₀'
      all_goals nomatch eq₀
    all_goals nomatch eq'
  all_goals nomatch eq

end «F⊗⊕ω».Type

open «F⊗⊕ω»

local instance : Inhabited Monotype where
  default := .row [] none
in
local instance : Inhabited «Type» where
  default := .list []
in
set_option maxHeartbeats 2000000 in
open TypeScheme in
mutual

theorem TypeScheme.KindingAndElaboration.Monotype_open_preservation
  (σke : KindingAndElaboration Γc [[Γ, a : κ₀, Γ']] (TypeVar_open σ a m) κ₁
    (Type.TypeVar_open A a n)) (Γcw : [[⊢c Γc]]) (ΓaΓ'we : [[Γc ⊢ Γ, a : κ₀, Γ' ⇝ Δ]])
  (aninΓ' : [[a ∉ dom(Γ')]]) (aninσ : a ∉ σ.freeTypeVars) (aninA : a ∉ A.freeTypeVars)
  (τke : [[Γc; Γ ⊢ τ : κ₀ ⇝ B]])
  : KindingAndElaboration Γc [[Γ, (Γ' [τ / a])]] (σ.Monotype_open τ m) κ₁ (A.Type_open B n) :=
  open KindingAndElaboration in by
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
              let ⟨_, κ₁e⟩ := κ₁.Elaboration_total
              let ainΔ := ΓaΓ'we.TypeVarIn_preservation ain κ₁e
              rcases ainΔ.eq_of with ⟨_, _, rfl⟩
              exact τke.weakening (Γ'' := .empty) <|
                ΓaΓ'we.TypeVar_subst_preservation Γcw aninΓ' τke
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
      | .app ϕ τ'' =>
        rw [Monotype.TypeVar_open] at σke
        cases A <;> rw [Type.TypeVar_open] at σke
        case app =>
          let .app ϕke τ''ke := σke
          rw [Monotype.Monotype_open, Type.Type_open]
          rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at ϕke τ''ke
          rw [Monotype.freeTypeVars] at aninσ
          rw [Type.freeTypeVars] at aninA
          let ϕke' := ϕke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) (aninA <| List.mem_append_left _ ·) τke
          let τ''ke' := τ''ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_right _ ·) (aninA <| List.mem_append_right _ ·) τke
          rw [Monotype_open, QualifiedType.Monotype_open] at ϕke' τ''ke'
          exact app ϕke' τ''ke'
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
          let τ₀ke' := τ₀ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) (aninA <| List.mem_append_left _ ·) τke
          let τ₁ke' := τ₁ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
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
        cases A <;> rw [Type.TypeVar_open] at A'eq
        case list =>
          rename List _ => A
          rw [List.mapMem_eq_map] at A'eq
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
                simp only [Function.comp, ξ', τ']
              ), ← Range.map, Range.map_eq_of_eq_of_mem (by
                intro i _
                show _ = A'' i
                simp only [Function.comp, A'']
              ), ← Range.map]
          rw [← Range.map_get!_eq (as := ξτs), ξτslength_eq, Range.map, List.map_map] at ξτs'eq
          rw [Monotype.freeTypeVars, List.mapMem_eq_map] at aninσ
          let aninξ i ilt : a ∉ (ξτs.get! i).fst.freeTypeVars := by
            apply (List.not_mem_append' (ys := (ξτs.get! i).snd.freeTypeVars)).mp _ |>.left
            apply List.not_mem_flatten.mp aninσ
            apply List.mem_map.mpr
            exact ⟨_, List.get!_mem ilt, rfl⟩
          let aninτ i ilt : a ∉ (ξτs.get! i).snd.freeTypeVars := by
            apply (List.not_mem_append' (xs := (ξτs.get! i).fst.freeTypeVars)).mp _ |>.right
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
            let Bki := ξike.soundness Γcw ΓaΓ'we .label |>.TypeVarLocallyClosed_of.weaken (n := m)
            rw [Nat.zero_add] at Bki
            rw [← Bki.TypeVar_open_TypeVar_close_id (a := a)] at ξike
            let ilt : i < ξτs.length := by rw [ξτslength_eq]; exact mem.upper
            have := ξike.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' (aninξ i ilt)
              Type.not_mem_freeTypeVars_TypeVar_close τke
            rw [Monotype_open, QualifiedType.Monotype_open] at this
            exact this
          · rw [funext (f := fun i => ξ' i) (by
              intro i
              show _ = ((fun x => x.Monotype_open τ m) ∘ (fun i => ξτs.get! i |>.fst)) i
              simp only [ξ', Function.comp]
            ), Range.map, ← List.map_map]
            apply Monotype.label.Uniqueness.Monotype_open_preservation (a := a)
            rw [Range.map, Range.map_eq_of_eq_of_mem (by
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
              exact mem.upper
            let aninAi := List.not_mem_flatten.mp aninA (A.get! i).freeTypeVars
              (List.mem_map.mpr ⟨_, List.get!_mem iltAlength, rfl⟩)
            let ilt : i < ξτs.length := by rw [ξτslength_eq]; exact mem.upper
            have := τike.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' (aninτ i ilt) aninAi τke
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
              let Alc := ξke.soundness Γcw ΓaΓ'we .label |>.TypeVarLocallyClosed_of.weaken (n := n)
              rw [Nat.zero_add] at Alc
              rw [← Alc.TypeVar_open_TypeVar_close_id (a := a)] at ξke
              rw [Monotype.freeTypeVars] at aninσ
              exact floor <| ξke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninσ
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
          let Blc := μke.soundness Γcw ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
          rw [Nat.zero_add] at Blc
          rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
          let μke' := μke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) Type.not_mem_freeTypeVars_TypeVar_close τke
          let ρke' := ρke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
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
          let Blc := μke.soundness Γcw ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
          rw [Nat.zero_add] at Blc
          rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
          let μke' := μke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
            (aninσ <| List.mem_append_left _ ·) Type.not_mem_freeTypeVars_TypeVar_close τke
          let ρke' := ρke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
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
            let ρke' := ρke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
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
            let Blc := τke.soundness Γcw Γwe κ₀e |>.TypeVarLocallyClosed_of
            rw [Blc.Type_open_TypeVar_open_comm <| Nat.succ_ne_zero _]
            have := τ''ke a' a'ninI
            rw [τ''.TypeVar_open_comm <| Nat.succ_ne_zero _,
                ← QualifiedType.TypeVar_open, ← TypeVar_open,
                A.TypeVar_open_comm <| Nat.succ_ne_zero _, ← TypeEnvironment.append] at this
            have := this.Monotype_open_preservation Γcw (ΓaΓ'we.typeExt a'ninΓaΓ'' κ₀'e)
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
        rw [if_neg nofun]
        rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at μke ρ₀ke ρ₁ke
        rw [Monotype.freeTypeVars] at aninσ
        let ⟨aninρ₀μ, aninρ₁⟩ := List.not_mem_append'.mp aninσ
        let ⟨aninρ₀, aninμ⟩ := List.not_mem_append'.mp aninρ₀μ
        simp [Type.freeTypeVars] at aninA
        let ⟨_, aninA₀, aninA₁⟩ := aninA
        let Blc := μke.soundness Γcw ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
        rw [Nat.zero_add] at Blc
        rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
        let μke' := μke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninμ
          Type.not_mem_freeTypeVars_TypeVar_close τke
        let ρ₀ke' := ρ₀ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninρ₀ aninA₀ τke
        let ρ₁ke' := ρ₁ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninρ₁ aninA₁ τke
        rw [Monotype_open, QualifiedType.Monotype_open] at ρ₀ke' ρ₁ke'
        exact contain μke' ρ₀ke' ρ₁ke' κe
      | .concat .. =>
        rw [Monotype.TypeVar_open] at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .concat μke ρ₀ke ρ₁ke ρ₂ke κe keBₗ keBᵣ := σke
        rcases Type.concat_evidence_eq_inversion A'eq with
          ⟨A₀', A₀'', A₁', A₁'', A₂', A₂'', Bₗ', Bᵣ', eq₀, eq₀', eq₁, eq₁', eq₂, eq₂', rfl, rfl, rfl⟩
        simp [Type.Type_open]
        rw [Monotype.Monotype_open]
        simp [Type.freeTypeVars] at aninA
        let ⟨aninA₀', aninA₁', aninA₂', aninA₀'', aninA₁'', aninA₂'', aninBₗ', aninBᵣ'⟩:= aninA
        let A₀lc := ρ₀ke.soundness Γcw ΓaΓ'we κe.row |>.TypeVarLocallyClosed_of.weaken (n := n + 1)
        let A₀lc' := ρ₀ke.soundness Γcw ΓaΓ'we κe.row |>.TypeVarLocallyClosed_of.weaken (n := n + 2)
        rw [Nat.zero_add] at A₀lc A₀lc'
        rw [← A₀lc.TypeVar_open_TypeVar_close_id (a := a)] at eq₀ ρ₀ke
        rw [← A₀lc'.TypeVar_open_TypeVar_close_id (a := a)] at eq₀'
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close
          aninA₀' eq₀
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close
          aninA₀'' eq₀'
        let A₁lc := ρ₁ke.soundness Γcw ΓaΓ'we κe.row |>.TypeVarLocallyClosed_of.weaken (n := n + 1)
        let A₁lc' := ρ₁ke.soundness Γcw ΓaΓ'we κe.row |>.TypeVarLocallyClosed_of.weaken (n := n + 2)
        rw [Nat.zero_add] at A₁lc A₁lc'
        rw [← A₁lc.TypeVar_open_TypeVar_close_id (a := a)] at eq₁ ρ₁ke
        rw [← A₁lc'.TypeVar_open_TypeVar_close_id (a := a)] at eq₁'
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close
          aninA₁' eq₁
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close
          aninA₁'' eq₁'
        let A₂lc := ρ₂ke.soundness Γcw ΓaΓ'we κe.row |>.TypeVarLocallyClosed_of.weaken (n := n + 1)
        let A₂lc' := ρ₂ke.soundness Γcw ΓaΓ'we κe.row |>.TypeVarLocallyClosed_of.weaken (n := n + 2)
        rw [Nat.zero_add] at A₂lc A₂lc'
        rw [← A₂lc.TypeVar_open_TypeVar_close_id (a := a)] at eq₂ ρ₂ke
        rw [← A₂lc'.TypeVar_open_TypeVar_close_id (a := a)] at eq₂'
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close
          aninA₂' eq₂
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars Type.not_mem_freeTypeVars_TypeVar_close
          aninA₂'' eq₂'
        rw [A₀lc'.Type_open_TypeVar_close_eq_TypeVar_subst,
            ← A₀lc.Type_open_TypeVar_close_eq_TypeVar_subst,
            A₁lc'.Type_open_TypeVar_close_eq_TypeVar_subst,
            ← A₁lc.Type_open_TypeVar_close_eq_TypeVar_subst,
            A₂lc'.Type_open_TypeVar_close_eq_TypeVar_subst,
            ← A₂lc.Type_open_TypeVar_close_eq_TypeVar_subst]
        simp [Monotype.freeTypeVars] at aninσ
        let ⟨aninρ₀, aninμ, aninρ₁, aninρ₂⟩ := aninσ
        rw [← Monotype.TypeVar_open] at keBₗ keBᵣ
        rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at μke ρ₀ke ρ₁ke ρ₂ke keBₗ keBᵣ
        let Blc := μke.soundness Γcw ΓaΓ'we .comm |>.TypeVarLocallyClosed_of.weaken (n := n)
        rw [Nat.zero_add] at Blc
        rw [← Blc.TypeVar_open_TypeVar_close_id (a := a)] at μke
        let μke' := μke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninμ
          Type.not_mem_freeTypeVars_TypeVar_close τke
        let ρ₀ke' := ρ₀ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninρ₀
          Type.not_mem_freeTypeVars_TypeVar_close τke
        let ρ₁ke' := ρ₁ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninρ₁
          Type.not_mem_freeTypeVars_TypeVar_close τke
        let ρ₂ke' := ρ₂ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninρ₂
          Type.not_mem_freeTypeVars_TypeVar_close τke
        let keBₗ' := keBₗ.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' (by
          simp [freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars]
          exact ⟨aninρ₀, aninμ, aninρ₂⟩) aninBₗ' τke
        let keBᵣ' := keBᵣ.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' (by
          simp [freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars]
          exact ⟨aninρ₁, aninμ, aninρ₂⟩) aninBᵣ' τke
        rw [Monotype_open, QualifiedType.Monotype_open, Monotype.Monotype_open] at keBₗ' keBᵣ'
        exact concat μke' ρ₀ke' ρ₁ke' ρ₂ke' κe keBₗ' keBᵣ'
      | .typeClass .. =>
        rw [Monotype.TypeVar_open] at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .tc inΓc τ'ke (κ := κ) (A := A) (TCₛ := TCₛ) (Aₛ := Aₛ) (n := n') (m := m) (σ := σ')
          (B := B') := σke
        let ⟨a', a'nin⟩ := a :: ↑A.freeTypeVars ++ ↑([:n'].map fun i => (Aₛ i).freeTypeVars).flatten
          |>.exists_fresh
        let ⟨_, κe, _, Aki, _, Aₛki⟩ := Γcw.In_inversion inΓc
        let B'lc := τ'ke.soundness Γcw ΓaΓ'we κe |>.TypeVarLocallyClosed_of
        rcases Type.tc_evidence_eq_inversion aninA (Aki a').TypeVarLocallyClosed_of
          (Aₛki a' · · |>.TypeVarLocallyClosed_of) B'lc A'eq with ⟨A', Aₛ', eq₀, eq₁, rfl⟩
        let Alc := Aki a' |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop Nat.one_pos
        rw [Type.freeTypeVars, Type.freeTypeVars, List.mapMem_eq_map, List.map_cons,
            List.flatten_cons, List.map_map] at aninA
        let ⟨aninA', aninAₛ'⟩ := List.not_mem_append'.mp aninA
        let AopB'lc := Alc.Type_open_dec B'lc
        let AopB'lc' := AopB'lc.weaken (n := n)
        rw [Nat.zero_add] at AopB'lc'
        rw [← AopB'lc'.TypeVar_open_TypeVar_close_id (a := a)] at eq₀
        cases Type.TypeVar_open_inj_of_not_mem_freeTypeVars
          Type.not_mem_freeTypeVars_TypeVar_close aninA' eq₀
        let ⟨_, .typeExt Γwe ..⟩ := ΓaΓ'we.append_left_elim
        let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
        let Blc := τke.soundness Γcw Γwe κ₀e |>.TypeVarLocallyClosed_of
        rw [Type.Type_open, Type.Type_open, List.mapMem_eq_map, List.map_cons,
            List.map_map, Range.map_eq_of_eq_of_mem (by
              intro i mem
              show _ = ((Aₛ i).TypeVar_subst a B).Type_open (B'.TypeVar_subst a B)
              let Aₛeq := eq₁ i mem
              let Aₛlc := Aₛki a' i mem |>.TypeVarLocallyClosed_of.weaken (n := 1).TypeVar_open_drop
                Nat.one_pos
              let AₛopB'lc := Aₛlc.Type_open_dec B'lc
              let AₛopB'lc' := AₛopB'lc.weaken (n := n)
              rw [Nat.zero_add] at AₛopB'lc'
              rw [← AₛopB'lc'.TypeVar_open_TypeVar_close_id (a := a)] at Aₛeq
              let aninAₛ'' := List.not_mem_flatten.mp aninAₛ' (Aₛ' i).freeTypeVars <|
                Range.mem_map_of_mem mem
              have := Type.TypeVar_open_inj_of_not_mem_freeTypeVars
                Type.not_mem_freeTypeVars_TypeVar_close aninAₛ'' Aₛeq
              rw [Function.comp, ← this, AₛopB'lc'.Type_open_TypeVar_close_eq_TypeVar_subst,
                  Blc.Type_open_TypeVar_subst_dist]
            ), AopB'lc'.Type_open_TypeVar_close_eq_TypeVar_subst, Blc.Type_open_TypeVar_subst_dist,
            Monotype.Monotype_open]
        let B'lc' := B'lc.weaken (n := n)
        rw [Nat.zero_add] at B'lc'
        rw [← QualifiedType.TypeVar_open, ← TypeVar_open,
            ← B'lc'.TypeVar_open_TypeVar_close_id (a := a)] at τ'ke
        rw [Monotype.freeTypeVars] at aninσ
        let τ'ke' := τ'ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninσ
          Type.not_mem_freeTypeVars_TypeVar_close τke
        rw [B'lc'.Type_open_TypeVar_close_eq_TypeVar_subst] at τ'ke'
        apply tc _ τ'ke' (TCₛ := TCₛ) (m := m) (σ := σ')
        let ⟨a'nea, _⟩ := List.not_mem_cons.mp a'nin
        let aninA := Type.not_mem_freeTypeVars_TypeVar_open_drop <|
          (Aki a').not_mem_freeTypeVars_of <| List.not_mem_singleton.mpr a'nea.symm
        rw [Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninA, Range.map_eq_of_eq_of_mem'' (by
          intro i mem
          show _ = (TCₛ i, Aₛ i)
          let aninAₛ := Type.not_mem_freeTypeVars_TypeVar_open_drop <|
            Aₛki a' i mem |>.not_mem_freeTypeVars_of <| List.not_mem_singleton.mpr a'nea.symm
          rw [Type.TypeVar_subst_id_of_not_mem_freeTypeVars aninAₛ]
        )]
        exact inΓc
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
              let ρke' := ρke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
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
              let Blc := τke.soundness Γcw Γwe κ₀e |>.TypeVarLocallyClosed_of
              rw [Blc.Type_open_TypeVar_open_comm <| Nat.succ_ne_zero _]
              have := ψke a' a'ninI
              rw [ψ.TypeVar_open_comm <| Nat.succ_ne_zero _,
                  ← QualifiedType.TypeVar_open, ← TypeVar_open,
                  A.TypeVar_open_comm <| Nat.succ_ne_zero _, ← TypeEnvironment.append] at this
              have := this.Monotype_open_preservation Γcw (ΓaΓ'we.typeExt a'ninΓaΓ'' κe)
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
      | .ind ρ =>
        rw [Monotype.TypeVar_open] at σke
        generalize A'eq : A.TypeVar_open a n = A' at σke
        let .ind I₀ I₁ ρke κe keBᵣ keBₗ (κ := κ) := σke
        rcases Type.ind_evidence_inversion A'eq with ⟨Bᵣ', Bₗ', A'', rfl, rfl, rfl, rfl⟩
        rw [Monotype.Monotype_open]
        simp [Type.Type_open]
        rw [← QualifiedType.TypeVar_open, ← TypeVar_open] at ρke
        rw [Monotype.freeTypeVars] at aninσ
        simp [Type.freeTypeVars] at aninA
        let ⟨aninBᵣ', aninBₗ', aninA''⟩ := aninA
        let ρke' := ρke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' aninσ aninA'' τke
        apply «ind» (I₀ ++ [[(Γ, a : κ₀, Γ')]].typeVarDom) (I₁ ++ [[(Γ, a : κ₀, Γ')]].typeVarDom)
          ρke' κe
        · intro aₗ aₗnin aₜ aₜnin aₚ aₚnin aᵢ aᵢnin aₙ aₙnin
          let ⟨aₗninI₀, aₗninΓaΓ'⟩ := List.not_mem_append'.mp aₗnin

          let ⟨aₜneaₗ, aₜnin'⟩ := List.not_mem_cons.mp aₜnin
          let ⟨aₜninI₀, aₜninΓaΓ'⟩ := List.not_mem_append'.mp aₜnin'
          let aₜninI₀' := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninI₀⟩
          let aₜninΓaΓ'' := List.not_mem_cons.mpr ⟨aₜneaₗ, aₜninΓaΓ'⟩

          let ⟨aₚneaₜ, aₚnin'⟩ := List.not_mem_cons.mp aₚnin
          let ⟨aₚneaₗ, aₚnin''⟩ := List.not_mem_cons.mp aₚnin'
          let ⟨aₚninI₀, aₚninΓaΓ'⟩ := List.not_mem_append'.mp aₚnin''
          let aₚninI₀' := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninI₀⟩⟩
          let aₚninΓaΓ'' := List.not_mem_cons.mpr ⟨aₚneaₜ, List.not_mem_cons.mpr ⟨aₚneaₗ, aₚninΓaΓ'⟩⟩

          let ⟨aᵢneaₚ, aᵢnin'⟩ := List.not_mem_cons.mp aᵢnin
          let ⟨aᵢneaₜ, aᵢnin''⟩ := List.not_mem_cons.mp aᵢnin'
          let ⟨aᵢneaₗ, aᵢnin'''⟩ := List.not_mem_cons.mp aᵢnin''
          let ⟨aᵢninI₀, aᵢninΓaΓ'⟩ := List.not_mem_append'.mp aᵢnin'''
          let aᵢninI₀' := List.not_mem_cons.mpr
            ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninI₀⟩⟩⟩
          let aᵢninΓaΓ'' := List.not_mem_cons.mpr
            ⟨aᵢneaₚ, List.not_mem_cons.mpr ⟨aᵢneaₜ, List.not_mem_cons.mpr ⟨aᵢneaₗ, aᵢninΓaΓ'⟩⟩⟩

          let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
          let ⟨aₙneaₚ, aₙnin''⟩ := List.not_mem_cons.mp aₙnin'
          let ⟨aₙneaₜ, aₙnin'''⟩ := List.not_mem_cons.mp aₙnin''
          let ⟨aₙneaₗ, aₙnin''''⟩ := List.not_mem_cons.mp aₙnin'''
          let ⟨aₙninI₀, aₙninΓaΓ'⟩ := List.not_mem_append'.mp aₙnin''''
          let aₙninI₀' := List.not_mem_cons.mpr ⟨
            aₙneaᵢ,
            List.not_mem_cons.mpr
              ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninI₀⟩⟩⟩
          ⟩
          let aₙninΓaΓ'' := List.not_mem_cons.mpr ⟨
            aₙneaᵢ,
            List.not_mem_cons.mpr
              ⟨aₙneaₚ, List.not_mem_cons.mpr ⟨aₙneaₜ, List.not_mem_cons.mpr ⟨aₙneaₗ, aₙninΓaΓ'⟩⟩⟩
          ⟩

          let keBᵣ' : KindingAndElaboration Γc
            [[(Γ, a : κ₀, Γ', aₗ : L, aₜ : κ, aₚ : R κ, aᵢ : R κ, aₙ : R κ)]]
            ((qual (.mono (.concat (.var aₚ) (.comm .non) (.row [(.var aₗ, .var aₜ)] none)
              (.var aᵢ)))).TypeVar_open a (n + 6)) .constr
            ((((((Bᵣ'.TypeVar_open aₗ 4).TypeVar_open aₜ 3).TypeVar_open aₚ 2)
              |>.TypeVar_open aᵢ 1).TypeVar_open aₙ 0).TypeVar_open a (n + 6)) := by
            rw [TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
                Monotype.TypeVar_open, if_neg nofun, Monotype.TypeVar_open, if_neg nofun,
                Monotype.TypeVar_open, Monotype.TypeVar_open, List.mapMem_eq_map,
                List.map_singleton, Monotype.TypeVar_open, if_neg nofun, Monotype.TypeVar_open,
                if_neg nofun,
                Type.TypeVar_open_comm (m := 0) (n := n + 6) _ (Nat.zero_ne_add_one _),
                Type.TypeVar_open_comm (m := 1) (n := n + 6) _ (by simp_arith),
                Type.TypeVar_open_comm (m := 2) (n := n + 6) _ (by simp_arith),
                Type.TypeVar_open_comm (m := 3) (n := n + 6) _ (by simp_arith),
                Type.TypeVar_open_comm (m := 4) (n := n + 6) _ (by simp_arith)]
            exact keBᵣ _ aₗninI₀ _ aₜninI₀' _ aₚninI₀' _ aᵢninI₀' _ aₙninI₀'
          let aneaₗ : a ≠ aₗ := by
            rw [TypeEnvironment.typeVarDom_append] at aₗninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aₗninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aneaₚ : a ≠ aₚ := by
            rw [TypeEnvironment.typeVarDom_append] at aₚninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aₚninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aneaₜ : a ≠ aₜ := by
            rw [TypeEnvironment.typeVarDom_append] at aₜninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aₜninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aneaᵢ : a ≠ aᵢ := by
            rw [TypeEnvironment.typeVarDom_append] at aᵢninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aᵢninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aneaₙ : a ≠ aₙ := by
            rw [TypeEnvironment.typeVarDom_append] at aₙninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aₙninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aninΓ'aₗaₜaₚaᵢaₙ := List.not_mem_cons.mpr ⟨
            aneaₙ,
            List.not_mem_cons.mpr ⟨
              aneaᵢ,
              List.not_mem_cons.mpr
                ⟨aneaₚ, List.not_mem_cons.mpr ⟨aneaₜ, List.not_mem_cons.mpr ⟨aneaₗ, aninΓ'⟩⟩⟩
            ⟩
          ⟩
          let keBᵣ'' := keBᵣ'.Monotype_open_preservation Γcw
            (ΓaΓ'we.typeExt aₗninΓaΓ' .label |>.typeExt aₜninΓaΓ'' κe |>.typeExt aₚninΓaΓ'' κe.row
              |>.typeExt aᵢninΓaΓ'' κe.row |>.typeExt aₙninΓaΓ'' κe.row)
            aninΓ'aₗaₜaₚaᵢaₙ (by
              simp [freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars]
              exact ⟨aneaₚ, aneaₗ, aneaₜ, aneaᵢ⟩)
            (Type.not_mem_freeTypeVars_TypeVar_open_intro
              (Type.not_mem_freeTypeVars_TypeVar_open_intro
                (Type.not_mem_freeTypeVars_TypeVar_open_intro
                  (Type.not_mem_freeTypeVars_TypeVar_open_intro
                    (Type.not_mem_freeTypeVars_TypeVar_open_intro aninBᵣ' aneaₗ) aneaₜ) aneaₚ) aneaᵢ)
              aneaₙ)
            τke
          let ⟨_, .typeExt Γwe ..⟩ := ΓaΓ'we.append_left_elim
          let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
          let Blc := τke.soundness Γcw Γwe κ₀e |>.TypeVarLocallyClosed_of
          rw [TypeEnvironment.TypeVar_subst, TypeEnvironment.TypeVar_subst,
              TypeEnvironment.TypeVar_subst, TypeEnvironment.TypeVar_subst,
              TypeEnvironment.TypeVar_subst, ← Blc.Type_open_TypeVar_open_comm (Nat.succ_ne_zero _),
              ← Blc.weaken (n := 1).Type_open_TypeVar_open_comm (by simp_arith),
              ← Blc.weaken (n := 2).Type_open_TypeVar_open_comm (by simp_arith),
              ← Blc.weaken (n := 3).Type_open_TypeVar_open_comm (by simp_arith),
              ← Blc.weaken (n := 4).Type_open_TypeVar_open_comm (by simp_arith),
              Monotype_open, QualifiedType.Monotype_open, Monotype.Monotype_open,
              Monotype.Monotype_open, if_neg nofun, Monotype.Monotype_open, if_neg nofun,
              Monotype.Monotype_open, Monotype.Monotype_open, List.mapMem_eq_map,
              List.map_singleton, Monotype.Monotype_open, if_neg nofun, Monotype.Monotype_open,
              if_neg nofun] at keBᵣ''
          exact keBᵣ''
        · intro aᵢ aᵢnin aₙ aₙnin
          let ⟨aᵢninI₁, aᵢninΓaΓ'⟩ := List.not_mem_append'.mp aᵢnin
          let ⟨aₙneaᵢ, aₙnin'⟩ := List.not_mem_cons.mp aₙnin
          let ⟨aₙninI₁, aₙninΓaΓ'⟩ := List.not_mem_append'.mp aₙnin'
          let aₙninI₁' := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninI₁⟩
          let aₙninΓaΓ'' := List.not_mem_cons.mpr ⟨aₙneaᵢ, aₙninΓaΓ'⟩
          let keBₗ' : KindingAndElaboration Γc [[(Γ, a : κ₀, Γ', aᵢ : R κ, aₙ : R κ)]]
            ((qual (.mono (.concat (.var aᵢ) (.comm .non) (.var aₙ) ρ))).TypeVar_open a m) .constr
            (((Bₗ'.TypeVar_open aᵢ 1).TypeVar_open aₙ).TypeVar_open a (n + 6)) := by
            rw [TypeVar_open, QualifiedType.TypeVar_open, Monotype.TypeVar_open,
                Monotype.TypeVar_open, if_neg nofun, Monotype.TypeVar_open, if_neg nofun,
                Monotype.TypeVar_open,
                Type.TypeVar_open_comm (m := 0) (n := n + 6) _ (Nat.zero_ne_add_one _),
                Type.TypeVar_open_comm (m := 1) (n := n + 6) _ (by simp_arith)]
            exact keBₗ _ aᵢninI₁ _ aₙninI₁'
          let aneaᵢ : a ≠ aᵢ := by
            rw [TypeEnvironment.typeVarDom_append] at aᵢninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aᵢninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aneaₙ : a ≠ aₙ := by
            rw [TypeEnvironment.typeVarDom_append] at aₙninΓaΓ'
            let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aₙninΓaΓ'
            symm
            exact List.ne_of_not_mem_cons aninΓa
          let aninΓ'aᵢaₙ := List.not_mem_cons.mpr ⟨aneaₙ, List.not_mem_cons.mpr ⟨aneaᵢ, aninΓ'⟩⟩
          let keBₗ'' := keBₗ'.Monotype_open_preservation Γcw
            (ΓaΓ'we.typeExt aᵢninΓaΓ' κe.row |>.typeExt aₙninΓaΓ'' κe.row) aninΓ'aᵢaₙ (by
              simp [freeTypeVars, QualifiedType.freeTypeVars, Monotype.freeTypeVars]
              exact ⟨aneaᵢ, aneaₙ, aninσ⟩) (Type.not_mem_freeTypeVars_TypeVar_open_intro
              (Type.not_mem_freeTypeVars_TypeVar_open_intro aninBₗ' aneaᵢ) aneaₙ) τke
          let ⟨_, .typeExt Γwe ..⟩ := ΓaΓ'we.append_left_elim
          let ⟨_, κ₀e⟩ := κ₀.Elaboration_total
          let Blc := τke.soundness Γcw Γwe κ₀e |>.TypeVarLocallyClosed_of
          rw [TypeEnvironment.TypeVar_subst, TypeEnvironment.TypeVar_subst,
              ← Blc.Type_open_TypeVar_open_comm (Nat.succ_ne_zero _),
              ← Blc.weaken (n := 1).Type_open_TypeVar_open_comm (by simp_arith), Monotype_open,
              QualifiedType.Monotype_open, Monotype.Monotype_open, Monotype.Monotype_open,
              Monotype.Monotype_open, Monotype.Monotype_open] at keBₗ''
          exact keBₗ''
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
        let concatke'' := concatke'.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' (by
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
        let ψke' := ψke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ' (aninσ <| List.mem_append_left _ ·)
          (aninA <| List.mem_append_left _ ·) τke
        let γ'ke' := γ'ke.Monotype_open_preservation Γcw ΓaΓ'we aninΓ'
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
      let Blc := τke.soundness Γcw Γwe κ₀e |>.TypeVarLocallyClosed_of
      rw [Blc.Type_open_TypeVar_open_comm <| Nat.succ_ne_zero _]
      have := σ'ke a' a'ninI
      rw [σ'.TypeVar_open_comm <| Nat.succ_ne_zero _,
          A.TypeVar_open_comm <| Nat.succ_ne_zero _, ← TypeEnvironment.append] at this
      rw [freeTypeVars] at aninσ
      rw [Type.freeTypeVars] at aninA
      have := this.Monotype_open_preservation Γcw (ΓaΓ'we.typeExt a'ninΓaΓ'' κe)
        (List.not_mem_cons.mpr ⟨ne, aninΓ'⟩) (not_mem_freeTypeVars_TypeVar_open_intro aninσ ne)
        (Type.not_mem_freeTypeVars_TypeVar_open_intro aninA ne) τke
      rw [← TypeEnvironment.append, ← TypeEnvironment.TypeVar_subst,
          ← σ'.TypeVar_open_Monotype_open_comm τlc <| Nat.zero_ne_add_one _]
      exact this
    all_goals nomatch σke
termination_by [[Γ, a : κ₀, Γ']].sizeOf' + σ.sizeOf'
decreasing_by
  all_goals simp_arith; try simp_arith [h, TypeEnvironment.append, TypeEnvironment.sizeOf']
  · simp_arith [TypeEnvironment.sizeOf'_append, TypeEnvironment.sizeOf']
  · rw [← List.getD_eq_getElem?_getD, ← List.get!_eq_getD]
    apply Nat.le_add_right_of_le
    apply Nat.le_add_right_of_le
    apply List.le_sum_of_mem'
    apply List.mem_map.mpr
    exact ⟨_, List.get!_mem ilt, rfl⟩
  · rw [← List.getD_eq_getElem?_getD, ← List.get!_eq_getD]
    apply Nat.le_add_right_of_le
    apply Nat.le_trans _ <| Nat.le_add_left _ _
    apply List.le_sum_of_mem'
    apply List.mem_map.mpr
    exact ⟨_, List.get!_mem ilt, rfl⟩
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _
  · exact Nat.succ_le_of_lt <| Monotype.sizeOf'_pos _
  · exact Nat.succ_le_of_lt <| QualifiedType.sizeOf'_pos _
  · simp_arith [TypeEnvironment.sizeOf'_append, TypeEnvironment.sizeOf']

theorem TypeEnvironment.WellFormednessAndElaboration.TypeVar_subst_preservation
  (ΓaΓ'we : [[Γc ⊢ Γ, a : κ, Γ' ⇝ Δ, a : K, Δ']]) (Γcw : [[⊢c Γc]]) (aninΓ' : [[a ∉ dom(Γ')]])
  (τke : [[Γc; Γ ⊢ τ : κ ⇝ B]]) : [[Γc ⊢ Γ, Γ' [τ / a] ⇝ Δ, Δ' [B / a] ]] := by match Γ' with
  | .empty => match Δ' with
    | .empty =>
      let .typeExt Γwe .. := ΓaΓ'we
      exact Γwe
    | .typeExt .. =>
      let .typeExt Γwe aninΓ _ := ΓaΓ'we
      let aninΔaΔ'' := Γwe.TypeVarNotInDom_preservation aninΓ
      rw [Environment.TypeVarNotInDom, Environment.TypeVarInDom,
          Environment.typeVarDom_append] at aninΔaΔ''
      let ⟨_, aninΔa⟩ := List.not_mem_append'.mp aninΔaΔ''
      nomatch aninΔa <| .head _
  | .typeExt .. => match Δ' with
    | .empty =>
      let .typeExt _ aninΓaΓ'' _ := ΓaΓ'we
      rw [TypeEnvironment.TypeVarNotInDom, TypeEnvironment.typeVarDom_append] at aninΓaΓ''
      let ⟨_, aninΓa⟩ := List.not_mem_append'.mp aninΓaΓ''
      nomatch aninΓa <| .head _
    | .typeExt .. =>
      let .typeExt ΓaΓ''we a'ninΓaΓ'' κ'e := ΓaΓ'we
      rw [TypeEnvironment.TypeVar_subst, Environment.TypeVar_subst, TypeEnvironment.append,
        Environment.append]
      rw [TypeEnvironment.TypeVarNotInDom] at aninΓ'
      let aninΓ'' := List.not_mem_of_not_mem_cons aninΓ'
      rw [TypeEnvironment.TypeVarNotInDom, TypeEnvironment.typeVarDom_append] at a'ninΓaΓ''
      let ⟨a'ninΓ'', a'ninΓa⟩ := List.not_mem_append'.mp a'ninΓaΓ''
      let a'ninΓ := List.not_mem_of_not_mem_cons a'ninΓa
      rw [← TypeEnvironment.TypeVarNotInDom] at a'ninΓ''
      let a'ninΓ'' := a'ninΓ''.TypeVar_subst_preservation (a' := a) (τ := τ)
      let a'ninΓΓ'' := List.not_mem_append'.mpr ⟨a'ninΓ'', a'ninΓ⟩
      rw [← TypeEnvironment.typeVarDom_append] at a'ninΓΓ''
      exact ΓaΓ''we.TypeVar_subst_preservation Γcw aninΓ'' τke |>.typeExt a'ninΓΓ'' κ'e
  | .termExt .. =>
    let .termExt .. := Δ'
    let .termExt ΓaΓ''we xninΓaΓ'' σke := ΓaΓ'we
    rw [TypeEnvironment.TypeVar_subst, Environment.TypeVar_subst, TypeEnvironment.append,
        Environment.append]
    rw [TypeEnvironment.TermVarNotInDom, TypeEnvironment.termVarDom_append] at xninΓaΓ''
    let ⟨xninΓ'', xninΓa⟩ := List.not_mem_append'.mp xninΓaΓ''
    rw [← TypeEnvironment.TermVarNotInDom] at xninΓ''
    let xninΓ'' := xninΓ''.TypeVar_subst_preservation (a := a) (τ := τ)
    rw [TypeEnvironment.termVarDom] at xninΓa
    let xninΓΓ'' := List.not_mem_append'.mpr ⟨xninΓ'', xninΓa⟩
    rw [← TypeEnvironment.termVarDom_append] at xninΓΓ''
    apply ΓaΓ''we.TypeVar_subst_preservation Γcw aninΓ' τke |>.termExt xninΓΓ'' _
    let σlc := σke.TypeVarLocallyClosed_of
    let Blc := σke.soundness Γcw ΓaΓ''we .star |>.TypeVarLocallyClosed_of
    rw [← σlc.TypeVar_open_TypeVar_close_id (a := a),
        ← Blc.TypeVar_open_TypeVar_close_id (a := a)] at σke
    have := σke.Monotype_open_preservation Γcw ΓaΓ''we aninΓ' not_mem_freeTypeVars_TypeVar_close
      Type.not_mem_freeTypeVars_TypeVar_close τke
    rw [σlc.Monotype_open_TypeVar_close_eq_TypeVar_subst,
        Blc.Type_open_TypeVar_close_eq_TypeVar_subst] at this
    exact this
  | .constrExt .. =>
    let .termExt .. := Δ'
    let .constrExt ΓaΓ''we xninΓaΓ'' ψke := ΓaΓ'we
    rw [TypeEnvironment.TypeVar_subst, Environment.TypeVar_subst, TypeEnvironment.append,
        Environment.append]
    rw [TypeEnvironment.TermVarNotInDom, TypeEnvironment.termVarDom_append] at xninΓaΓ''
    let ⟨xninΓ'', xninΓa⟩ := List.not_mem_append'.mp xninΓaΓ''
    rw [← TypeEnvironment.TermVarNotInDom] at xninΓ''
    let xninΓ'' := xninΓ''.TypeVar_subst_preservation (a := a) (τ := τ)
    rw [TypeEnvironment.termVarDom] at xninΓa
    let xninΓΓ'' := List.not_mem_append'.mpr ⟨xninΓ'', xninΓa⟩
    rw [← TypeEnvironment.termVarDom_append] at xninΓΓ''
    apply ΓaΓ''we.TypeVar_subst_preservation Γcw aninΓ' τke |>.constrExt xninΓΓ'' _
    let ψlc := ψke.TypeVarLocallyClosed_of
    let Blc := ψke.soundness Γcw ΓaΓ''we .constr |>.TypeVarLocallyClosed_of
    rw [← ψlc.TypeVar_open_TypeVar_close_id (a := a),
        ← Blc.TypeVar_open_TypeVar_close_id (a := a)] at ψke
    have := ψke.Monotype_open_preservation Γcw ΓaΓ''we aninΓ' not_mem_freeTypeVars_TypeVar_close
      Type.not_mem_freeTypeVars_TypeVar_close τke
    rw [ψlc.Monotype_open_TypeVar_close_eq_TypeVar_subst,
        Blc.Type_open_TypeVar_close_eq_TypeVar_subst] at this
    exact this
termination_by [[Γ, a : κ, Γ']].sizeOf'
decreasing_by
  all_goals simp_arith [TypeEnvironment.append, TypeEnvironment.sizeOf']

end

end TabularTypeInterpreter
