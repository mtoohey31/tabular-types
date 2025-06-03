import Lott.Data.Option
import TabularTypeInterpreter.Interpreter.«λπι»
import TabularTypeInterpreter.Interpreter.Basic

namespace TabularTypeInterpreter

namespace Interpreter

private
structure ElabState where
  nextFresh : Nat

private
abbrev ElabM := StateM ElabState

def freshId : ElabM «λπι».Id := do
  let { nextFresh } ← getModify fun st => { st with nextFresh := st.nextFresh + 1 }
  return { val := nextFresh }

instance : Coe MId «λπι».Id where
  coe | { val } => { val }

instance : Coe «λπι».Id MId where
  coe | { val } => { val }

open Std

namespace Monotype

def subst (τ τ' : Monotype) (i : TId) : Monotype := match τ with
  | var i' => if i == i' then τ' else var i'
  | lam i' κ τ'' => lam i' κ <| if i == i' then τ'' else subst τ'' τ' i
  | app ϕ τ'' => app (subst ϕ τ' i) (subst τ'' τ' i)
  | arr τ₀ τ₁ => app (subst τ₀ τ' i) (subst τ₁ τ' i)
  | label s => label s
  | floor ξ => floor <| subst ξ τ' i
  | comm u => comm u
  | row ξτ''s κ? =>
    row (.ofList (ξτ''s.toList.mapMem fun (ξ, τ'') _ => (subst ξ τ' i, subst τ'' τ' i))) κ?
  | prodOrSum Ξ μ => prodOrSum Ξ <| subst μ τ' i
  | lift => lift
  | contain ρ₀ μ ρ₁ => contain (subst ρ₀ τ' i) (subst μ τ' i) (subst ρ₁ τ' i)
  | concat ρ₀ μ ρ₁ ρ₂ => concat (subst ρ₀ τ' i) (subst μ τ' i) (subst ρ₁ τ' i) (subst ρ₂ τ' i)
  | tc s => tc s
  | all => all
  | ind => ind
  | split => split
  | list => list
  | int => int
  | str => str
  | «alias» s => «alias» s
termination_by sizeOf τ
decreasing_by
  all_goals simp_arith [sizeOf]
  all_goals (
    apply Nat.le_add_right_of_le
    apply Nat.le_of_lt <| Nat.lt_of_le_of_lt (m := sizeOf (ξ, τ'')) _ <| List.sizeOf_lt_of_mem ..
    · simp_arith
      simp_arith [sizeOf]
    · assumption
  )

inductive CommutativityPartialOrdering : Monotype → Monotype → Prop where
  | non : CommutativityPartialOrdering (comm .non) μ
  | comm : CommutativityPartialOrdering μ (comm .comm)

inductive RowEquivalence : Monotype → Monotype → Monotype → Type where
  | refl : RowEquivalence ρ μ ρ
  | trans : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence ρ₁ μ ρ₂ → RowEquivalence ρ₀ μ ρ₂
  | comm : List.Perm ξτs₀ ξτs₁ →
    RowEquivalence (row (.ofList ξτs₀) κ?) (comm .non) (row (.ofList ξτs₁) κ?)
  | liftL : RowEquivalence ((lift.app ϕ).app (row (.ofList ξτs) κ?)) μ
      (row (.ofList (ξτs.map fun (ξ, τ) => (ξ, ϕ.app τ))) κ?)
  | liftR : RowEquivalence (row (.ofList (ξτs.map fun (ξ, τ) => (ξ, ϕ.app τ))) κ?) μ
      ((lift.app ϕ).app (row (.ofList ξτs) κ?))

namespace RowEquivalence

def symm : RowEquivalence ρ₀ μ ρ₁ → RowEquivalence ρ₁ μ ρ₀
  | refl => refl
  | trans ρ₀₁re ρ₁₂re => trans ρ₁₂re.symm ρ₀₁re.symm
  | comm perm => comm perm.symm
  | liftL => liftR
  | liftR => liftL

def prodElab : RowEquivalence ρ₀ μ ρ₁ → ElabM «λπι».Term
  | refl | liftL | liftR => return .id
  | trans ρ₀₁re ρ₁₂re => do
    let i ← freshId
    let F₀₁ ← ρ₀₁re.prodElab
    let F₁₂ ← ρ₁₂re.prodElab
    return .lam i <| F₁₂.app <| F₀₁.app <| .var i
  | comm _ (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) => do
    let i ← freshId
    return .lam i <| .prodIntro <| ξτs₁.map fun (ξ₁, _) =>
      .prodElim (ξτs₀.findIdx (·.fst == ξ₁)) <| .var i

def sumElab : RowEquivalence ρ₀ μ ρ₁ → ElabM «λπι».Term
  | refl | liftL | liftR => return .id
  | trans ρ₀₁re ρ₁₂re => do
    let i ← freshId
    let F₀₁ ← ρ₀₁re.sumElab
    let F₁₂ ← ρ₁₂re.sumElab
    return .lam i <| F₁₂.app <| F₀₁.app <| .var i
  | comm _ (ξτs₀ := ξτs₀) (ξτs₁ := ξτs₁) => do
    let i ← freshId
    return .lam i <| .sumElim (.var i) <| ← ξτs₀.mapM fun (ξ₀, _) => do
      let i ← freshId
      return .lam i <| .sumIntro (ξτs₁.findIdx (·.fst == ξ₀)) <| .var i

end RowEquivalence

opaque ConstraintSolution : Monotype → Type

opaque ConstraintSolution.elab : ConstraintSolution τ → ElabM «λπι».Term

opaque ConstraintSolution.local : «λπι».Id → ConstraintSolution τ := sorry

end Monotype

open Monotype

namespace QualifiedType

def subst (γ : QualifiedType) (τ : Monotype) (i : TId) : QualifiedType := match γ with
  | .mono τ' => τ'.subst τ i
  | .qual ψ γ' => subst γ' τ i |>.qual <| ψ.subst τ i

end QualifiedType

open QualifiedType

namespace TypeScheme

def subst (σ : TypeScheme) (τ : Monotype) (i : TId) : TypeScheme := match σ with
  | .qual γ => γ.subst τ i
  | .quant i' κ σ' =>
    .quant i' κ <| if i == i' then σ' else subst σ' τ i

inductive Subtyping : TypeScheme → TypeScheme → Type where
  | refl : Subtyping σ σ
  | trans : Subtyping σ₀ σ₁ → Subtyping σ₁ σ₂ → Subtyping σ₀ σ₂
  | arr {τ₀ τ₁ τ₂ τ₃ : Monotype} : Subtyping τ₂ τ₀ → Subtyping τ₁ τ₃ →
    Subtyping (arr τ₀ τ₁) (arr τ₂ τ₃)
  | qual {ψ₀ ψ₁ : Monotype} {γ₀ γ₁ : QualifiedType} : Subtyping ψ₁ ψ₀ → Subtyping γ₀ γ₁ →
    Subtyping (γ₀.qual ψ₀) (γ₁.qual ψ₁)
  | scheme : Subtyping σ₀ (subst σ₁ (var i) i') → Subtyping (quant i κ σ₀) (quant i' κ σ₁)
  | prodOrSum {τ₀s τ₁s : List Monotype} :
    (∀ τ₀₁ ∈ List.zip τ₀s τ₁s, let (τ₀, τ₁) := τ₀₁; Subtyping τ₀ τ₁) →
    Subtyping ((prodOrSum Ξ μ).app (row (.ofList (List.zip ξs τ₀s)) κ?))
      ((prodOrSum Ξ μ).app (row (.ofList (List.zip ξs τ₁s)) κ?))
  | prodOrSumRow : RowEquivalence ρ₀ μ ρ₁ →
    Subtyping ((prodOrSum Ξ μ).app ρ₀) ((prodOrSum Ξ μ).app ρ₁)
  | decay : CommutativityPartialOrdering μ₀ μ₁ →
    Subtyping ((prodOrSum Ξ μ₀).app ρ) ((prodOrSum Ξ μ₁).app ρ)
  | never : Subtyping ((prodOrSum (uvars := false) .sum (comm .comm)).app (.row .nil (some star))) σ
  | contain : RowEquivalence ρ₀ μ ρ₂ → RowEquivalence ρ₁ μ ρ₃ →
    Subtyping (contain ρ₀ μ ρ₁) (contain ρ₂ μ ρ₃)
  | concat : RowEquivalence ρ₀ μ ρ₃ → RowEquivalence ρ₁ μ ρ₄ → RowEquivalence ρ₂ μ ρ₅ →
    Subtyping (concat ρ₀ μ ρ₁ ρ₂) (concat ρ₃ μ ρ₄ ρ₅)
  | tc {supers : List String} : (∀ s ∈ supers, Subtyping ((tc s).app τ₀) ((tc s).app τ₁)) →
    Subtyping (subst σ τ₀ i) (subst σ τ₁ i) → Subtyping ((tc s).app τ₀) ((tc s).app τ₁)
  | allRow : RowEquivalence ρ₀ (comm .comm) ρ₁ → Subtyping ((all.app ϕ).app ρ₀) ((all.app ϕ).app ρ₁)
  | split : Subtyping (concat ((lift.app ϕ).app ρ₀) μ ρ₁ ρ₂) (concat ((lift.app ϕ).app ρ₃) μ ρ₄ ρ₅) →
    Subtyping ((((split.app ϕ).app ρ₀).app ρ₁).app ρ₂)
      ((((split.app (uvars := false) ϕ).app ρ₃).app ρ₄).app ρ₅)
  | aliasₗ : Subtyping («alias» (uvars := false) s) σ
  | aliasᵣ : Subtyping σ («alias» (uvars := false) s)

def Subtyping.elab : Subtyping σ₀ σ₁ → ElabM «λπι».Term
  | refl | decay _ | aliasₗ | aliasᵣ => return .id
  | trans σ₀₁'st σ₁'₂st => do
    let i ← freshId
    return .lam i <| (← σ₁'₂st.elab).app <| (← σ₀₁'st.elab).app <| .var i
  | arr st st'
  | qual st st' => do
    let i ← freshId
    let i' ← freshId
    return .lam i <| .lam i' <| (← st'.elab).app <| .app (.var i) <| (← st.elab).app <| .var i'
  | scheme σ₀₁'st => σ₀₁'st.elab
  | prodOrSum τ₀₁sst (Ξ := Ξ) (τ₀s := τ₀s) (τ₁s := τ₁s) => do
    let i ← freshId
    match Ξ with
    | .prod => return .lam i <| .prodIntro <| ← τ₀s.zip τ₁s |>.mapMemIdxM fun j _ mem =>
        return (← τ₀₁sst _ mem |>.elab).app <| .prodElim j <| .var i
    | .sum => return .lam i <| .sumElim (.var i) <| ← τ₀s.zip τ₁s |>.mapMemIdxM fun j _ mem => do
        let i' ← freshId
        return .lam i' <| .sumIntro j <| (← τ₀₁sst _ mem |>.elab).app <| .var i'
  | prodOrSumRow ρ₀₁re (Ξ := Ξ) => match Ξ with | .prod => ρ₀₁re.prodElab | .sum => ρ₀₁re.sumElab
  | never => do
    let i ← freshId
    return .lam i <| .sumElim (.var i) []
  | contain ρ₀₂re ρ₁₃re => do
    let i ← freshId
    return .lam i <| ← contain.elab ρ₀₂re ρ₁₃re i
  | concat ρ₀₃re ρ₁₄re ρ₂₅re => do
    let i₀ ← freshId
    let i₁ ← freshId
    let i₂ ← freshId
    let i₃ ← freshId
    let i₄ ← freshId
    let i₅ ← freshId
    let i₆ ← freshId
    let i₇ ← freshId
    return .lam i₀ <| .prodIntro [
      .lam i₁ <| .lam i₂ <| (← ρ₂₅re.prodElab).app <| «λπι».Term.app (.var i₀)
        ((← ρ₀₃re.symm.prodElab).app (.var i₁)) |>.app ((← ρ₁₄re.symm.prodElab).app (.var i₂)),
      .lam i₃ <| .lam i₄ <| .lam i₅ <| («λπι».Term.var i₀) |>.app
        (.lam i₆ (.app (.var i₃) ((← ρ₀₃re.sumElab).app (.var i₆))))
        |>.app (.lam i₇ (.app (.var i₄) ((← ρ₁₄re.sumElab).app (.var i₇)))) |>.app <|
        (← ρ₂₅re.symm.sumElab).app (.var i₅),
      ← contain.elab ρ₀₃re ρ₂₅re i₀,
      ← contain.elab ρ₁₄re ρ₂₅re i₀
    ]
  | tc superst memberst (supers := supers) => do
    let i ← freshId
    return .lam i <| .prodIntro <| List.cons ((← memberst.elab).app (.prodElim 0 (.var i))) <|
      ← supers.mapMemIdxM fun j _ mem =>
        return (← superst _ mem |>.elab).app <| .prodElim (j + 1) <| .var i
  | allRow ρ₀₁re => ρ₀₁re.prodElab
  | split concatst => concatst.elab
where
  contain.elab {μ ρ₀ ρ₁ ρ₂ ρ₃} (ρ₀₂re : RowEquivalence ρ₀ μ ρ₂) (ρ₁₃re : RowEquivalence ρ₁ μ ρ₃)
    (i : «λπι».Id) : ElabM «λπι».Term := do
      let i' ← freshId
      let i'' ← freshId
      return «λπι».Term.prodIntro [
        .lam i' <| (← ρ₀₂re.prodElab).app <| .app (.var i) <|
          (← ρ₁₃re.symm.prodElab).app <| .var i',
        .lam i'' <| (← ρ₁₃re.sumElab).app <| .app (.var i) <| (← ρ₀₂re.symm.sumElab).app <| .var i''
      ]

end TypeScheme

open TypeScheme

def «λπι».Op.result : «λπι».Op → Monotype
  | .add | .sub | .mul | .div => .int
  | .eq | .lt | .le | .gt | .ge => .bool

namespace Term

-- Existence of this Typing term doesn't actually prove the Term has this type; this is only used to
-- guide elaboration, so it is up to the function producing this to ensure it is constructed
-- correctly, since mistakes will not necessarily be caught by the type checker.
inductive Typing : Term → TypeScheme → Type where
  | var : Typing (.var n) σ
  | lam {τ₁ : Monotype} : Typing M τ₁ → Typing (M.lam i) (arr τ₀ τ₁)
  | app {ϕ : Monotype} : Typing M (ϕ.arr τ) → Typing N ϕ → Typing (M.app N) τ
  | qualI {γ : QualifiedType} : (ConstraintSolution ψ → Typing M γ) → Typing M (γ.qual ψ)
  | qualE {γ : QualifiedType} : ConstraintSolution ψ → (Typing M (γ.qual ψ)) → Typing M γ
  | schemeI : Typing M σ → Typing M (quant i κ σ)
  | schemeE : Typing M (quant i κ σ) → Typing M (subst σ τ i)
  | let : Typing M σ₀ → Typing N σ₁ → Typing (M.let i (Option.someIf σ₀ b) N) σ₁
  | annot : Typing M σ → Typing (M.annot σ) σ
  | label : Typing (label s) (floor (uvars := false) (.label s))
  | prod : (∀ MNξτ ∈ MNs.zip ξτs, let ((_, N), _, τ) := MNξτ; Typing N τ) →
    Typing (prod (.ofList MNs))
      ((prodOrSum .prod (comm .non)).app (row (.ofList (uvars := false) ξτs) none))
  | sum {τ : Monotype} : Typing N τ →
    Typing (sum M N) ((prodOrSum .sum (comm .non)).app (row (.cons ξ τ .nil) none))
  | unlabel : Typing M ((prodOrSum Ξ μ).app (row (.cons (uvars := false) ξ τ .nil) none)) →
    Typing (unlabel M N) τ
  | prj : Typing M ((prodOrSum .prod μ).app ρ₀) → ConstraintSolution (contain ρ₁ μ ρ₀) →
    Typing (prj M) ((prodOrSum .prod μ).app ρ₁)
  | concat : Typing M ((prodOrSum .prod μ).app ρ₀) → Typing N ((prodOrSum .prod μ).app ρ₁) →
    ConstraintSolution (.concat ρ₀ μ ρ₁ ρ₂) → Typing (M.concat N) ((prodOrSum .prod μ).app ρ₂)
  | inj : Typing M ((prodOrSum .sum μ).app ρ₀) → ConstraintSolution (contain ρ₀ μ ρ₁) →
    Typing (prj M) ((prodOrSum .sum μ).app ρ₁)
  | elim : Typing M (((prodOrSum .prod μ).app ρ₀).arr τ) →
    Typing N (((prodOrSum .prod μ).app ρ₁).arr τ) → ConstraintSolution (.concat ρ₀ μ ρ₁ ρ₂) →
    Typing (M.elim N) (((prodOrSum .prod μ).app ρ₂).arr τ)
  | sub : Typing M σ₀ → Subtyping σ₀ σ₁ → Typing M σ₁
  | member : ConstraintSolution ((tc s).app τ) → Typing (member m) σ
  | ind : Typing M (quant iₗ .label (quant iₜ κ (quant iₚ κ.row (quant iᵢ κ.row (quant iₙ κ.row
      (qual (.concat (.var iₚ) (comm .non) (row (.cons (.var iₗ) (.var iₜ) .nil) none) (.var iᵢ))
        (qual (.concat (.var iᵢ) (comm .non) (.var iₙ) ρ)
          ((floor (.var iₗ)).arr ((ϕ.app (.var iₚ)).arr (ϕ.app (.var iᵢ))))))))))) →
    Typing N (ϕ.app (.row .nil (some κ))) → ConstraintSolution (Monotype.ind.app ρ) →
    Typing (ind ϕ ρ iₗ iₜ iₚ iᵢ iₙ M N) (ϕ.app ρ)
  | splitₚ : Typing M ((prodOrSum .prod (comm .comm)).app ρ₂) →
    ConstraintSolution ((((split.app ϕ).app ρ₀).app ρ₁).app ρ₂) →
    Typing (M.splitₚ ϕ) ((prodOrSum .prod (comm .non)).app
      (row (.cons
        (.label "match") ((prodOrSum .prod (comm .comm)).app ((lift.app ϕ).app ρ₀))
        (.cons (.label "rest") ((prodOrSum .prod (comm .comm)).app ρ₁) .nil)
      ) none))
  | splitₛ : Typing M (((prodOrSum .sum (comm .comm)).app ((lift.app ϕ).app ρ₀)).arr τ) →
    Typing N (((prodOrSum .sum (comm .comm)).app ρ₁).arr τ) →
    ConstraintSolution ((((split.app ϕ).app ρ₀).app ρ₁).app ρ₂) →
    Typing (M.splitₛ ϕ N) (((prodOrSum .sum (comm .comm)).app ρ₂).arr τ)
  | nil : Typing nil (list.app (uvars := false) τ)
  | cons {τ : Monotype} : Typing M τ → Typing N (list.app τ) → Typing (cons M N) (list.app τ)
  | fold : Typing fold (quant i star (quant iₐ star (qual (mono (arr (arr
      (.var iₐ) (arr (.var i) (.var iₐ))) (arr (.var iₐ) ((list.app (.var i)).arr (.var iₐ))))))))
  | int : Typing (int i) (Monotype.int (uvars := false))
  | op : Typing M (Monotype.int (uvars := false)) → Typing N (Monotype.int (uvars := false)) →
    Typing (op o M N) o.result
  | range : Typing range (Monotype.int.arr (uvars := false) (list.app .int))
  | str : Typing (str s) (Monotype.str (uvars := false))
  | throw : Typing throw (Monotype.str (uvars := false).arr σ)
  | def : Typing («def» s) σ

instance [Inhabited α] : Inhabited (Thunk α) where
  default := .mk fun _ => default

def Typing.elab : Typing M σ → ReaderT (HashMap String (Thunk «λπι».Term)) ElabM «λπι».Term
  | var (n := n) => return .var n
  | lam (i := i) M'ty => M'ty.elab <&> .lam i
  | app M'ty Nty => return (← M'ty.elab).app <| ← Nty.elab
  | qualI Mty'_of_so => do
    let i ← freshId
    «elab» (Mty'_of_so <| .local i) <&> .lam i
  | qualE ψso Mty' => return (← Mty'.elab).app <| ← ψso.elab
  | schemeI Mty' => Mty'.elab
  | schemeE Mty' => Mty'.elab
  | .let (i := i) M'ty Nty => return (← Nty.elab).lam i |>.app <| ← M'ty.elab
  | annot M'ty => M'ty.elab
  | label => return .prodIntro []
  | prod Nsty (MNs := MNs) (ξτs := ξτs) =>
    return .prodIntro <| ← MNs.zip ξτs |>.mapMemM (Nsty · · |>.elab)
  | sum Nty => Nty.elab <&> .sumIntro 0
  | unlabel M'ty (Ξ := Ξ) => match Ξ with
    | .prod => M'ty.elab <&> .prodElim 0
    | .sum => return (← M'ty.elab).sumElim [.id]
  | prj M'ty containso => return (← containso.elab).prodElim 0 |>.app <| ← M'ty.elab
  | concat M'ty Nty concatso =>
    return (← concatso.elab).prodElim 0 |>.app (← M'ty.elab) |>.app <| ← Nty.elab
  | inj M'ty containso => return (← containso.elab).prodElim 1 |>.app <| ← M'ty.elab
  | elim M'ty Nty concatso =>
    return (← concatso.elab).prodElim 1 |>.app (← M'ty.elab) |>.app <| ← Nty.elab
  | sub Mty' σ₀st =>
    return (← σ₀st.elab).app <| ← Mty'.elab
  | member TCτso => return (← TCτso.elab).prodElim 0
  | ind M'ty Nty indso => return (← indso.elab).app (← M'ty.elab) |>.app <| ← Nty.elab
  | splitₚ M'ty splitso => do
    let E ← M'ty.elab
    let F ← splitso.elab
    return .prodIntro [F.prodElim 2 |>.prodElim 0 |>.app E, F.prodElim 3 |>.prodElim 0 |>.app E]
  | splitₛ M'ty Nty splitso =>
    return (← splitso.elab).prodElim 1 |>.app (← M'ty.elab) |>.app <| ← Nty.elab
  | nil => return .nil
  | cons M'ty Nty => return .cons (← M'ty.elab) (← Nty.elab)
  | fold => return .fold
  | int (i := i) => return .int i
  | op M'ty Nty (o := o) => return .op o (← M'ty.elab) (← Nty.elab)
  | range => return .range
  | str (s := s) => return .str s
  | throw => return .throw
  | «def» (s := s) => return (← read)[s]!.get

end Term

namespace «λπι»

def Value.delab (V : Value) (σ : Interpreter.TypeScheme) : Option Interpreter.Term := do
  let .qual (.mono τ) := σ | none
  let ⟨E, EIs⟩ := V
  match E with
  | .lam i E' =>
    if E'Is : Is E' then
      let .arr _ τ₁ := τ | none
      let M ← delab ⟨E', E'Is⟩ τ₁
      return M.lam i
    none
  | .app E' F => match E' with
    | .fold =>
      let .arr τₐ (.arr (.app .list τₑ) _) := τ | none
      let FIs := match EIs with | .fold₁ h => h
      let M ← delab ⟨F, FIs⟩ <| τₐ.arr <| τₑ.arr τₐ
      some <| .app .fold M
    | .app .fold _ => none -- Can't determine accumulator type.
  | .prodIntro Es =>
    let .app (.prodOrSum .prod _) (.row ξτ's _) := τ | none
    let EsIs := match EIs with | .prodIntro h => h
    let true := Es.length == ξτ's.toList.length | none
    let V's : List { V' : Value // V'.val ∈ Es } := Es.mapMem fun E mem => ⟨⟨E, EsIs _ mem⟩, mem⟩
    let MNs ← V's.zip ξτ's.toList |>.mapM fun
      | (⟨V', _⟩, .label s, τ') => do
        let N ← V'.delab τ'
        return (TabularTypeInterpreter.Interpreter.Term.label s, N)
      | _ => none
    return .prod <| .ofList MNs
  | .sumIntro n E' => do
    let .app (.prodOrSum .sum _) (.row ξτ's _) := τ | none
    let E'Is := match EIs with | .sumIntro h => h
    let (.label s, τ') ← ξτ's.toList.get? n | none
    let N ← delab ⟨E', E'Is⟩ τ'
    return .sum (.label s) N
  | .nil => some .nil
  | .cons E' F => do
    let .app .list τ' := τ | none
    let ⟨E'Is, FIs⟩ : _ ∧ _ := match EIs with
      | .cons EIs FIs => ⟨EIs, FIs⟩
    let M ← delab ⟨E', E'Is⟩ τ'
    let N ← delab ⟨F, FIs⟩ <| .qual <| .mono <| .app .list τ'
    return M.cons N
  | .fold => some <| .fold
  | .int i => some <| .int i
  | .range => some <| .range
  | .str s => some <| .str s
  | .throw => some <| .throw
termination_by sizeOf V.val

end «λπι»

end Interpreter

end TabularTypeInterpreter
