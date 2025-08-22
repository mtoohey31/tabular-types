import Lott.Elab.ImpliesJudgement
import Lott.Elab.NotJudgement
import Mathlib.Data.Rel
import Mathlib.Logic.Relation
import TabularTypeInterpreter.Data.List
import TabularTypeInterpreter.Logic.Relation
import TabularTypeInterpreter.«F⊗⊕ω».Lemmas.Kind
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Environment
import TabularTypeInterpreter.«F⊗⊕ω».Semantics.Type

namespace TabularTypeInterpreter.«F⊗⊕ω»

judgement_syntax A " = " B : Type.Eq

def Type.Eq := _root_.Eq (α := «Type»)

judgement_syntax A " ≠ " B : Type.Ne

def Type.Ne := _root_.Ne (α := «Type»)

judgement_syntax "value " A : Type.IsValue

judgement Type.IsValue where

─────── var {a : TypeVarId}
value a

∀ a ∉ I, value A^a
∀ A', A = A' a$0 ⇒ ¬lc_ A'
────────────────────────── lam (I : List TypeVarId)
value λ a : K. A

∀ a ∉ I, value A^a
────────────────── «forall» (I : List TypeVarId)
value ∀ a : K. A

value A
value B
─────────── arr
value A → B

</ value A@i // i in [:n] />
───────────────────────────────────────────── list
value {</ A@i // i in [:n] /> </ : K // b />}

value A
───────── prod
value ⊗ A

value A
───────── sum
value ⊕ A

value A
───────── varApp {a : TypeVarId}
value a A

value A₀ A₁
value B
─────────────── appApp
value (A₀ A₁) B

∀ K, A ≠ λ a : K. a$0
value A
───────────────────── listAppVar {a : TypeVarId}
value A ⟦a⟧

∀ K, A ≠ λ a : K. a$0
value A
value B₀ B₁
───────────────────── listAppApp
value A ⟦B₀ B₁⟧

judgement_syntax Δ " ⊢ " A " -> " B : SmallStep

judgement SmallStep where

Δ ⊢ A : K₁ ↦ K₂
──────────────────────── eta
Δ ⊢ λ a : K₁. A a$0 -> A

Δ ⊢ λ a : K₁. A : K₁ ↦ K₂
Δ ⊢ B : K₁
───────────────────────────── lamApp
Δ ⊢ (λ a : K₁. A) B -> A^^B/a

Δ ⊢ A : K₁ ↦ K₂
────────────────────────────────────────────────────────────────────────────────────────────── listAppList
Δ ⊢ A ⟦{</ B@i // i in [:n] /> </ : K₁ // b />}⟧ -> {</ A B@i // i in [:n] /> </ : K₂ // b />}

Δ ⊢ A : L K
─────────────────────────── listAppId
Δ ⊢ (λ a : K. a$0) ⟦A⟧ -> A

lc_ A₀
Δ ⊢ A₁ : K₁ ↦ K₂
────────────────────────────────────────────── listAppComp
Δ ⊢ A₀ ⟦A₁ ⟦B⟧⟧ -> (λ a : K₁. A₀ (A₁ a$0)) ⟦B⟧

∀ a ∉ I, Δ, a : K ⊢ A^a -> A'^a
─────────────────────────────── lam (I : List TypeVarId)
Δ ⊢ λ a : K. A -> λ a : K. A'

Δ ⊢ A -> A'
─────────────── appl
Δ ⊢ A B -> A' B

Δ ⊢ B -> B'
─────────────── appr
Δ ⊢ A B -> A B'

∀ a ∉ I, Δ, a : K ⊢ A^a -> A'^a
─────────────────────────────── «forall» (I : List TypeVarId)
Δ ⊢ ∀ a : K. A -> ∀ a : K. A'

Δ ⊢ A -> A'
─────────────────── arrl
Δ ⊢ A → B -> A' → B

Δ ⊢ B -> B'
─────────────────── arrr
Δ ⊢ A → B -> A → B'

Δ ⊢ A₁ -> A₁'
─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────── list
Δ ⊢ {</ A₀@i // i in [:m] />, A₁, </ A₂@j // j in [:n] /> </ : K // b />} -> {</ A₀@i // i in [:m] />, A₁', </ A₂@j // j in [:n] /> </ : K // b />}

Δ ⊢ A -> A'
─────────────────── listAppl
Δ ⊢ A ⟦B⟧ -> A' ⟦B⟧

Δ ⊢ B -> B'
─────────────────── listAppr
Δ ⊢ A ⟦B⟧ -> A ⟦B'⟧

Δ ⊢ A -> A'
─────────────── prod
Δ ⊢ ⊗ A -> ⊗ A'

Δ ⊢ A -> A'
─────────────── sum
Δ ⊢ ⊕ A -> ⊕ A'

judgement_syntax Δ " ⊢ " A " ->* " B : MultiSmallStep

abbrev MultiSmallStep := fun Δ => Relation.ReflTransGen (SmallStep Δ)

judgement_syntax Δ " ⊢"n A " ->* " B : MultiSmallStepIn

abbrev MultiSmallStepIn := fun Δ n => Relation.IndexedReflTransGen (SmallStep Δ) n

judgement_syntax Δ " ⊢ " A " <->* " B : EqSmallStep (tex := s!"{Δ} \\, \\lottsym\{⊢} \\, {A} \\, \\lottsym\{↔^*} \\, {B}")

abbrev EqSmallStep := fun Δ => Relation.EqvGen (SmallStep Δ)

judgement_syntax Δ " ⊢ " "SN" "(" A ")" : StronglyNormalizing

abbrev StronglyNormalizing := fun Δ => Acc (Rel.inv (SmallStep Δ))

judgement_syntax Δ " ⊢" n " SN" "(" A ")" : StronglyNormalizingIn (tex := s!"{Δ} \\, \\lottsym\{⊢}_\{{n}} \\, \\lottkw\{SN} \\lottsym\{(} {A} \\lottsym\{)}")

inductive StronglyNormalizingIn : Environment → Nat → «Type» → Prop where
  | intro (Bns : List («Type» × Nat)) (eb : ∀ {B}, (∃ n, (B, n) ∈ Bns) ↔ [[Δ ⊢ A -> B]])
    (sni : (∀ Bn ∈ Bns, StronglyNormalizingIn Δ Bn.snd Bn.fst))
    : StronglyNormalizingIn Δ (Bns.map Prod.snd |>.max?.map (· + 1) |>.getD 0) A

judgement_syntax Δ " ⊢ " "SN" K "(" A ")" : IndexedStronglyNormalizing (tex := s!"{Δ} \\, \\lottsym\{⊢} \\, \\lottkw\{SN}_\{{K}} \\lottsym\{(} {A} \\lottsym\{)}")

abbrev IndexedStronglyNormalizing : Environment → Kind → «Type» → Prop
  | Δ, [[*]], A => [[Δ ⊢ A : *]] ∧ [[Δ ⊢ SN(A)]]
  | Δ, [[K₁ ↦ K₂]], A =>
    [[Δ ⊢ A : K₁ ↦ K₂]] ∧ ∀ B Δ', Δ ≤ Δ' → [[Δ' ⊢ SN K₁ (B)]] → [[Δ' ⊢ SN K₂ (A B)]]
  | Δ, [[L K]], A =>
    [[Δ ⊢ A : L K]] ∧ [[Δ ⊢ SN(A)]] ∧ ∀ A' n b,
      [[Δ ⊢ A ->* {</ A'@i // i in [:n] /> </ : K // b />}]] → ∀ i ∈ [:n], [[Δ ⊢ SN K (A'@i)]]

nosubst
nonterminal Subst, δ :=
  | "ε"              : empty
  | δ ", " A " / " a : ext (id a)

namespace Subst

def find? (δ : Subst) (a : TypeVarId) : Option «Type» := match δ with
  | .empty => none
  | .ext δ' A a' => if a = a' then A else find? δ' a

def apply (δ : Subst) : «Type» → «Type»
  | .var a => match a with
    | .bound n => .var <| .bound n
    | .free a => if let some A := δ.find? a then
        A
      else
        .var <| .free a
  | .lam K A => .lam K <| apply δ A
  | .app A B => .app (apply δ A) (apply δ B)
  | .forall K A => .forall K <| apply δ A
  | .arr A B => .arr (apply δ A) (apply δ B)
  | .list As K? => .list (As.mapMem fun A _ => apply δ A) K?
  | .listApp A B => .listApp (apply δ A) (apply δ B)
  | .prod A => .prod <| apply δ A
  | .sum A => .sum <| apply δ A

instance : CoeFun Subst (fun _ => «Type» → «Type») where
  coe := Subst.apply

def «dom» : Subst → List TypeVarId
  | .empty => []
  | .ext δ _ a => a :: δ.dom

def freeTypeVars : Subst → List TypeVarId
  | .empty => []
  | .ext δ A _ => A.freeTypeVars ++ δ.freeTypeVars

end Subst

judgement_syntax δ " ⊨ " Δ " ⊣ " Δ' : SubstSatisfies

judgement SubstSatisfies := fun (δ : Subst) Δ Δ' => δ.dom.Unique ∧ δ.dom ⊆ Δ.typeVarDom ∧
    ∀ a K, [[a : K ∈ Δ]] → IndexedStronglyNormalizing Δ' K (δ (Type.var a))

judgement_syntax "neutral " A : Type.Neutral

abbrev Type.Neutral A :=
  (∀ K A', A ≠ [[λ a : K. A']]) ∧
    ∀ A' n K b, A = [[{</ A'@i // i in [:n] /> </ : K // b />}]] → ∀ i ∈ [:n], Neutral (A' i)
termination_by sizeOf A
decreasing_by
  rename A = _ => eq
  simp_arith [eq]
  apply Nat.le_add_right_of_le
  apply Nat.le_of_lt
  apply List.sizeOf_lt_of_mem
  apply Std.Range.mem_map_of_mem
  assumption

end TabularTypeInterpreter.«F⊗⊕ω»
