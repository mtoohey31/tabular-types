import Lott.Elab.Nat
import TabularTypeInterpreter.RuleSets
import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Kind

namespace TabularTypeInterpreter.«F⊗⊕ω»

locally_nameless
metavar (tex pre := "\\targetpre", post := "\\targetpost") TypeVar, a

nonterminal (tex pre := "\\targetpre", post := "\\targetpost") «Type», A, B, C, T :=
  | a                      : var
  | "λ " a " : " K ". " A  : lam (bind a in A)
  | A B                    : app
  | "∀ " a " : " K ". " A  : «forall» (bind a in A)
  | A " → " B              : arr
  | "{" sepBy(A, ", ") "}" : list
  | A " ⟦" B "⟧"           : listApp
  | "⊗ " A                 : prod
  | "⊕ " A                 : sum
  | "(" A ")"              : paren notex (expand := return A)

termonly
attribute [aesop norm (rule_sets := [topen])] Type.Type_open Type.TypeVar_open

namespace «Type»

termonly
@[app_unexpander TypeVar_open]
def delabTVOpen: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a)
  | `($(_) $T $a 0) =>
    `( $T^$a )
  | `($(_) $T $a $n) =>
    `( $T^$a @ $n )
  | _ => throw ()

termonly
@[app_unexpander Type_open]
def delabTOpen: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a)
  | `($(_) $T $a 0) =>
    `( $T^^$a )
  | `($(_) $T $a $n) =>
    `( $T^^$a @ $n )
  | _ => throw ()

termonly
@[app_unexpander TypeVar_subst]
def delabTVSubst: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a $A) =>
    let info := Lean.SourceInfo.none
    let mapsto := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "↦") }
    `( $T[$a $mapsto $A])
  | _ => throw ()

end «Type»

namespace «Type»

termonly
inductive TypeVarLocallyClosed_aux : «Type» → Prop where
| var_free: ∀{x}, (var (TypeVar.free x)).TypeVarLocallyClosed_aux
| lam: ∀{I: List _} {K A}, (∀a ∉ I, (A.TypeVar_open a).TypeVarLocallyClosed_aux) → (Type.lam K A).TypeVarLocallyClosed_aux
| app: ∀{T1 T2}, T1.TypeVarLocallyClosed_aux → T2.TypeVarLocallyClosed_aux → (Type.app T1 T2).TypeVarLocallyClosed_aux
| forall: ∀{I: List _} {K A}, (∀a ∉ I, (A.TypeVar_open a).TypeVarLocallyClosed_aux) → (Type.forall K A).TypeVarLocallyClosed_aux
| arr: ∀{T1 T2}, T1.TypeVarLocallyClosed_aux → T2.TypeVarLocallyClosed_aux → (Type.arr T1 T2).TypeVarLocallyClosed_aux
| list: ∀{Tl}, (∀T ∈ Tl, T.TypeVarLocallyClosed_aux) → (Type.list Tl).TypeVarLocallyClosed_aux
| listApp: ∀{T1 T2}, T1.TypeVarLocallyClosed_aux → T2.TypeVarLocallyClosed_aux → (Type.listApp T1 T2).TypeVarLocallyClosed_aux
| prod: ∀{T}, T.TypeVarLocallyClosed_aux → (Type.prod T).TypeVarLocallyClosed_aux
| sum: ∀{T}, T.TypeVarLocallyClosed_aux → (Type.sum T).TypeVarLocallyClosed_aux

end «Type»

end TabularTypeInterpreter.«F⊗⊕ω»
