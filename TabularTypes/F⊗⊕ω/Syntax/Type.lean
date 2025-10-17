import Lott.Elab.Nat
import TabularTypes.RuleSets
import TabularTypes.«F⊗⊕ω».Syntax.Kind

namespace TabularTypes.«F⊗⊕ω»

run_cmd Lott.addNatAlias `i
run_cmd Lott.addNatAlias `j

locally_nameless
metavar (tex pre := "\\targetpre", post := "\\targetpost") TypeVar, a

nonterminal (tex pre := "\\targetpre", post := "\\targetpost") «Type», A, B, C, T notex :=
  | a                                          : var
  | "λ " a " : " K ". " A                      : lam (bind a in A)
  | A B                                        : app
  | "∀ " a " : " K ". " A                      : «forall» (bind a in A)
  | A " → " B                                  : arr
  | "{" e:sepBy(A, ", ") optional(" : " K) "}" : list (tex := s!"\\lottsym\{\\\{} {e} \\lottsym\{\\}}")
  | A " ⟦" B "⟧"                               : listApp
  | "⊗ " A                                     : prod
  | "⊕ " A                                     : sum
  | A "^^^" a "#" n                            : TypeVar_multi_open notex (id a) (expand := return .mkCApp `TabularTypes.«F⊗⊕ω».Type.TypeVar_multi_open #[A, a, n]) (tex := A)
  | A "^^^^" B "@@" i "#" n "/" a              : Type_multi_open notex (expand := return .mkCApp `TabularTypes.«F⊗⊕ω».Type.Type_multi_open #[A, B, n]) (tex := s!"{A}\\lottsepbycomprehension\{\\left[\{{B}}_\{{i}}/\{{a}}_\{{i}}\\right]}")
  | "(" A ")"                                  : paren notex (expand := return A)

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
@[app_unexpander TypeVar_close]
def delabTVClose: Lean.PrettyPrinter.Unexpander
  | `($(_) $T $a)
  | `($(_) $T $a 0) =>
    let info := Lean.SourceInfo.none
    let close := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "\\") }
    `( $close $a^$T )
  | `($(_) $T $a $n) =>
    let info := Lean.SourceInfo.none
    let close := { raw := Lean.Syntax.node1 info `str (Lean.Syntax.atom info "\\") }
    let d := `( $close $a@$n^$T )
    d
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
| list: ∀{Tl K?}, (∀T ∈ Tl, T.TypeVarLocallyClosed_aux) → (Type.list Tl K?).TypeVarLocallyClosed_aux
| listApp: ∀{T1 T2}, T1.TypeVarLocallyClosed_aux → T2.TypeVarLocallyClosed_aux → (Type.listApp T1 T2).TypeVarLocallyClosed_aux
| prod: ∀{T}, T.TypeVarLocallyClosed_aux → (Type.prod T).TypeVarLocallyClosed_aux
| sum: ∀{T}, T.TypeVarLocallyClosed_aux → (Type.sum T).TypeVarLocallyClosed_aux

end «Type»

end TabularTypes.«F⊗⊕ω»
