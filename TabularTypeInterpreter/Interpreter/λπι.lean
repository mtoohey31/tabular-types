import Lott.Data.List

namespace TabularTypeInterpreter.Interpreter

structure Id (n : Name) where
  private val : Nat
deriving Hashable, DecidableEq, Inhabited, Ord

instance {n : Name} : ToString (Id n) where toString x := toString x.val

namespace «λπι»

nonrec
abbrev Id := Id `«λπι»

inductive Op where
  | add
  | sub
  | mul
  | div
  | eq
  | lt
  | le
  | gt
  | ge
deriving BEq, DecidableEq

instance : ToString Op where
  toString
    | .add => "+"
    | .sub => "-"
    | .mul => "*"
    | .div => "÷"
    | .eq => "=="
    | .lt => "<"
    | .le => "≤"
    | .gt => ">"
    | .ge => "≥"

inductive Term where
  | var : Id → Term
  | lam : Id → Term → Term
  | app : Term → Term → Term
  | prodIntro : List Term → Term
  | prodElim : Nat → Term → Term
  | sumIntro : Nat → Term → Term
  | sumElim : Term → List Term → Term
  | nil
  | cons : Term → Term → Term
  | fold
  | int : Int → Term
  | op : Op → Term → Term → Term
  | range
  | str : String → Term
  | throw

instance : Inhabited Term where
  default := .prodIntro []

namespace Term

def id := lam (.mk 0) <| var (.mk 0)

def unit := prodIntro []

end Term

inductive Value.Is : Term → Prop where
  | lam : Is (.lam i E)
  | prodIntro : (∀ E ∈ Es, Is E) → Is (.prodIntro Es)
  | sumIntro : Is E → Is (.sumIntro i E)
  | nil : Is .nil
  | cons : Is E → Is F → Is (.cons E F)
  | fold₀ : Is .fold
  | fold₁ : Is E → Is (.app .fold E)
  | fold₂ : Is E → Is F → Is (.app (.app .fold E) F)
  | int : Is (.int i)
  | range : Is .range
  | str : Is (.str s)
  | throw : Is .throw

def Value.Is.decide : Decidable (Is E) := match E with
  | .var _ => isFalse nofun
  | .lam _ _ => isTrue .lam
  | .app E' F => match E' with
    | .var _ => isFalse nofun
    | .lam _ _ => isFalse nofun
    | .app E'' F' => match E'' with
      | .var _ => isFalse nofun
      | .lam _ _ => isFalse nofun
      | .app .. => isFalse nofun
      | .prodIntro _ => isFalse nofun
      | .prodElim .. => isFalse nofun
      | .sumIntro .. => isFalse nofun
      | .sumElim .. => isFalse nofun
      | .nil => isFalse nofun
      | .cons .. => isFalse nofun
      | .fold => match decide (E := F') with
        | isFalse h => isFalse fun | .fold₂ h' _ => h h'
        | isTrue h => match decide (E := F) with
          | isFalse h' => isFalse fun | .fold₂ _ h'' => h' h''
          | isTrue h' => isTrue <| .fold₂ h h'
      | .int _ => isFalse nofun
      | .op .. => isFalse nofun
      | .range => isFalse nofun
      | .str _ => isFalse nofun
      | .throw => isFalse nofun
    | .prodIntro _ => isFalse nofun
    | .prodElim .. => isFalse nofun
    | .sumIntro .. => isFalse nofun
    | .sumElim .. => isFalse nofun
    | .nil => isFalse nofun
    | .cons .. => isFalse nofun
    | .fold => match decide (E := F) with
      | isFalse h => isFalse fun | .fold₁ h' => h h'
      | isTrue h => isTrue <| .fold₁ h
    | .int _ => isFalse nofun
    | .op .. => isFalse nofun
    | .range => isFalse nofun
    | .str _ => isFalse nofun
    | .throw => isFalse nofun
  | .prodIntro E's => match E's with
    | [] => isTrue <| .prodIntro nofun
    | E' :: E's' => match decide (E := E') with
      | isFalse h => isFalse fun | .prodIntro h' => h <| h' _ <| .head _
      | isTrue h => match decide (E := .prodIntro E's') with
        | isFalse h' => isFalse fun
          | .prodIntro h'' => h' <| .prodIntro fun _ mem => h'' _ <| .tail _ mem
        | isTrue h' =>
          let h'' := match h' with
            | .prodIntro h'' => h''
          isTrue <| .prodIntro fun
          | _, .head _ => h
          | _, .tail _ mem => h'' _ mem
  | .prodElim .. => isFalse nofun
  | .sumIntro _ E' => match decide (E := E') with
    | isFalse h => isFalse fun | .sumIntro h' => h h'
    | isTrue h => isTrue <| .sumIntro h
  | .sumElim .. => isFalse nofun
  | .nil => isTrue .nil
  | .cons E' F => match decide (E := E') with
    | isFalse h => isFalse fun | .cons h' _ => h h'
    | isTrue h => match decide (E := F) with
      | isFalse h' => isFalse fun | .cons _ h'' => h' h''
      | isTrue h' => isTrue <| .cons h h'
  | .fold => isTrue .fold₀
  | .int _ => isTrue .int
  | .op .. => isFalse nofun
  | .range => isTrue .range
  | .str _ => isTrue .str
  | .throw => isTrue .throw

instance : Decidable (Value.Is E) := Value.Is.decide

abbrev Value := { E : Term // Value.Is E }

namespace Value

instance : Inhabited Value where
  default := ⟨default, .prodIntro nofun⟩

def unit : Value := ⟨.prodIntro [], .prodIntro nofun⟩

def bool : Bool → Value
  | false => ⟨.sumIntro 0 unit, .sumIntro unit.property⟩
  | true => ⟨.sumIntro 1 unit, .sumIntro unit.property⟩

end Value

def Op.fn (i₀ i₁ : Int) : Op → Value
  | .add => ⟨.int <| i₀ + i₁, .int⟩
  | .sub => ⟨.int <| i₀ - i₁, .int⟩
  | .mul => ⟨.int <| i₀ * i₁, .int⟩
  | .div => ⟨.int <| i₀ / i₁, .int⟩
  | .eq => .bool <| i₀ == i₁
  | .lt => .bool <| i₀ < i₁
  | .le => .bool <| i₀ ≤ i₁
  | .gt => .bool <| i₀ > i₁
  | .ge => .bool <| i₀ ≥ i₁

namespace Term

def subst (E F : Term) (i : Id) : Term := match E with
  | var i' => if i' == i then F else var i'
  | lam i' E' => if i' == i then lam i' E' else lam i' <| subst E' F i
  | app E' F' => app (subst E' F i) (subst F' F i)
  | prodIntro Es => prodIntro <| Es.mapMem fun E' _ => subst E' F i
  | prodElim n E' => prodElim n <| subst E' F i
  | sumIntro n E' => sumIntro n <| subst E' F i
  | sumElim E' Fs => sumElim (subst E' F i) <| Fs.mapMem fun F' _ => subst F' F i
  | nil => nil
  | cons E' F' => cons (subst E' F i) (subst F' F i)
  | fold => fold
  | int i => int i
  | op o E' F' => op o (subst E' F i) (subst F' F i)
  | range => range
  | str s => str s
  | throw => throw

def multiSubst (E : Term) : List (Term × Id) → Term
  | [] => E
  | (F, i) :: Fis => E.subst F i |>.multiSubst Fis

inductive eval.Error where
  | freeVar (i : Id)
  | nonLamApp
  | nonProdIntroProdElim
  | invalidProdIdx (n l : Nat)
  | nonSumIntroSumElim
  | invalidSumIdx (n l : Nat)
  | nonLamSumElim
  | nonIntOperand
  | nonListFold
  | nonIntRange
  | nonStringThrow
  | throw (s : String)

instance [ToString Id] : ToString eval.Error where
  toString
    | .freeVar i => s!"encountered free variable: {i}"
    | .nonLamApp => "application of non-lambda term"
    | .nonProdIntroProdElim => "prod elimination of non-prod intro term"
    | .invalidProdIdx n l =>
      s!"prod elimination index {n} is out of range for prod with {l} entries"
    | .nonSumIntroSumElim => "sum elimination of non-sum intro term"
    | .invalidSumIdx n l =>
      s!"sum intro index {n} is out of range for sum elim with {l} entries"
    | .nonLamSumElim => "sum elim contained non-lambda term"
    | .nonIntOperand => "non-int term used as operand"
    | .nonListFold => "non-list term used as third argument for fold"
    | .nonIntRange => "non-int term used as argument for range"
    | .nonStringThrow => "non-string term used as argument for throw"
    | .throw s => s

partial
def eval (E : Term) : Except eval.Error Value := do match E with
  | var i => throw <| .freeVar i
  | lam i E => return ⟨lam i E, .lam⟩
  | app E F =>
    let VE ← eval E
    let V ← eval F
    match VE with
    | ⟨lam i E', _⟩ => eval <| subst E' V i
    | ⟨fold, _⟩ => return ⟨app fold V, .fold₁ V.property⟩
    | ⟨app fold F', appfoldIs⟩ =>
      let F'Is := match appfoldIs with | .fold₁ h => h
      return ⟨app (app fold F') V, .fold₂ F'Is V.property⟩
    | ⟨app (app fold F') Eᵢ, appappfoldIs⟩ => match V with
      | ⟨.nil, _⟩ => return ⟨Eᵢ, match appappfoldIs with | .fold₂ _ h => h⟩
      | ⟨.cons Eₙ V', _⟩ => eval <| fold.app F' |>.app (F'.app Eᵢ |>.app Eₙ) |>.app V'
      | _ => throw .nonListFold
    | ⟨range, _⟩ =>
      let ⟨int i, _⟩ := V | throw .nonIntRange
      return i.toNat.fold (init := (⟨nil, .nil⟩ : Value)) fun j _ V =>
        ⟨cons (.int j) V, .cons .int V.property⟩
    | ⟨.throw, _⟩ =>
      let ⟨.str Fs, _⟩ := V | throw .nonStringThrow
      throw <| .throw Fs
    | _ => throw .nonLamApp
  | prodIntro Es =>
    let Vs ← Es.mapM eval
    return ⟨
      prodIntro <| Vs.map (·.val),
      .prodIntro fun E mem => by
        let ⟨⟨_, EIsValue⟩, Vmem, .refl _⟩ := List.mem_map.mp mem
        exact EIsValue
    ⟩
  | prodElim n E =>
    let ⟨prodIntro Vs, VsAreValues⟩ ← eval E | throw .nonProdIntroProdElim
    let VsAreValues := match VsAreValues with | .prodIntro h => h
    if h : n < Vs.length then
      let V := Vs.get ⟨n, h⟩
      return ⟨V, VsAreValues V <| Vs.get_mem ⟨n, h⟩⟩
    else
      throw <| .invalidProdIdx n Vs.length
  | sumIntro n E =>
    let V ← eval E
    return ⟨sumIntro n V, .sumIntro V.property⟩
  | sumElim E Fs =>
    let ⟨sumIntro n VE, sumIntroIs⟩ ← eval E | throw .nonSumIntroSumElim
    let VEIs := match sumIntroIs with | .sumIntro h => h
    let VFs ← Fs.mapM eval
    let some VF := VFs.get? n | throw <| .invalidSumIdx n VFs.length
    let ⟨lam i F', _⟩ := VF | throw .nonLamSumElim
    eval <| subst F' VE i
  | nil => return ⟨nil, .nil⟩
  | cons E F =>
    let VE ← eval E
    let VF ← eval F
    return ⟨cons VE VF, .cons VE.property VF.property⟩
  | fold => return ⟨fold, .fold₀⟩
  | int i => return ⟨int i, .int⟩
  | op o E F =>
    let ⟨int Ei, _⟩ ← eval E | throw .nonIntOperand
    let ⟨int Fi, _⟩ ← eval F | throw .nonIntOperand
    return o.fn Ei Fi
  | range => return ⟨range, .range⟩
  | str s => return ⟨str s, .str⟩
  | .throw => return ⟨.throw, .throw⟩
where
  throw := MonadExcept.throw

end Term

end «λπι»

end TabularTypeInterpreter.Interpreter
