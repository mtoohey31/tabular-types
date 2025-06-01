import Lott.Data.List

namespace TabularTypeInterpreter.Interpreter.«λπι»

inductive Op where
  | add
  | sub
  | mul
  | div
deriving BEq

instance : ToString Op where
  toString
    | .add => "+"
    | .sub => "-"
    | .mul => "*"
    | .div => "/"

inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | prodIntro : List Term → Term
  | prodElim : Nat → Term → Term
  | sumIntro : Nat → Term → Term
  | sumElim : Term → List Term → Term
  | nil
  | cons : Term → Term → Term
  | fold
  | nat : Nat → Term
  | op : Op → Term → Term → Term
  | range
  | str : String → Term

namespace Term

instance : Inhabited Term where
  default := prodIntro []

def id := lam <| .var 0

def shift (E : Term) (off := 1) (min := 0) : Term := match E with
  | var n => var <| if min ≤ n then n + off else n
  | lam E' => lam <| shift E' off (min + 1)
  | app E' F => app (shift E' off min) (shift F off min)
  | prodIntro E's => prodIntro <| E's.mapMem fun E' _ => shift E' off min
  | prodElim n E' => prodElim n <| shift E' off min
  | sumIntro n E' => sumIntro n <| shift E' off min
  | sumElim E' Fs => sumElim (shift E' off min) <| Fs.mapMem fun F _ => shift F off min
  | nil => nil
  | cons E' F => cons (shift E' off min) (shift F off min)
  | fold => fold
  | nat n => nat n
  | op o E' F => op o (shift E' off min) (shift F off min)
  | range => range
  | str s => str s

end Term

inductive Value.Is : Term → Prop where
  | lam : Is (.lam E)
  | prodIntro : (∀ E ∈ Es, Is E) → Is (.prodIntro Es)
  | sumIntro : Is E → Is (.sumIntro i E)
  | nil : Is .nil
  | cons : Is E → Is F → Is (.cons E F)
  | fold₀ : Is .fold
  | fold₁ : Is E → Is (.app .fold E)
  | fold₂ : Is E → Is F → Is (.app (.app .fold E) F)
  | nat : Is (.nat n)
  | range : Is .range
  | str : Is (.str s)

def Value.Is.decide : Decidable (Is E) := match E with
  | .var _ => isFalse nofun
  | .lam _ => isTrue .lam
  | .app E' F => match E' with
    | .var _ => isFalse nofun
    | .lam _ => isFalse nofun
    | .app E'' F' => match E'' with
      | .var _ => isFalse nofun
      | .lam _ => isFalse nofun
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
      | .nat _ => isFalse nofun
      | .op .. => isFalse nofun
      | .range => isFalse nofun
      | .str _ => isFalse nofun
    | .prodIntro _ => isFalse nofun
    | .prodElim .. => isFalse nofun
    | .sumIntro .. => isFalse nofun
    | .sumElim .. => isFalse nofun
    | .nil => isFalse nofun
    | .cons .. => isFalse nofun
    | .fold => match decide (E := F) with
      | isFalse h => isFalse fun | .fold₁ h' => h h'
      | isTrue h => isTrue <| .fold₁ h
    | .nat _ => isFalse nofun
    | .op .. => isFalse nofun
    | .range => isFalse nofun
    | .str _ => isFalse nofun
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
  | .nat _ => isTrue .nat
  | .op .. => isFalse nofun
  | .range => isTrue .range
  | .str _ => isTrue .str

instance : Decidable (Value.Is E) := Value.Is.decide

abbrev Value := { E : Term // Value.Is E }

instance : Inhabited Value where
  default := ⟨default, .prodIntro nofun⟩

theorem Value.Is.shift_preservation {min} (EIs : Is E) : Is (E.shift off min) := by
  induction EIs with
  | lam =>
    rw [Term.shift]
    exact lam
  | prodIntro _ ih =>
    rw [Term.shift, List.mapMem_eq_map]
    apply prodIntro
    intro _ mem
    rcases List.mem_map.mp mem with ⟨_, mem', rfl⟩
    exact ih _ mem'
  | sumIntro _ ih =>
    rw [Term.shift]
    exact sumIntro ih
  | nil =>
    rw [Term.shift]
    exact nil
  | cons _ _ E'ih Fih =>
    rw [Term.shift]
    exact cons E'ih Fih
  | fold₀ =>
    rw [Term.shift]
    exact fold₀
  | fold₁ _ ih =>
    rw [Term.shift, Term.shift]
    exact fold₁ ih
  | fold₂ _ _ E'ih Fih =>
    rw [Term.shift, Term.shift, Term.shift]
    exact fold₂ E'ih Fih
  | nat =>
    rw [Term.shift]
    exact nat
  | range =>
    rw [Term.shift]
    exact range
  | str =>
    rw [Term.shift]
    exact str

namespace Term

def «open» (E : Term) (V : Value) (n : Nat := 0) : Term := match E with
  | var m => if m == n then V else var m
  | lam E' => lam <| E'.open ⟨V.val.shift, V.property.shift_preservation⟩ (n + 1)
  | app E' F => app (E'.open V n) (F.open V n)
  | prodIntro Es => prodIntro <| Es.mapMem fun E' _ => E'.open V n
  | prodElim n E' => prodElim n <| E'.open V n
  | sumIntro n E' => sumIntro n <| E'.open V n
  | sumElim E' Fs => sumElim (E'.open V n) <| Fs.mapMem fun F _ => F.open V n
  | nil => nil
  | cons E' F => cons (E'.open V n) (F.open V n)
  | fold => fold
  | nat n => nat n
  | op o E' F => op o (E'.open V n) (F.open V n)
  | range => range
  | str s => str s

inductive eval.Error where
  | freeVar (n : Nat)
  | nonLamApp
  | nonProdIntroProdElim
  | invalidProdIdx (n l : Nat)
  | nonSumIntroSumElim
  | invalidSumIdx (n l : Nat)
  | nonLamSumElim
  | nonNatOperand
  | nonListFold
  | nonNatRange

instance : ToString eval.Error where
  toString
    | .freeVar n => s!"encountered free variable: {n}"
    | .nonLamApp => "application of non-lambda term"
    | .nonProdIntroProdElim => "prod elimination of non-prod intro term"
    | .invalidProdIdx n l =>
      s!"prod elimination index {n} is out of range for prod with {l} entries"
    | .nonSumIntroSumElim => "sum elimination of non-sum intro term"
    | .invalidSumIdx n l =>
      s!"sum intro index {n} is out of range for sum elim with {l} entries"
    | .nonLamSumElim => "sum elim contained non-lambda term"
    | .nonNatOperand => "non-nat term used as operand"
    | .nonListFold => "non-list term used as third argument for fold"
    | .nonNatRange => "non-nat term used as first argument for range"

partial
def eval (E : Term) : Except eval.Error Value := do match E with
  | var n => throw <| .freeVar n
  | lam E => return ⟨lam E, .lam⟩
  | app E F =>
    let VE ← eval E
    let V ← eval F
    match VE with
    | ⟨lam E', _⟩ => eval <| E'.open V
    | ⟨fold, _⟩ => return ⟨app fold V, .fold₁ V.property⟩
    | ⟨app fold F', appfoldIs⟩ =>
      let F'Is := match appfoldIs with | .fold₁ h => h
      return ⟨app (app fold F') V, .fold₂ F'Is V.property⟩
    | ⟨app (app fold F') Eᵢ, appappfoldIs⟩ => match V with
      | ⟨.nil, _⟩ => return ⟨Eᵢ, match appappfoldIs with | .fold₂ _ h => h⟩
      | ⟨.cons Eₙ V', _⟩ => eval <| fold.app F' |>.app (F'.app Eᵢ |>.app Eₙ) |>.app V'
      | _ => throw .nonListFold
    | ⟨range, _⟩ =>
      let ⟨nat n, _⟩ := V | throw .nonNatRange
      return n.fold (init := (⟨nil, .nil⟩ : Value)) fun i _ V =>
        ⟨cons (.nat i) V, .cons .nat V.property⟩
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
    let ⟨lam F', _⟩ := VF | throw .nonLamSumElim
    eval <| F'.open ⟨VE, VEIs⟩
  | nil => return ⟨nil, .nil⟩
  | cons E F =>
    let VE ← eval E
    let VF ← eval F
    return ⟨cons VE VF, .cons VE.property VF.property⟩
  | fold => return ⟨fold, .fold₀⟩
  | nat n => return ⟨nat n, .nat⟩
  | op o E F =>
    let ⟨nat En, _⟩ ← eval E | throw .nonNatOperand
    let ⟨nat Fn, _⟩ ← eval F | throw .nonNatOperand
    let f := match o with
      | .add => Nat.add
      | .sub => Nat.sub
      | .mul => Nat.mul
      | .div => Nat.div
    return ⟨nat (f En Fn), .nat⟩
  | range => return ⟨range, .range⟩
  | str s => return ⟨str s, .str⟩

end Term

namespace TabularTypeInterpreter.Interpreter.«λπι»
