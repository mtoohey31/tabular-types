import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Value

namespace TabularTypeInterpreter.«F⊗⊕ω»

inductive Term.EvalError where
  | free (x : TermVar)
  | nonLamApp
  | nonTypeLamTypeApp
  | nonProdIntroProdElim
  | invalidProdIdx (n l : Nat)
  | nonSumIntroSumElim
  | nonLamSumElim

local instance instInhabitedValue' : Inhabited Value where
  default := ⟨.prodIntro [], .prodIntro nofun⟩
in
partial
def Term.eval (E : Term) : Except EvalError Value := do match E with
  | var x => throw <| .free x
  | lam A E => return ⟨lam A E, .lam⟩
  | app E F =>
    let ⟨lam _ E', _⟩ ← eval E | throw <| .nonLamApp
    let F' ← eval F
    eval <| E'.Term_open F
  | typeLam K E => return ⟨typeLam K E, .typeLam⟩
  | typeApp E A =>
    let ⟨typeLam _ E', _⟩ ← eval E | throw <| .nonLamApp
    eval <| E'.Type_open A
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
    return ⟨sumIntro n V.val, .sumIntro V.property⟩
  | sumElim E Fs =>
    let ⟨sumIntro n VE, VEIsValue⟩ ← eval E | throw .nonSumIntroSumElim
    let VFs ← Fs.mapM eval
    let some ⟨lam _ F', _⟩ := VFs.get? n | throw .nonLamSumElim
    eval <| F'.Term_open VE

end TabularTypeInterpreter.«F⊗⊕ω»
