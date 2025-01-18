import TabularTypeInterpreter.«F⊗⊕ω».Syntax.Kind
import TabularTypeInterpreter.Syntax.Kind

namespace TabularTypeInterpreter

open «F⊗⊕ω»

judgement_syntax "⊢ " κ " ⇝ " K : Kind.Elaboration

judgement Kind.Elaboration :=

─────── star
⊢ * ⇝ *

⊢ κ₀ ⇝ K₀
⊢ κ₁ ⇝ K₁
─────────────────── arr
⊢ κ₀ ↦ κ₁ ⇝ K₀ ↦ K₁

─────── label
⊢ L ⇝ *

─────── comm
⊢ U ⇝ *

⊢ κ ⇝ K
─────────── row
⊢ R κ ⇝ L K

─────── constr
⊢ C ⇝ *

end TabularTypeInterpreter
