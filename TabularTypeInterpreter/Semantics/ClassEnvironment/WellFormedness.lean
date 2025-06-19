import TabularTypeInterpreter.Semantics.Type.KindingAndElaboration

namespace TabularTypeInterpreter

judgement_syntax "⊢c " Γc : ClassEnvironment.WellFormedness

judgement ClassEnvironment.WellFormedness where

──── empty
⊢c ε

⊢c Γc
TC ∉ dom(Γc)
m ∉ dom(Γc)
⊢ κ ⇝ K
∀ a, Γc; ε, a : κ ⊢ σ^a : * ⇝ A^a
∀ a, ε, a : K ⊢ A^a : *
</ ∀ a, Γc; ε, a : κ ⊢ TC'@i a : C ⇝ A'@i^a // i in [:n] notex />
</ ∀ a, ε, a : K ⊢ A'@i^a : * // i in [:n] notex />
─────────────────────────────────────────────────────────────────────── ext {TC}
⊢c Γc, (</ TC'@i a ⇝ A'@i // i in [:n] notex /> ⇒ TC a : κ) ↦ m : σ ⇝ A

end TabularTypeInterpreter
