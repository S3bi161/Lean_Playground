import Logic.REPEAT.Semantics
import Logic.DL.Semantics

open Logic.DL

/- -/
inductive RelAtomNext where
  | dyn: DynIndexSym → RelAtomNext
  | next: RelAtomNext
deriving DecidableEq

def executionModelNext (e: Execution) :
  KripkeModel RelAtomNext Cond DynIndex where
    val := (executionModel e).val
    rel := λ a s₁ s₂ ↦
      match a with
        | .dyn i => (executionModel e).rel i s₁ s₂
        | .next => (
            (∃ u i,
              s₁ = u ∘ᵢ ι i ∧
              s₂ = u ∘ᵢ ι (i+1) ∧
              s₂ ∈ e.quasi.cft.Q)
            ∨
            (∃ u i,
              s₁ = u ∘ᵢ ι i ∧
              (u ∘ᵢ ι (i+1) ∉ e.quasi.cft.Q) ∧
              s₂ = u ∘ᵢ $ ∧
              s₂ ∈ e.quasi.cft.Q)
            ∨
            (∃ u i,
              s₁ = u ∘ᵢ ι i ∧
              (u ∘ᵢ ι (i+1) ∉ e.quasi.cft.Q) ∧
              (u ∘ᵢ $ ∉ e.quasi.cft.Q) ∧
              s₂ = u ∘ᵢ # ∧
              s₂ ∈ e.quasi.cft.Q)
            ∨
            (∃ u,
              s₁ = u ∘ᵢ $ ∧
              s₂ = u ∘ᵢ #)
        )
