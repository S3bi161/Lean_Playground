import Logic.REPEAT.Semantics
import Logic.DL.Semantics

/- # Temporal Extension of DA
This file introduces the temporal successor using the order on execution states, specifically `nextState`.

The idea is to model basic LTL that way:
  • `X φ = ⟨next⟩ φ`
  • `F φ = ⟨next*⟩ φ`
  • `G φ = [next*] φ`
-/
namespace Logic.Temporal
open Logic.DL

/-New datatype for atomic relations, extending dynamic Index Symbols with next-/
inductive RelAtomTemporal where
  | dyn: DynIndexSym → RelAtomTemporal
  | next: RelAtomTemporal
deriving DecidableEq

/- The evaluation for the temporal extension keeps the default evaluation of an evaluation symbol.
It is extended to evaluate `next` using `nextState`-/
def executionModelNext (e: Execution) :
  KripkeModel RelAtomTemporal Cond DynIndex where
    val := (executionModel e).val
    rel := λ a s₁ s₂ ↦
      match a with
        | .dyn i => (executionModel e).rel i s₁ s₂
        | .next => nextState e.quasi.cft s₁ s₂

-- `X φ = ⟨next⟩ φ`
def X (φ: DLForm RelAtomTemporal Cond): DLForm RelAtomTemporal Cond :=
  DLForm.diamond (Relation.relAtom RelAtomTemporal.next) φ

-- `F φ = ⟨next*⟩ φ`
def F (φ: DLForm RelAtomTemporal Cond): DLForm RelAtomTemporal Cond :=
  DLForm.diamond (Relation.iter (Relation.relAtom RelAtomTemporal.next)) φ

-- `G φ = [next*] φ`
def G (φ: DLForm RelAtomTemporal Cond): DLForm RelAtomTemporal Cond :=
  box (Relation.iter (Relation.relAtom RelAtomTemporal.next)) φ

end Logic.Temporal
