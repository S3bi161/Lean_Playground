import Logic.DL.Semantics

namespace Logic.DL

open DLForm
open Relation
set_option trace.Meta.Tactic.simp.rewrite true

--formulas are equivalent to themselves
theorem equiv_refl (φ: DLForm):
  equiv φ φ :=
  by
    simp[equiv]

--and evaluates correct wrt to ∧
theorem and_correct (φ ψ: DLForm):
  ∀ M s, eval M (conj φ ψ) s ↔ (eval M φ s) ∧ (eval M ψ s) :=
  by
    intro M s
    simp[conj, not, eval]
-- anything follows from ⊥
theorem ex_falso (φ: DLForm):
  eval M falsum n → eval M φ n :=
  by
    intro h
    simp[eval] at h


-- transition s -> s' with some a implies transition s -> s' with wildcard
theorem ato_imp_wild (M: KripkeModel) (a s s': Nat) :
  evalRel M (Relation.relAtom a) s s' → evalRel M Relation.wild s s' :=
  by
  intro h
  simp[evalRel] at h
  simp[evalRel]
  exact ⟨a, h⟩

-- transition s -> s' with wildcard implies there exist atomic rel with s -> s'
theorem wild_imp_ato (M: KripkeModel):
  evalRel M Relation.wild s s' → ∃a, evalRel M (Relation.relAtom a) s s' :=
  by
  intro h
  simp[evalRel] at *
  exact h

end Logic.DL
