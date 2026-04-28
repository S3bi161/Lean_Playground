import Logic.DL.Semantics

namespace Logic.DL

open DLForm
open Relation
set_option trace.Meta.Tactic.simp.rewrite true

--formulas are equivalent to themselves
theorem equiv_refl{RelType AtomType State: Type} (φ: DLForm RelType AtomType):
  @equiv RelType AtomType State φ φ :=
  by
    simp[equiv]

--and evaluates correct wrt to ∧
theorem and_correct{RelType AtomType State: Type} (φ ψ: DLForm RelType AtomType):
  ∀ (M: KripkeModel RelType AtomType State) s, eval M (conj φ ψ) s ↔ (eval M φ s) ∧ (eval M ψ s) :=
  by
    intro M s
    simp[conj, not, eval]

-- anything follows from ⊥
theorem ex_falso (M: KripkeModel RelType AtomType State) (φ: DLForm RelType AtomType):
  eval M falsum s → eval M φ s  :=
  by
    intro h
    simp[eval] at h


-- transition s -> s' with some a implies transition s -> s' with wildcard
theorem ato_imp_wild (M: KripkeModel RelType AtomType State) (a: RelType) (s s': State) :
  evalRel M (Relation.relAtom a) s s' → evalRel M Relation.wild s s' :=
  by
  intro h
  simp[evalRel] at h
  simp[evalRel]
  exact ⟨a, h⟩

-- transition s -> s' with wildcard implies there exist atomic rel with s -> s'
theorem wild_imp_ato (M: KripkeModel RelType AtomType State):
  evalRel M Relation.wild s s' → ∃a, evalRel M (Relation.relAtom a) s s' :=
  by
  intro h
  simp[evalRel] at *
  exact h

end Logic.DL
