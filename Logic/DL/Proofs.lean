import Logic.DL.Semantics
import Logic.DL.FinModelSemantics
namespace Logic.DL

open DLForm
open Relation
--set_option trace.Meta.Tactic.simp.rewrite true

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

theorem evalRelB_correct
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (states: List State) (rels: List RelType)
  (α: Relation RelType) (s₀ s₁: State):
    evalRelB M relDecidableH states rels α s₀ s₁ = Bool.true ↔ evalRel M α s₀ s₁ :=
    sorry


/- Correctness proof for evalB under assumptions:
  • evalRelB is correct
  • all states are passed in states: List State
 -/
theorem evalB_correct
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (valDecidableH: ∀ atom s, Decidable (M.val atom s))
  (states: List State) (rels: List RelType)
  (φ: DLForm RelType AtomType)
  (allStatesPassedH: ∀ α s s', evalRel M α s s' → s' ∈ states):
    ∀ s, evalB M relDecidableH valDecidableH states rels φ s = Bool.true ↔ eval M φ s :=
    by
      induction φ with
        | atom => simp[evalB, eval]
        | falsum => simp[evalB, eval]
        | imp φ ψ ihφ ihψ =>  simp[evalB, eval, ihψ]
                              intro s
                              constructor
                              · intro evalBH
                                intro evalφh
                                have hbφ := (ihφ s).mpr evalφh
                                cases evalBH with
                                  | inl hnotbφ =>
                                      have cont: Bool.true = false :=
                                        by rw [hbφ] at hnotbφ; exact hnotbφ
                                      cases cont -- cont has no constructor -> done
                                  | inr hψ => exact hψ
                              · intro evalH
                                cases evalBH: evalB M relDecidableH valDecidableH states rels φ s with
                                  | false => apply Or.inl; rfl
                                  | true => apply Or.inr
                                            have hφ := (ihφ s).mp evalBH
                                            apply evalH hφ

        | diamond α φ ihφ =>  simp[evalB, eval]
                              intro s
                              constructor
                              · intro evalBH
                                --split evalBH
                                cases evalBH with
                                  | intro s' inner =>
                                    cases inner with
                                      | intro sInStates evalBSemH

                                    have evalαH: evalRel M α s s' :=
                                      ((evalRelB_correct M relDecidableH states rels α s s').mp evalBSemH.left)
                                    have evalφH: eval M φ s' :=
                                      ((ihφ s').mp evalBSemH.right)

                                    apply Exists.intro s'
                                    apply And.intro
                                    · exact evalαH
                                    · exact evalφH

                              · intro evalH
                                cases evalH with
                                  | intro s' inner =>
                                    cases inner with
                                      | intro evalαH evalφH
                                    have s'InStatesH: s' ∈ states := allStatesPassedH α s s' evalαH --correctness relies on passing all states to evalB, i.e. that s' ∈ states

                                    have evalαBH: evalRelB M relDecidableH states rels α s s' :=
                                      ((evalRelB_correct M relDecidableH states rels α s s').mpr evalαH)

                                    have evalφBH: evalB M relDecidableH valDecidableH states rels φ s' :=
                                      (ihφ s').mpr evalφH

                                    apply Exists.intro s'
                                    apply And.intro
                                    · exact s'InStatesH
                                    · apply And.intro evalαBH evalφBH

end Logic.DL
