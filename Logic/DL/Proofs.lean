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

theorem relBFS_correct
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (states: List State) (rels: List RelType)
  (α: Relation RelType)
  (hα: ∀ s s', evalRelB M relDecidableH states rels α s s' = Bool.true ↔
        evalRel M α s s')
  (allStatesPassedH: ∀ s: State, s ∈ states)
  (s₀ s₁: State) :
    relBFS M relDecidableH states rels α states.length [s₀] [s₀] s₁ = Bool.true ↔
      Relation.ReflTransGen (evalRel M α) s₀ s₁ := by
        sorry

theorem evalRelB_correct
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (states: List State) (rels: List RelType)
  (allStatesPassedH: ∀ s: State, s ∈ states)
  (allRelsPassedH: ∀ {a s s'}, M.rel a s s' → a ∈ rels)
  (α: Relation RelType) (s₀ s₁: State):
    evalRelB M relDecidableH states rels α s₀ s₁ = Bool.true ↔ evalRel M α s₀ s₁ := by
      induction α generalizing s₀ s₁ with
      | relAtom a           =>  simp[evalRelB, evalRel]
      | emptyset            =>  simp[evalRelB, evalRel]
      | wild                =>  simp[evalRelB, evalRel]
                                constructor
                                · rintro ⟨x, h⟩
                                  exists x
                                  exact h.2
                                · rintro ⟨x, h⟩
                                  exists x
                                  exact And.intro (@allRelsPassedH x s₀ s₁ h) (h)
      | alt α β ihα ihβ     =>  simp_all[evalRel, evalRelB]
      | comp α β ihα ihβ    =>  simp_all[evalRel, evalRelB]
      | iter α ihα          =>  simp_all[evalRel, evalRelB]
                                exact relBFS_correct M relDecidableH states rels α ihα allStatesPassedH s₀ s₁




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
  (allStatesPassedH: ∀ s: State, s ∈ states)
  (allRelsPassedH: ∀ {a s s'}, M.rel a s s' → a ∈ rels):
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
                                      ((evalRelB_correct M relDecidableH states rels allStatesPassedH allRelsPassedH α s s').mp evalBSemH.left)
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
                                    have s'InStatesH: s' ∈ states := allStatesPassedH s' --correctness relies on passing all states to evalB, i.e. that s' ∈ states

                                    have evalαBH: evalRelB M relDecidableH states rels α s s' :=
                                      ((evalRelB_correct M relDecidableH states rels allStatesPassedH allRelsPassedH α s s').mpr evalαH)

                                    have evalφBH: evalB M relDecidableH valDecidableH states rels φ s' :=
                                      (ihφ s').mpr evalφH

                                    apply Exists.intro s'
                                    apply And.intro
                                    · exact s'InStatesH
                                    · apply And.intro evalαBH evalφBH

end Logic.DL
