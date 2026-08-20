import Logic.REPEAT.Semantics

namespace Logic.DL

theorem rel_iff
  (e: Execution)
  (s s': DynIndex):

  (executionModel e).rel (DL.DynIndexSym.line i) s s' ↔
  s ∈ e.liberal.cft.Q ∧
  s' = s ∘ᵢ i ∧
  s' ∈ e.liberal.cft.Q := by

    simp[executionModel]
    intro hSInQ
    constructor
    · intro h
      constructor
      · exact h.right
      · exact h.left
    · intro h
      constructor
      · exact h.right
      · exact h.left

/- The kripke model execution model induced by an execution e is always non-branching-/
theorem rel_non_branching_line
  (e: Execution)
  (s t₁ t₂: DynIndex)
  (h₁: (executionModel e).rel (DL.DynIndexSym.line i) s t₁)
  (h₂: (executionModel e).rel (DL.DynIndexSym.line i) s t₂):

  t₁ = t₂ := by

    simp[executionModel] at *
    rw[h₁.right.right]
    rw[h₂.right.right]

theorem rel_non_branching_dollar
  (e: Execution)
  (s t₁ t₂: DynIndex)
  (h₁: (executionModel e).rel $ s t₁)
  (h₂: (executionModel e).rel $ s t₂):

  t₁ = t₂ := by

    simp[executionModel] at *
    rw[h₁.right.right]
    rw[h₂.right.right]

theorem rel_non_branching_hash
  (e: Execution)
  (s t₁ t₂: DynIndex)
  (h₁: (executionModel e).rel # s t₁)
  (h₂: (executionModel e).rel # s t₂):

  t₁ = t₂ := by

    simp[executionModel] at *
    rw[h₁.right.right]
    rw[h₂.right.right]



theorem model_non_branching
  (e: Execution):
  DL.nonBranching (executionModel e) := by
    simp[DL.nonBranching]
    intro relAtom
    intro s t₁ t₂
    intro h₁
    intro h₂
    cases relAtom with
    | line i => exact rel_non_branching_line e s t₁ t₂ h₁ h₂
    | dollar => exact rel_non_branching_dollar e s t₁ t₂ h₁ h₂
    | hash => exact rel_non_branching_hash e s t₁ t₂ h₁ h₂


end Logic.DL
