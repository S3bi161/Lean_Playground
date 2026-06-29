import Logic.REPEAT.Semantics

namespace Logic.DL

-- s i+1 ∈ Q → s i ∈ Q in a valid cft
theorem line_predecessor
  (cft: CFTrace)
  (hcftValid: validCFTrace cft)
  (hline: (line s (i+1)) ∈ cft.Q) :
  ((line s i) ∈ cft.Q) := by

    have hNoJunkLines := by
      unfold validCFTrace at hcftValid
      unfold cftNoJunk at hcftValid
      unfold noJunkLines at hcftValid
      exact hcftValid.right.right.left s i hline

    cases hNoJunkLines with
    | inl hAssign =>
        cases hAssign with
        | intro v hAssign' =>
          cases hAssign' with
          | intro e₁ hAssign'' =>
            cases hAssign'' with
            | intro e₂ h => exact h.left
    | inr hReturn =>
        cases hReturn with
        | intro e hReturn' => exact hReturn'.left

-- s i+1 ∈ Q → stmt (s i) is assignment or returnIf
theorem line_successor_origin
  (cft: CFTrace)
  (hcftValid: validCFTrace cft)
  (hline: (line s (i+1) ) ∈ cft.Q):
  (∃ v e₀ e₁, stmt cft (line s i) = some (Stmt.assign v e₀ e₁)) ∨
  (∃ e, stmt cft (line s i) = some (Stmt.returnIf e)) := by

  have hNoJunkLines := by
    unfold validCFTrace at hcftValid
    unfold cftNoJunk at hcftValid
    unfold noJunkLines at hcftValid
    exact hcftValid.right.right.left s i hline

  cases hNoJunkLines with
  | inl hAssign =>
    cases hAssign with
    | intro v hAssign' =>
      cases hAssign' with
      | intro e₀ hAssign'' =>
        cases hAssign'' with
        | intro e₁ h => left
                        use v, e₀, e₁
                        exact h.right
  | inr hReturn =>
    cases hReturn with
    | intro e hReturn' => right
                          use e
                          exact hReturn'.right


theorem call_tar_exists
  (cft: CFTrace)
  (hcftValid: validCFTrace cft)
  (hcall: stmt cft s = some (Stmt.call expr args)):
  ∃ proc, cft.tar s = some proc := by sorry


--after an assign, exactly one array cell is changed
theorem assign_changes_exactly_one_cell
  (qe: QuasiExecution)
  (hVal: validValuation val qe)
  (hStmt: stmt qe.cft (line s i) = some (Stmt.assign v e₀ e₁)):

  val (line s (i+1)) v k =
  if evalExpr qe.cft val (line s i) e₀ = k then
    evalExpr qe.cft val (line s i) e₁
  else
    val (line s i) v k := by

    by_cases hk: evalExpr qe.cft val (line s i) e₀ = k
    · have hAssignHit := by
        unfold validValuation at hVal
        unfold valAssignHit at hVal
        exact hVal.right.right.right.left s i v k e₀ e₁

      have hHit := hAssignHit ⟨hStmt, hk⟩
      simp[hk]
      exact hHit
    · have hAssignMiss := by
        unfold validValuation at hVal
        unfold valAssignMiss at hVal
        exact hVal.right.right.right.right.left s i v e₀ e₁ k
      have hMiss := hAssignMiss ⟨hStmt, hk⟩
      simp[hk]
      exact hMiss

theorem rel_iff
  (e: Execution)
  (s s': DynIndex):

  (executionModel e).rel (DL.DynIdxSym.line i) s s' ↔
  s ∈ e.quasi.cft.Q ∧
  s' = line s i ∧
  s' ∈ e.quasi.cft.Q := by

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
  (h₁: (executionModel e).rel (DL.DynIdxSym.line i) s t₁)
  (h₂: (executionModel e).rel (DL.DynIdxSym.line i) s t₂):

  t₁ = t₂ := by

    simp[executionModel] at *
    rw[h₁.right.right]
    rw[h₂.right.right]

theorem rel_non_branching_dollar
  (e: Execution)
  (s t₁ t₂: DynIndex)
  (h₁: (executionModel e).rel (DL.DynIdxSym.dollar) s t₁)
  (h₂: (executionModel e).rel (DL.DynIdxSym.dollar) s t₂):

  t₁ = t₂ := by

    simp[executionModel] at *
    rw[h₁.right.right]
    rw[h₂.right.right]

theorem rel_non_branching_hash
  (e: Execution)
  (s t₁ t₂: DynIndex)
  (h₁: (executionModel e).rel (DL.DynIdxSym.hash) s t₁)
  (h₂: (executionModel e).rel (DL.DynIdxSym.hash) s t₂):

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
