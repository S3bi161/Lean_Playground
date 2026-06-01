import Logic.REPEAT.Semantics

namespace Logic.REPEAT

theorem root_in_Q (cft: CFTrace):
  ε ∈ cft.Q := by
    exact InQ.root

theorem repeat_entry_in_Q (cft: CFTrace) (s: DynIndex) (i: Nat):
  DynIndex.line s i ∈ cft.Q →
  stmt cft (DynIndex.line s i) = some (Stmt.repeat) →
  InQ cft (DynIndex.line (s $) 0) := by
    intro hsInQ hrep
    --intro hrep

    exact InQ.repeat_entry s i hsInQ hrep

theorem valid_tar_implies_valid_cft (cft: CFTrace):
  wellFormedTar cft → validCFTrace cft := by
    intro hwellFormedTar
    simp [wellFormedTar, validCFTrace] at *
    constructor
    · exact InQ.root
    · intro s e args
      constructor
      intro hsInQ
      intro hStmt
      sorry
      sorry



--TODO: IH is too weak
theorem no_hash_line (cft: CFTrace):
  ∀ t, InQ cft t →
  (∀ s i, t ≠ DynIndex.line (s #) i) ∧ -- no line comes after #
  (∀ s, t ≠ (s #) $) ∧                 -- no dollar comes after #
  (∀ s, t ≠ (s #) #) := by             -- no hash after hash
    intro t h
    --intro h
    induction h with
    | root => simp
    | call s expr args hs hstmt ih =>
                                      constructor
                                      · intro s' i heq
                                        cases heq
                                        simp[stmt] at *

                                      · constructor
                                        · intro s heq
                                          cases heq
                                        · intro s heq
                                          cases heq
    | assign s i v e₀ e₁ hsi hassign ih =>
                                      simp at *
                                      exact ih
    | return_next s i e hsi hreturn ih =>
                                      simp at *
                                      exact ih
    | return_exit s i e hsi hreturn ih =>
                                      simp at *
                                      exact ih
    | repeat_iter s i hsi hrepeat ih =>
                                      simp at *
                                      exact ih
    | repeat_entry s i hsi hrepeat ih =>
                                      simp at *
    | repeat_return s hs ih => sorry

    | call_return s i hsi ih => sorry

end Logic.REPEAT
