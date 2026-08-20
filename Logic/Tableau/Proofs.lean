import Logic.Tableau.Tableau
import Logic.REPEAT.Semantics

open Logic.DL


def SatisfiesBranch (E: LiberalExecution) (branch: Branch) : Prop :=
  sorry


-- given a branch is satisfied by E, then at least one rule generated branch is satisfied
def RuleSound (r: Rule) : Prop :=
  ∀ E sel branches,
    SatisfiesBranch E sel.branch ∧
    r sel = some branches →
      ∃ b ∈ branches, SatisfiesBranch E b
