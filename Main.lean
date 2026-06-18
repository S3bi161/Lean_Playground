import Logic.Prop.Syntax
import Logic.Prop.Semantics
import Logic.DL.Syntax
import Logic.DL.Semantics
--import Logic.DL.Notation
import Logic.DL.FinModelSemantics
import Logic.REPEAT.Semantics


def main : IO Unit := pure ()

open Logic.REPEAT

def testQ : Set DynIndex := {ε, DynIndex.line ε 0, (DynIndex.line ε 0) #}
def dummyProc : Proc := {
  id := 0,
  params := [],
  body := []
}
def testCFT : CFTrace := {
  Q := testQ,
  prompt := Stmt.call (Expr.const 0) [],
  tar := λ _ ↦ some dummyProc
}

def testSeed : DynIndex → Var → Int → Int :=
  λ _ _ _ ↦ 0

def testVal : DynIndex → Var → Int → Int :=
  λ _ _ _ ↦ 0

def testExec : Execution := {
  quasi := {
    cft := testCFT,
    seed := testSeed
  },
  val := testVal,
  hCFT := by sorry,
  hVal := by sorry,
  hExec := by sorry
}

def M := executionModel testExec
#check Logic.DL.DynIdxSym.line
#check M.rel
example : M.rel (Logic.DL.DynIdxSym.line 0) ε (DynIndex.line ε 0) := by
  simp[M, executionModel]
  constructor
  · constructor
    rfl
  · right
    left
    rfl

#check (Logic.DL.evalRel M)

#check (Logic.DL.evalRel M (Logic.DL.Relation.relAtom (Logic.DL.DynIdxSym.line 0)))

#check (Logic.DL.evalRel M (Logic.DL.Relation.relAtom (Logic.DL.DynIdxSym.line 0)) DynIndex.root)

example : Logic.DL.evalRel M
                 (Logic.DL.Relation.comp
                    (Logic.DL.Relation.relAtom (Logic.DL.DynIdxSym.line 0))
                    (Logic.DL.Relation.relAtom Logic.DL.DynIdxSym.hash))
                  DynIndex.root
                  ((DynIndex.line DynIndex.root 0) # ) := by
  simp[Logic.DL.evalRel]
  use (DynIndex.line ε 0)
  simp[M, executionModel]
  constructor
  · constructor
    · constructor
      rfl
    · right
      left
      rfl
  · constructor
    · right
      left
      rfl
    · right
      right
      constructor
