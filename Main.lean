import Logic.DL.Syntax
import Logic.DL.Semantics
import Logic.DL.Notation
import Logic.DL.FinModelSemantics
import Logic.REPEAT.Semantics


def main : IO Unit := pure ()

namespace GenericKripke
open Logic.DL
/- # Generic Dynamic Logic Example-/

--atomic formulas
inductive Atom
  | p
  | q
deriving DecidableEq

--atomic relations
inductive RelAtom
  | a
  | b
deriving DecidableEq


--states
inductive State
  | s₀
  | s₁
  | s₂
deriving DecidableEq

def M : Logic.DL.KripkeModel RelAtom Atom State where
  val
    | .p, .s₀      => True    -- in s₀, p holds
    | .q, .s₁      => True    -- in s₁, q holds
    | .p, .s₂      => True    -- in s₂, p holds
    | _, _         => False   -- no atomic proposition holds in another state
  rel
    | .a, .s₀, .s₁ => True    -- s₀ --a--> s₁
    | .b, .s₁, .s₂ => True    -- s₁ --b--> s₂
    | _, _, _      => False   -- no other transitions

-- φ := ⟨a⟩q
def φ : DLForm RelAtom Atom :=
  DLForm.diamond (Relation.relAtom RelAtom.a) (DLForm.atom Atom.q)

-- ψ := ⟨a ∪ b⟩¬p ∨ ¬q
def ψ : DLForm RelAtom Atom :=
  DLForm.diamond (Relation.comp (Relation.relAtom RelAtom.a) (Relation.relAtom RelAtom.b))
    (disj (not (DLForm.atom Atom.p)) (not (DLForm.atom Atom.q)))

-- M, s₀ ⊧ φ
example : eval M φ State.s₀ := by
  simp[M, φ, eval, evalRel]
  use State.s₁

-- M, s₀ ⊧ ψ
example : eval M ψ State.s₀ := by
  simp[M, ψ, eval, evalRel]
  use State.s₂
  constructor
  · use State.s₁
  · intro hp
    intro hq
    aesop

-- two arbitrary atomic steps lead to s₂
example : evalRel M (Relation.comp (Relation.wild) (Relation.wild)) State.s₀ State.s₂ := by
  simp[evalRel, M]
  use State.s₁
  constructor
  · use RelAtom.a
  · use RelAtom.b

end GenericKripke


namespace Logic.DL

/- # Execution Model -/
def testQ := [ε, ε ∘ᵢ ι 0, (ε ∘ᵢ ι 0) ∘ᵢ #]
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
  liberal := {
    cft := testCFT,
    seed := testSeed
  },
  val := testVal,
  hCFT := by sorry,
  hVal := by sorry,
  hExec := by sorry
}

def M := executionModel testExec

example : M.rel (0) ε (ε ∘ᵢ ι 0) := by
  simp[M, executionModel]
  constructor
  · constructor
  · right
    left

example : Logic.DL.evalRel M
                 (0 ∘ₗ #)
                  ε
                  ((ε ∘ᵢ ι 0) ∘ᵢ #) := by
  simp[Logic.DL.evalRel]
  use  (ε ∘ᵢ (ι 0))
  simp[M, executionModel]
  constructor
  · constructor
    · constructor
    · right
      left
  · constructor
    · right
      left
    · right
      right
      constructor

def φ : DAForm := ⟨0 ∪ 1*⟩ₗ "e" =ₑ "e"

example : Logic.DL.eval M φ ε := by
  simp[Logic.DL.eval, φ, M]
  use (ε ∘ᵢ ι 0)
  simp[Logic.DL.evalRel]
  simp[executionModel]
  constructor
  · constructor
    constructor
    · left
    · right
      left
  · constructor
    · right
      left
    · unfold evalCond
      rfl

end Logic.DL
