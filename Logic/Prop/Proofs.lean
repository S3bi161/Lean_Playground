import Logic.Prop.Nnf

namespace Logic.Prop

open PropositionalForm
set_option trace.Meta.Tactic.simp.rewrite true --show verbose infoview


--some simple proofs

-- prove deMorgans law
theorem DeMorgan (φ ψ: PropositionalForm):
  equiv (myNot (myAnd φ ψ))  (myOr (myNot φ) (myNot ψ)) :=
  by
    intro v --"take an arbitrary valuation v"
    simp[eval, myOr] --"simplify by using definitions of eval, myOr"


-- prove ¬¬φ ≃ φ
theorem DoubleNeg (φ: PropositionalForm):
  equiv (myNot (myNot φ)) φ :=
  by
    intro v
    calc
      eval v (myNot (myNot φ))
        = ! (eval v (myNot φ)) := by rfl
      _ = !(!(eval v  φ)) := by rfl
      _ = eval v φ := by rewrite[Bool.not_not]; rfl


--prove φ → ψ ≃ ¬φ ∨ ψ
theorem Imp (φ ψ: PropositionalForm):
  equiv (imp φ ψ)  (myOr (myNot φ) ψ) :=
  by
    intro v
    rfl


--prove φ ∧ ψ ≃ ψ ∧ φ
theorem AndComm (φ ψ: PropositionalForm):
  equiv (myAnd φ ψ) (myAnd ψ φ) :=
  by
    intro v
    simp[eval, Bool.and_comm]

--a little more verbose
theorem AndComm' (φ ψ: PropositionalForm):
  equiv (myAnd φ ψ) (myAnd ψ φ) :=
  by
    intro v
    unfold eval
    rw[Bool.and_comm]

--prove φ ≃ ψ => ¬φ ≃ ψ
theorem NotCongr (φ ψ: PropositionalForm):
  equiv φ ψ -> equiv (myNot φ) (myNot ψ) :=
  by
    intro h v
    simp[eval, h v]

--prove equivalence is transitive
theorem EquivTrans (φ ψ ρ: PropositionalForm):
  equiv φ ψ -> equiv ψ ρ -> equiv φ ρ :=
  by
    intro h₁ h₂ v
    simp[h₁ v, h₂ v]



--prove that the nnf of φ is equivalent to φ
theorem NNFEquiv (φ: PropositionalForm):
  equiv (nnf φ) φ ∧ equiv (nnf (myNot φ)) (myNot φ) := --including the negated version to obtain a suitable hypothesis ih.2 for myNot case
  by
    induction φ with
    | var x =>
      constructor -- apply And.intro (constructor) to split conjunction target
      case left => intro v; rw[nnf] -- equiv (nnf φ) φ
      case right => intro v; rw[nnf] -- equiv (nnf (myNot φ)) (myNot φ)
    | myFalse =>
      constructor
      case left => intro v; rw[nnf]
      case right => intro v; simp[nnf, eval, myTrue]
    | myAnd ψ₁ ψ₂ ih₁ ih₂ => --e.g. ih₁ is induction hypothesis for ψ₁
      constructor
      case left => intro v; simp[nnf, eval, ih₁.1 v, ih₂.1 v]
      case right => intro v; simp[nnf, eval, ih₁.2 v, ih₂.2 v, myOr] --nnf of negation  transformed into myOr
    | myNot ψ ih =>
      constructor
      case left => exact ih.2 --equiv
      case right => intro v; simp[nnf, eval, ih.1 v]

end Logic.Prop
