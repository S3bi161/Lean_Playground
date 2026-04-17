import Logic.Prop.Syntax

namespace Logic.Prop
-- propositional evaluation
def Valuation := String -> Bool

def eval (v : Valuation) : PropositionalForm -> Bool
  | PropositionalForm.var x => v x
  | PropositionalForm.myFalse => false
  | PropositionalForm.myAnd φ ψ => eval v φ && eval v ψ
  | PropositionalForm.myNot φ => ! eval v φ

-- logic equivalence
def equiv (φ ψ: PropositionalForm) : Prop :=
  ∀ v, eval v φ = eval v ψ

end Logic.Prop
