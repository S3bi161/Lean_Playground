
namespace Logic.Prop

-- Representation of propositional formulas
inductive PropositionalForm : Type
  | var : String -> PropositionalForm
  | myFalse : PropositionalForm
  | myNot : PropositionalForm -> PropositionalForm
  | myAnd : PropositionalForm -> PropositionalForm -> PropositionalForm

-- Syntactic sugar for additional connectives
def myOr (p q: PropositionalForm): PropositionalForm :=
  PropositionalForm.myNot (PropositionalForm.myAnd (PropositionalForm.myNot p) (PropositionalForm.myNot q))

def myTrue : PropositionalForm := PropositionalForm.myNot PropositionalForm.myFalse

def imp (p q: PropositionalForm): PropositionalForm := myOr (PropositionalForm.myNot p) q

end Logic.Prop
