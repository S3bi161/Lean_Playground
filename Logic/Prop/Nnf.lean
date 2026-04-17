import Logic.Prop.Semantics
namespace Logic.Prop

open PropositionalForm
-- negative normal form
def nnf : PropositionalForm -> PropositionalForm
  | var x => var x
  | myFalse => myFalse
  | myAnd φ ψ => myAnd (nnf φ) (nnf ψ)
  | myNot φ => match φ with
    | var x => myNot (var x)
    | myFalse => myTrue
    | myAnd ψ₁ ψ₂ => myOr (nnf (myNot ψ₁)) (nnf (myNot ψ₂))
    | myNot ψ => nnf ψ

end Logic.Prop
