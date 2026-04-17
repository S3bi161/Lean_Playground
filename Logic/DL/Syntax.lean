import Logic.Prop.Syntax

namespace Logic.DL

inductive Relation : Type
  | relAtom : Nat → Relation -- atomic relations modelled as natural numbers
  | anywhere : Relation --
  | wild : Relation -- wildcard •
  | comp : Relation → Relation → Relation -- composition α.β
  | alt : Relation → Relation → Relation -- alternation α ∪ β
  | iter : Relation → Relation --iteration α*

inductive DLForm : Type
  | atom : String → DLForm -- atomic propositions modelled as strings
  | falsum : DLForm -- falsum ⊥
  | imp : DLForm → DLForm → DLForm -- implication φ → ψ
  | diamond : Relation → DLForm → DLForm -- diamond ⟨α⟩φ

--derived syntactic sugar
open DLForm

-- negation ¬φ
def not (φ : DLForm) : DLForm := imp φ falsum

-- true ⊤
def true : DLForm := not falsum

--conjunction φ ∧ ψ
def conj (φ ψ: DLForm) : DLForm := not (imp φ (not ψ))

--disjunction φ ∨ ψ
def disj (φ ψ: DLForm) : DLForm := imp (not φ) ψ

--box [α]φ
def box (α: Relation) (φ: DLForm) : DLForm := not (diamond α (not φ))

end Logic.DL
