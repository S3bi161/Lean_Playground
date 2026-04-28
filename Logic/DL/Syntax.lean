namespace Logic.DL

inductive Relation (RelType: Type) : Type
  | relAtom : RelType → Relation RelType
  | emptyset : Relation RelType -- emptyset ∅
  | wild : Relation RelType -- wildcard •
  | comp : Relation RelType → Relation RelType → Relation RelType -- composition α.β
  | alt : Relation RelType → Relation RelType → Relation RelType -- alternation α ∪ β
  | iter : Relation RelType → Relation RelType --iteration α*

inductive DLForm (RelType AtomType: Type) : Type
  | atom : AtomType → DLForm RelType AtomType -- atomic propositions modelled as strings
  | falsum : DLForm RelType AtomType -- falsum ⊥
  | imp : DLForm RelType AtomType → DLForm RelType AtomType → DLForm RelType AtomType -- implication φ → ψ
  | diamond : Relation RelType → DLForm RelType AtomType → DLForm RelType AtomType -- diamond ⟨α⟩φ

--derived syntactic sugar
open DLForm

-- negation ¬φ
def not (φ: DLForm RelType AtomType): DLForm RelType AtomType := imp φ falsum

-- true ⊤
def true : DLForm RelType AtomType := not falsum

--conjunction φ ∧ ψ
def conj (φ ψ: DLForm RelType AtomType) : DLForm RelType AtomType := not (imp φ (not ψ))

--disjunction φ ∨ ψ
def disj (φ ψ: DLForm RelType AtomType) : DLForm RelType AtomType := imp (not φ) ψ

--box [α]φ
def box (α: Relation RelType) (φ: DLForm RelType AtomType) : DLForm RelType AtomType := not (diamond α (not φ))


-- concrete relation type for dynamic indices
inductive DynamicIndices: Type
  | line: Nat → DynamicIndices
  | dollar: DynamicIndices
  | hash: DynamicIndices
deriving DecidableEq, BEq

-- concrete formula type, strings for modelling assertions
inductive Atoms: Type
  | name: String → Atoms
deriving DecidableEq, BEq

end Logic.DL
