import Logic.DL.Syntax
namespace Logic.DL

/-
# Remarks
- This approach is only applicable when using the monomorphic DAForm, which fixes DynamicIndices and Atoms as DLForm Types
- Any non atomic formula has to be parenthesized in order to ensure correct precedence - TODO!
- Whitespaces need to be present between composition operator "." and the operands when using Nats, otherwise parsed as single number
-/


-- relevant coercions
instance: Coe DynamicIndices (Relation DynamicIndices) where
  coe α := Relation.relAtom α

instance: OfNat DynamicIndices n where
  ofNat := DynamicIndices.line n

instance: OfNat (Relation DynamicIndices) n where
  ofNat := Relation.relAtom (DynamicIndices.line n)

instance: Coe String (DLForm DynamicIndices Atoms) where
  coe p := DLForm.atom (Atoms.name p)

instance: Coe String Atoms where
  coe p := Atoms.name p

--basic notations
notation "$" => DynamicIndices.dollar
notation "#" => DynamicIndices.hash

notation "∅" => Relation.emptyset
notation "•" => Relation.wild

notation "⊥" => DLForm.falsum


--relation operators
notation:80 α " . " β  => Relation.comp (α: Relation DynamicIndices) (β: Relation DynamicIndices)
notation:70 α " ∪ " β => Relation.alt (α: Relation DynamicIndices) (β: Relation DynamicIndices)
notation:max α "*" => Relation.iter (α: Relation DynamicIndices)

--formulas
abbrev DAForm := DLForm DynamicIndices Atoms

notation:60 φ " → " ψ => DLForm.imp (φ: DAForm) (ψ: DAForm)
notation:90 "⟨" α "⟩" φ => DLForm.diamond (α: Relation DynamicIndices) (φ: DAForm)
notation:90 "[" α "]" φ => box (α: Relation DynamicIndices) (φ: DAForm)
notation:85 "¬" φ => not (φ: DAForm)
notation:70 φ " ∧ " ψ => conj (φ: DAForm) (ψ: DAForm)
notation:65 φ " ∨ " ψ => disj (φ: DAForm) (ψ: DAForm)


#check [(0)*] "p"
#check ¬⟨0 . $⟩ ¬"p" ∧ "q"
#check ¬⟨0 . #⟩ (¬ "p") ∧ "q"
#check "p" ∨ "q" ∧ "p"
#check ("p" ∧ "q") ∨ "p"
#check "p" ∧ ⊥ ∨ "p"
#check "p" → "q"
#check ⊥
#check #
#check ∅


end Logic.DL
