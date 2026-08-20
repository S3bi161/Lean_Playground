import Logic.DL.Syntax
import Logic.REPEAT.Semantics


namespace Logic.DL

/-
# Remarks
- This approach is only applicable when using the monomorphic DAForm, which fixes DynamicIndices and Cond as DLForm Types.
- In order to avoid confusion with Leans inbuilt notation for Props, the following logical connectives have to be chosen slightly different than usual textbook:
  • `∨ₗ` for DL "or"
  • `∧ₗ` for DL "and"
  • `¬ₗ` for DL "not"
-/

--formulas
abbrev DAForm := DLForm DynIndexSym Cond
-- relevant coercions
instance: Coe DynIndexSym (Relation DynIndexSym) where
  coe α := Relation.relAtom α

instance: OfNat DynIndexSym n where
  ofNat := DynIndexSym.line n

instance: OfNat (Relation DynIndexSym) n where
  ofNat := Relation.relAtom (DynIndexSym.line n)

instance: Coe String Expr where
  coe s := Expr.var (Var.loc (LocVar.name s))

instance: Coe Cond DAForm where
  coe c := DLForm.atom c

--basic notations
notation "∅" => Relation.emptyset
notation "•" => Relation.wild

notation "⊥" => DLForm.falsum


--relation operators
notation:100 α "*" => Relation.iter (α: Relation DynIndexSym)
notation:80 α:81 "∘ₗ" β:80 => Relation.comp (α: Relation DynIndexSym) (β: Relation DynIndexSym)
notation:70 α:71 " ∪ " β:70 => Relation.alt (α: Relation DynIndexSym) (β: Relation DynIndexSym)


notation:90 "⟨" α "⟩ₗ" φ => DLForm.diamond (α: Relation DynIndexSym) (φ: DAForm)
notation:90 "[" α "]ₗ" φ => box (α: Relation DynIndexSym) (φ: DAForm)
notation:85 "¬ₗ" φ:85 => not (φ: DAForm)
notation:70 φ:71 " ∧ₗ " ψ:70 => conj (φ: DAForm) (ψ: DAForm)
notation:60 φ:61 " ∨ₗ " ψ:60 => disj (φ: DAForm) (ψ: DAForm)
notation:50 φ:51 " →ₗ " ψ:50 => DLForm.imp (φ: DAForm) (ψ: DAForm)


infix:110 "=ₑ" => Expr.Cond.eq
infix:110 "≤ₑ" => Cond.le

#check ε ∘ᵢ 0 ∘ᵢ 1 ∘ᵢ 2 ∘ᵢ 3 ∘ᵢ #
#check [(0 ∘ₗ 1* ∪ 1)*]ₗ "p" =ₑ "q"
#check 0 ∪ 1 * ∪ #
#check ⟨0 ∘ₗ $⟩ₗ ("p" =ₑ "q")
#check ¬ₗ ⟨0 ∘ₗ #⟩ₗ (¬ₗ "p" ≤ₑ "q") ∨ₗ "q" ≤ₑ "p"
#check ⊥
#check #
#check ∅

end Logic.DL
