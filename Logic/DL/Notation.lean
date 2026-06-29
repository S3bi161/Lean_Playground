import Logic.DL.Syntax
import Logic.REPEAT.Semantics


namespace Logic.DL

/-
# Remarks
- This approach is only applicable when using the monomorphic DAForm, which fixes DynamicIndices and Cond as DLForm Types.
- In order to avoid confusion with Leans inbuilt notation for Props, the following logical connectives have to be chosen slightly different than usual textbook:
  • `⋎` for DL "or"
  • `⋏` for DL "and"
  • `∼` for DL "not"
-/

--formulas
abbrev DAForm := DLForm DynIdxSym Cond
-- relevant coercions
instance: Coe DynIdxSym (Relation DynIdxSym) where
  coe α := Relation.relAtom α

instance: OfNat DynIdxSym n where
  ofNat := DynIdxSym.line n

instance: OfNat (Relation DynIdxSym) n where
  ofNat := Relation.relAtom (DynIdxSym.line n)

instance: Coe String Expr where
  coe s := Expr.var (Var.name s)

instance: Coe Cond DAForm where
  coe c := DLForm.atom c

--basic notations
notation "∅" => Relation.emptyset
notation "•" => Relation.wild

notation "⊥" => DLForm.falsum


--relation operators
notation:100 α "*" => Relation.iter (α: Relation DynIdxSym)
notation:80 α:81 β:80 => Relation.comp (α: Relation DynIdxSym) (β: Relation DynIdxSym)
notation:70 α:71 " ∪ " β:70 => Relation.alt (α: Relation DynIdxSym) (β: Relation DynIdxSym)




notation:90 "⟨" α "⟩" φ => DLForm.diamond (α: Relation DynIdxSym) (φ: DAForm)
notation:90 "[" α "]" φ => box (α: Relation DynIdxSym) (φ: DAForm)
notation:85 "∼" φ:85 => not (φ: DAForm)
notation:70 φ:71 " ⋏ " ψ:70 => conj (φ: DAForm) (ψ: DAForm)
notation:60 φ:61 " ⋎ " ψ:60 => disj (φ: DAForm) (ψ: DAForm)
notation:50 φ:51 " → " ψ:50 => DLForm.imp (φ: DAForm) (ψ: DAForm)


infix:110 "=ₑ" => Expr.Cond.eq
infix:110 "<ₑ" => Cond.le

#check 0 1 2 3 #
#check [(0 1 * ∪ 1)*]
#check 0 ∪ 1 * ∪ #
#check ⟨0 $⟩ ("p" =ₑ "q")
#check ∼⟨0 #⟩ (∼ "p" <ₑ "q") ⋎ "q" <ₑ "p"
#check ⊥
#check #
#check ∅


end Logic.DL
