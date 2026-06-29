namespace Logic.DL

inductive DynIdxSym where
  | line : Nat → DynIdxSym
  | hash : DynIdxSym
  | dollar : DynIdxSym
deriving DecidableEq

inductive DynIndex where
  | root : DynIndex
  | cons : DynIndex → DynIdxSym → DynIndex
deriving DecidableEq

def line (ι: DynIndex) (n: Nat) :=
  DynIndex.cons ι (DynIdxSym.line n)

def dollar (ι: DynIndex) :=
  DynIndex.cons ι DynIdxSym.dollar

def hash (ι: DynIndex) :=
  DynIndex.cons ι DynIdxSym.hash

instance : Coe Nat DynIdxSym where
  coe := DynIdxSym.line

notation "ε" => DynIndex.root
notation "$" => DynIdxSym.dollar
notation "#" => DynIdxSym.hash
notation "ι" => DynIdxSym.line
infixl:80 "∘" => DynIndex.cons

end Logic.DL
