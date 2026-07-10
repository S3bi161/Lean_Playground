namespace Logic.DL


/--
Inductive Type `DynIndexSym` modelling *the alphabet* Σ over which dynamic indices are built of.
Dynamic index symbols are
  • natural numbers       - modelling line numbers
  • hash symbol #         - modelling termination
  • dollar symbol $       - modelling iteration

Dynamic index symbols serve as type for atomic relations in DA logic.
Thus an atomic relation is either a natural number, # or $, but not a composed dynamic index.

If Lean can't figure out that a natural number `n` is supposed to be a DynIndexSym, use the notation `ι n` for the line constructor.
On the other hand, `ι i` can also be used to signify that `i` is specifically a line number (and not $ or #), so that e.g. `ι (i+1)` is a valid expression.
-/
inductive DynIndexSym where
  | line : Nat → DynIndexSym                  -- line number n
  | hash : DynIndexSym                        -- #
  | dollar : DynIndexSym                      -- $
deriving DecidableEq

/--
Inductive Type `DynIndex` modelling dynamic indices, i.e. words from Σ*, where Σ are dynamic index symbols, modelled by `DynIndexSym`

Dynamic indices model program states in Executions and thus serve as states of the Kripke Model K_E associated with the execution E.
Each dynamic index is prefixed by ε, i.e. the `root` in this model, after which dynamic index symbols can be concatened with the `cons` constructor.

Notation for `root` is ε, for `cons` its `∘ᵢ`.

Examples of dynamic indices:
  • ε
  • ε ∘ᵢ 0 ∘ᵢ 1 ∘ᵢ #
  • ε ∘ᵢ $
-/
inductive DynIndex where
  | root : DynIndex                           -- ε
  | cons : DynIndex → DynIndexSym → DynIndex  -- s ∘ᵢ i, where s is a dynamic index and i a dynamic index symbol
deriving DecidableEq

def line (ι: DynIndex) (n: Nat) :=
  DynIndex.cons ι (DynIndexSym.line n)

def dollar (ι: DynIndex) :=
  DynIndex.cons ι DynIndexSym.dollar

def hash (ι: DynIndex) :=
  DynIndex.cons ι DynIndexSym.hash

instance : Coe Nat DynIndexSym where
  coe := DynIndexSym.line

notation "ε" => DynIndex.root
notation "$" => DynIndexSym.dollar
notation "#" => DynIndexSym.hash
notation "ι" => DynIndexSym.line
infixl:80 "∘ᵢ" => DynIndex.cons

end Logic.DL
