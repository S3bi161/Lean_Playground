import Logic.REPEAT.Syntax
import Logic.DL.Syntax
import Logic.Common.DynamicIndex

namespace Logic.DL

abbrev FreeVar := String

-- at verification/tableau level, also @fn, evaluating to the proc id is an expression
inductive TExpr : Type
  | program : Expr → TExpr
  | fn : TExpr
deriving DecidableEq, BEq


inductive TCond : Type
  | le : TExpr → TExpr → TCond
deriving DecidableEq, BEq

-- temporary new DAForm to include @fn
abbrev TDAForm := DLForm DynIndex TCond


inductive Sign : Type
  | pos : Sign
  | neg : Sign
deriving DecidableEq, BEq

-- represents an indexed formula s: φ as {Sign.pos, s, φ} or s̄: φ as {Sign.neg, s, φ}
structure IndexedForm where
  sign : Sign
  index: DynIndex
  form : TDAForm
deriving DecidableEq, BEq

-- represents an indexed expr x = s: ⌞e⌟ as {x, s, e}
structure IndexedExpr where
  free_var : FreeVar
  index : DynIndex
  expr : TExpr
deriving DecidableEq, BEq

-- represents an indexed program variable x = s: a[y] as {x, s, a, y}
structure IndexedVar where
  free_var : FreeVar
  index : DynIndex
  arr : Var
  arr_idx : FreeVar
deriving DecidableEq, BEq

-- type representing the arithmetic expression over free variables in tableau nodes
inductive AExp: Type
  | var : FreeVar → AExp
  | const : Int → AExp
  | add : AExp → AExp → AExp
  | neg : AExp → AExp
deriving DecidableEq, BEq

-- arithmetic constraints (i.e. e₁ ≤ e₂ or e₁ = e₂)
inductive ArithConstraint: Type
  | le : AExp → AExp → ArithConstraint
  | eq : AExp → AExp → ArithConstraint
deriving DecidableEq, BEq

-- representing a tableau node, being either an indexed formula, expression, program variable or arithmetic constraint
inductive TableauNode: Type
  | form  : IndexedForm → TableauNode
  | expr  : IndexedExpr → TableauNode
  | var   : IndexedVar → TableauNode
  | arith : ArithConstraint → TableauNode
deriving DecidableEq, BEq

-- a branch is a list of tableau nodes
abbrev Branch := List TableauNode

-- stores the rule target nodes, i.e. the nodes a rule is applied on
structure Selection where
  branch : Branch
  positions : List (Fin branch.length)

def Selection.nodes (sel: Selection) : List TableauNode :=
  sel.positions.map sel.branch.get

-- given a selection of nodes, a rule application generates a list of branches if applicable.
abbrev Rule := Selection → Option (List Branch)


/- # Rule definitions -/

def suitableVar (branch: Branch) (s: DynIndex) (e: TExpr) : FreeVar :=
  sorry

/-  s: φ → ψ
(→)-------------
    s̄: φ | s: ψ
-/
def posImpRule : Rule :=
  λ sel ↦
    match sel.nodes with
    | [TableauNode.form               -- selected node is s: φ → ψ
       {sign := Sign.pos,
        index := s,
        form := DLForm.imp φ ψ
      }] =>
        some [
          --first branch
          sel.branch ++ [
            TableauNode.form {        -- append node s̄: φ
              sign := Sign.neg,
              index := s
              form := φ
            }],
          --second branch
          sel.branch ++ [
            TableauNode.form {        -- append node s: ψ
              sign := Sign.pos,
              index := s
              form := ψ
            }
          ]
        ]
    | _ => none                       -- return none iff rule is not applicable wrt selection


/-  s̄: φ → ψ
(̄→)----------
    s: φ
    s̄: ψ
-/
def negImpRule : Rule :=
  λ sel ↦
    match sel.nodes with
    | [TableauNode.form               -- selected node is s̄: φ → ψ
       {sign := Sign.neg,
        index := s,
        form := DLForm.imp φ ψ
      }] =>
        some [
          sel.branch ++ [
            TableauNode.form {        -- append node s: φ
              sign := Sign.pos,
              index := s,
              form := φ
            },
            TableauNode.form {        -- append node s̄: ψ
              sign := Sign.neg,
              index := s,
              form := ψ
            }
          ]
        ]
    | _ => none                       -- return none iff rule is not applicable wrt selection

/-
    s: ⊥
(⊥)-------
      ×
-/
def posFalsumRule : Rule :=
  λ sel ↦
    match sel.nodes with
    | [TableauNode.form
       {sign := Sign.pos,
        index := _,
        form := DLForm.falsum
      }] => some []                   -- close branch, i.e. return empty list []
    | _ => none

/-
    ̄s: ⊥
(̄→)------

-/
def negFalsumRule : Rule :=
  λ sel ↦
    match sel.nodes with
    | [TableauNode.form
       {sign := Sign.neg,
        index := _,
        form := DLForm.falsum
      }] => some [sel.branch]         -- return unmodified branch (no-op)
    | _ => none

/-
    s: ⌞e₁ ≤ e₂⌟
(≤)-------------- x, y suitable
       x ≤ y
     x = s:⌞e₁⌟
     y = s:⌞e₂⌟
-/
def posLeRule : Rule :=
  λ sel ↦
    match sel.nodes with
    | [TableauNode.form
       {sign := Sign.pos,
        index := s,
        form := DLForm.atom (TCond.le e₁ e₂)}] =>

          let x := suitableVar sel.branch s e₁
          let y := suitableVar sel.branch s e₂

          some [
            sel.branch ++ [
              -- append node x ≤ y
              TableauNode.arith (ArithConstraint.le (AExp.var x) (AExp.var y)),

              -- append node x = s:⌞e₁⌟
              TableauNode.expr {
                free_var := x,
                index := s,
                expr := e₁
              },
              -- append node y = s:⌞e₂⌟
              TableauNode.expr {
                free_var := y,
                index := s,
                expr := e₂
              }
            ]

          ]
    | _ => none

end Logic.DL
