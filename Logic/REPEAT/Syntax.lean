namespace Logic.REPEAT


--Variables
inductive Var: Type
  | name: String → Var
deriving DecidableEq, BEq


/-
Expressions
-/
mutual
  inductive Expr: Type
    | const: Int → Expr                 --constant integers
    | access: Var → Expr → Expr         --variable access `v[e]`
    | sub: Expr → Expr → Expr           --subtraction `e₀ - e₁
    | cond: Cond → Expr
  --| le: Expr → Expr → Expr            --condition `e₀ ≤ e₁`

    inductive Cond: Type
    | le: Expr → Expr → Cond

end
deriving instance DecidableEq for Expr
deriving instance DecidableEq for Cond
deriving instance BEq for Expr
deriving instance BEq for Cond

-- Arguments
inductive Arg: Type
  | var: Var → Arg                   --call by value
  | ref: Var → Arg                   --call by name
deriving DecidableEq, BEq

--Statements
inductive Stmt: Type
  | call: Expr → List Arg → Stmt     --`call INT_PROC_ID (args*)`
  | assign: Var → Expr → Expr → Stmt --assignment `v[e₀] = e₁`
  | returnIf: Expr → Stmt            --conditional return `if e₀ return`
  | repeat: Stmt                     -- `repeat` statement present at the end of every procedure
deriving DecidableEq, BEq

--enumerated statements, i.e. carrying line number
structure LStmt where
  line: Nat                           --line number
  stmt: Stmt                          --statement

--Procedures
structure Proc where
  id: Int                             --proc id with constant name
  params: List Var                    --formal parameters of a procedure
  body: List LStmt                    --procedure body as a list of numbered stmts

--Programs are just lists of procedures
abbrev Program := Int → Option Proc   -- may be undefined


--Syntactic sugar
namespace Expr

--variable shorthand `x = x[0]`
def var (v: Var) : Expr :=
  access v (const 0)


--boolean constants
def TRUE : Expr := const 1
def FALSE: Expr := const 0

--unary minus
def unMin (e: Expr): Expr := sub (const 0) e

--addition
def add (e₀ e₁: Expr): Expr := sub e₀ (unMin e₁)

namespace Cond

-- ¬c := c ≤ 0
def not (c: Cond): Cond := Cond.le (cond c) (const 0)

-- c₀ ∨ c₁ := ¬c₀ ≤ c₁
def disj (c₀ c₁: Cond): Cond := Cond.le (cond (not c₀)) (cond c₁)

-- c₀ ∧ c₁ := ¬(¬c₀ ∧ ¬c₁)
def conj (c₀ c₁: Cond): Cond := not (disj (not c₀) (not c₁))

-- e₀ == e₁ := e₀ ≤ e₁ ∧ e₁ ≤ e₀
def eq (e₀ e₁: Expr): Cond := conj (Cond.le e₀ e₁) (Cond.le e₁ e₀)

end Cond
end Expr

end Logic.REPEAT
