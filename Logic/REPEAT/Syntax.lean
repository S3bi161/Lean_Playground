namespace Logic.REPEAT


--Variables
inductive Var: Type
  | name: String → Var
deriving DecidableEq, BEq


/-
Expressions
TODO: Design choice - keep Expressions and Conditions seperated?
-/

inductive Expr: Type
  | const: Int → Expr                 --constant integers
  | access: Var → Expr → Expr         --variable access `v[e]`
  | sub: Expr → Expr → Expr           --subtraction `e₀ - e₁`
  | le: Expr → Expr → Expr            --condition `e₀ ≤ e₁`
deriving DecidableEq, BEq

-- Arguments
inductive Arg: Type
  | var: Var → Arg                   --call by value
  | ref: Var → Arg                   --call by name
deriving DecidableEq, BEq

--Statements
inductive Stmt: Type
  | call: Expr → List Arg → Stmt    --`call INT_PROC_ID (args*)`
  | assign: Var → Expr → Expr → Stmt --assignment `v[e₀] = e₁`
  | returnIf: Expr → Stmt            --conditional return `if e₀ return`
deriving DecidableEq, BEq

--enumerated statements, i.e. carrying line number
structure LStmt where
  line: Nat                           --line number
  stmt: Stmt                          --statement

--Procedures
structure Proc where
  id: Int                             --proc id
  params: List Var                    --formal parameters of a procedure
  body: List LStmt                    --procedure body as a list of numbered stmts
  loops: Bool                         --flag for repeat keyword

--Programs are just lists of procedures
abbrev Program := List Proc


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


/-
Derived boolean operators. As of right now, there is nothing enforcing the operands are only 0/1
- see TODO design choice for expressions
-/
-- ¬c := c ≤ 0
def not (c: Expr): Expr := le c (const 0)

-- c₀ ∨ c₁ := ¬c₀ ≤ c₁
def disj (c₀ c₁: Expr): Expr := le (not c₀) c₁

-- c₀ ∧ c₁ := ¬(c₀ ≤ ¬c₁)
def conj (c₀ c₁: Expr): Expr := not (le c₀ (not c₁))

-- e₀ == e₁ := e₀ ≤ e₁ ∧ e₁ ≤ e₀
def eq (e₀ e₁: Expr): Expr := conj (le e₀ e₁) (le e₁ e₀)

end Expr
end Logic.REPEAT
