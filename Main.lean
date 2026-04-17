import Logic.Prop.Syntax
import Logic.Prop.Semantics
import Logic.DL.Syntax
import Logic.DL.Semantics

def main : IO Unit := pure ()
section
  open Logic.Prop
  open PropositionalForm

  -- p ∧ q
  def f : PropositionalForm :=
    myAnd (var "p") (var "q")

  #check f

  -- example interpretation I with I(p) = I(q) = 1
  def I : Valuation
    | "p" => true
    | "q" => true
    | _ => false

  #eval eval I f -- evaluate I(p ∧ q)

end

open Logic.DL

-- example kripke model
def model: KripkeModel where
  val := fun atom state => match atom, state with
    | "p", 0 => True --p holds in state 0
    | "q", 1 => True -- q holds in state 1
    | _, _ => False -- anything else false
  rel := fun atom state state' => match atom, state, state' with
    | 0, 0, 1 => True -- relation 0 ~ step state 0 to state 1
    | 1, 1, 0 => True -- relation 1 ~ step state 1 to state 0
    | _, _, _ => False

-- example dl formulas
open DLForm
open Relation
def p: DLForm := atom "p"
def q: DLForm := atom "q"

def φ: DLForm := diamond (relAtom 0) q

--evaluate model, 0 ⊧ ⟨0⟩q
example : eval model φ 0 :=
by
  simp[eval, evalRel, model, φ, q]
  apply Exists.intro 1
  simp

def α: Relation := comp (relAtom 1) (relAtom 0) --relation 1.0
def β: Relation := alt (relAtom 0) (relAtom 1) --relation 0 ∪ 1

-- ψ = ⟨1.0⟩q ∧ ⟨0 ∪ 1⟩p
def ψ: DLForm := conj (diamond α q) (diamond β p)

--evaluate model, 1 ⊧ ψ
example : eval model ψ 1 :=
by
  simp[eval, evalRel, model, ψ, α, β, conj, Logic.DL.not]
  apply Exists.intro 1
  apply Exists.intro 0
  simp[eval, q]
  apply Exists.intro 0
  simp[eval, p]

example : eval model (diamond (anywhere) (conj (not p) (not q))) 0 :=
by
  simp[eval, evalRel, model]
  apply Exists.intro 2
  simp[Logic.DL.not, conj, eval, p, q]

example: eval model (diamond (wild) q) 0:=
by
  simp[eval, evalRel, model]
  apply Exists.intro 1
  simp[eval, q]
  apply Exists.intro 0
  simp
