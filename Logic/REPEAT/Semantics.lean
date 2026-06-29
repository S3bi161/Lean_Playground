import Mathlib.Data.Set.Basic
import Logic.REPEAT.Syntax
import Logic.DL.Semantics
import Logic.Common.DynamicIndex

namespace Logic.DL


/-
inductive DynIndex where
  | root : DynIndex
  | line : DynIndex → Nat → DynIndex
  | dollar: DynIndex → DynIndex
  | hash: DynIndex → DynIndex
deriving DecidableEq
-/
/--
Encapsulates a control flow trace, which is a triple P = (Q, prompt, tar) where
* `Q` is a Set of States, represented as `Set DynIndex`
* `prompt` is the initially executed procedure
* `tar` is the call function mapping from states to called procedures
-/
structure CFTrace where
  Q : Set DynIndex
  prompt : Stmt
  tar : DynIndex → Option Proc


/--
Quasi Execution quadruple Q = (P, seed), where P is a control flow trace and seed provides initial variable values
-/
structure QuasiExecution where
  cft : CFTrace
  seed : DynIndex → Var → Int → Int


/--
Partial stmt function, which evaluates to the statement at a given dynamic index
-/
def stmt (cft: CFTrace) (idx: DynIndex) : Option Stmt :=
  match idx with
    | .root => some cft.prompt -- stmt(ε) = prompt, where [] represents ε
    | .cons s sym  => -- stmt(s i)
        match sym with
          | .line i =>
              match cft.tar s with  --cft.tar s is the current procedure
                | none => none       --shouldn't occur in valid cft (i.e. s i ∈ Q → ∃ p, tar s = some p)
                | some proc =>
                    match proc.body.find? (λ ls => ls.line == i) with
                      | none => none
                      | some ls => some ls.stmt

          | _ => none


def currentProcId (cft: CFTrace) (idx: DynIndex) : Option Int :=
  match idx with
    | .root =>     match cft.prompt with
                    | Stmt.call (Expr.const id) _ => id   --TODO: Requires call to constant, i.e. no call arithmetic is possible => otherwise currentProcId depends on val
                    | _ => none
    | .cons s _ => match cft.tar s with
                    | some proc => proc.id
                    | none => none


/- Closure properties for the set of states Q in a cft-/

--ε ∈ Q and prompt is a call
def rootClosure (cft: CFTrace) : Prop :=
  ε ∈ cft.Q ∧
  ∃ expr args, cft.prompt = Stmt.call expr args


-- if s ∈ Q and stmt (s) is a call `call expr args`, then s 0 ∈ Q and tar(s) maps to a arity matching procedure
def callClosure (cft: CFTrace) : Prop :=
  ∀ s expr args,
    ((s ∈ cft.Q ∧ stmt cft s = some (Stmt.call expr args)) →

      line s 0 ∈ cft.Q ∧
      ∃ proc, (cft.tar s = some proc ∧ args.length = proc.params.length))

-- if s i ∈ Q and stmt(s i) is an assignment `v[e₀] = e₁`, then s (i+1) ∈ Q
def assignClosure (cft: CFTrace) : Prop :=
  ∀ s i v e₀ e₁,
    (line s i ∈ cft.Q ∧
     stmt cft (line s i) = some (Stmt.assign v e₀ e₁) →

     line s (i + 1) ∈ cft.Q)

-- if s i ∈ Q and stmt(s i) is a returnIf `if e return ` then either s (i+1) ∈ Q or s # ∈ Q
def returnClosure (cft: CFTrace) : Prop :=
  ∀ s i e,
    (line s i) ∈ cft.Q ∧
     stmt cft (line s i) = some (Stmt.returnIf e) →

     (line s (i + 1) ∈ cft.Q ∨ s ∘ # ∈ cft.Q)

-- if s i ∈ Q and stmt(s i) is `repeat`, then s $ ∈ Q, s $ 0 ∈ Q and tar(s $) = tar(s)
def repeatClosure (cft: CFTrace) : Prop :=
  ∀ s i proc,
    (line s i ∈ cft.Q ∧
     stmt cft (line s i) = some (Stmt.repeat) ∧
     cft.tar s = some proc) →

      (s ∘ $ ∈ cft.Q ∧
       line (s ∘ $) 0 ∈ cft.Q ∧
       cft.tar (s ∘ $) = some proc)

-- if s $ # ∈ Q, then s # ∈ Q
def repeatReturnClosure (cft: CFTrace) : Prop :=
  ∀ s,
    (s ∘ $) ∘ # ∈ cft.Q → s ∘ # ∈ cft.Q

-- if s i # ∈ Q, then s (i + 1) ∈ Q
def callReturnClosure (cft: CFTrace) : Prop :=
  ∀ s i,
    (line s i) ∘ # ∈ cft.Q → line s (i + 1) ∈ cft.Q


/- No junk properties for the set of states Q in a cft -/

-- if s 0 ∈ Q, then s = ε or stmt(s) is a call `call expr args` with matching tar arity or s = t $ with stmt(t i) = `repeat`
def noJunkCalls (cft: CFTrace) : Prop :=
  ∀ s,
    line s 0 ∈ cft.Q →
      (s = ε ∨
       (∃ expr args proc, s ∈ cft.Q ∧ stmt cft s = some (Stmt.call expr args) ∧
        cft.tar s = some proc ∧ args.length = proc.params.length) ∨
       (∃ t i, s = t ∘ $ ∧ line t i ∈ cft.Q ∧ stmt cft (line t i) = some (Stmt.repeat))
       )

-- if s i+1 ∈ Q, then s i ∈ Q and stmt(s i) is an assign `v[e₀] = e₁` or returnIf `if e return`
def noJunkLines (cft: CFTrace) : Prop :=
  ∀ s i,
    line s (i+1) ∈ cft.Q →
      ((∃ v e₀ e₁,
       line s i ∈ cft.Q ∧
       stmt cft (line s i) = some (Stmt.assign v e₀ e₁)) ∨
      (∃ e,
       line s i ∈ cft.Q ∧
       stmt cft (line s i) = some (Stmt.returnIf e)))

-- if s # ∈ Q, then s i ∈ Q and stmt(s i) is a returnIf `if e return` or (s $)# ∈ Q
def noJunkReturns (cft: CFTrace) : Prop :=
  ∀ s,
    (s ∘ #) ∈ cft.Q →
      ((∃ i e,
       line s i ∈ cft.Q ∧
       stmt cft (line s i) = some (Stmt.returnIf e)) ∨
      (s ∘ $) ∘ # ∈ cft.Q)

-- if s $ ∈ Q, then s i ∈ Q and stmt(s i) is a `repeat`
def noJunkRepeats (cft: CFTrace) : Prop :=
  ∀ s,
    s ∘ $ ∈ cft.Q →
      (∃ i,
       line s i ∈ cft.Q ∧
       stmt cft (line s i) = some (Stmt.repeat))


def cftClosure (cft: CFTrace) : Prop :=
  rootClosure cft ∧
  callClosure cft ∧
  assignClosure cft ∧
  returnClosure cft ∧
  repeatClosure cft ∧
  repeatReturnClosure cft ∧
  callReturnClosure cft

def cftNoJunk (cft: CFTrace) : Prop :=
  noJunkCalls cft ∧
  noJunkLines cft ∧
  noJunkReturns cft ∧
  noJunkRepeats cft

def validCFTrace (cft: CFTrace) : Prop :=
  cftClosure cft ∧ cftNoJunk cft


-- val is an arbitrary variable valuation. Validity based on a quasi execution is defined as prop mirroring the paper clauses
abbrev Valuation :=
  DynIndex → Var → Int → Int

-- eval on Conds and Exprs
mutual
  def evalExpr (cft: CFTrace) (val: Valuation) (s: DynIndex): Expr → Int
    | Expr.const c => c
    | Expr.access x e => val s x (evalExpr cft val s e)
    | Expr.sub e₁ e₂ => evalExpr cft val s e₁ - evalExpr cft val s e₂
    | Expr.cond c => evalCond cft val s c

  def evalCond (cft: CFTrace) (val: Valuation) (s: DynIndex): Cond → Int
    | Cond.le e₁ e₂ => if evalExpr cft val s e₁ ≤ evalExpr cft val s e₂ then
        1
      else
        0
end

-- constrain val to be a valid val on given QuasiExecution
-- val(ε) = seed(ε)
def valRoot (val: Valuation) (q: QuasiExecution) : Prop :=
  val ε = q.seed ε

-- val(s0) (x) = seed(s0) (x) if x not a param
def valCallNoPar (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s expr args proc,
    stmt q.cft s = some (Stmt.call expr args) ∧
    q.cft.tar s = some proc →
      ∀ x, (x ∉ proc.params → val (line s 0) x = q.seed (line s 0) x)

-- val(s0) (x) = val(s) (y) if x is param and y is arg for x
def valCallPar (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s expr args proc,
    stmt q.cft s = some (Stmt.call expr args) ∧
    q.cft.tar s = some proc ∧
    ∀ x y, (x, y) ∈ (List.zip proc.params args) →
      (val (line s 0) x =
       val s (match y with         -- y is of type arg, which can be either ref or var
              | Arg.var v => v
              | Arg.ref v => v))

-- val(s i+1) (x) (k) = eval (s i, rhs) if stmt (s i) is assignment `x[e] = rhs` with eval(s i, e) = k
def valAssignHit (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i x k e rhs,
    stmt q.cft (line s i) = some (Stmt.assign x e rhs) ∧
    evalExpr q.cft val (line s i) e = k →
      val (line s (i+1)) x k = evalExpr q.cft val (line s i) rhs

-- val(s i+1) (x) (k) = val(s i) (x) (k) if stmt (s i) is assignment `x[e] = rhs` with eval(s i, e) ≠ k
def valAssignMiss (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i x e rhs k,
    stmt q.cft (line s i) = some (Stmt.assign x e rhs) ∧
    evalExpr q.cft val (line s i) e ≠ k →
      val (line s (i+1)) x k = val (line s i) x k

-- val(s i+1) (x) = val(s i) (x) if stmt (s i) is assignment `y[e] = rhs` with y ≠ x
def valAssignOther (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i x y e rhs,
    stmt q.cft (line s i) = some (Stmt.assign y e rhs) ∧
    y ≠ x →
      (val (line s (i+1)) x = val (line s i) x)

-- val(s i+1) = val (s i) if stmt (s i) is returnIf `if e return` and s i+1 ∈ Q
def valNoReturn (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i e,
    stmt q.cft (line s i) = some (Stmt.returnIf e) ∧
    (line s (i+1)) ∈ q.cft.Q →
      val (line s (i+1)) = val (line s i)

-- val(s #) = val (s i) if stmt (s i) is returnIf `if e return` and s i+1 ∉ Q
def valReturn (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i e,
    stmt q.cft (line s i) = some (Stmt.returnIf e) ∧
    (line s (i+1)) ∉ q.cft.Q →
      val (s ∘ #) = val (line s i)

-- val (s $) = val (s i) if stmt (s i) is `repeat`
def valRepeat (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i,
    stmt q.cft (line s i) = some (Stmt.repeat) →
      val (s ∘ $) = val (line s i)

-- val (s $ 0) = val (s $)
def valRepeatEntry (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s,
    s ∘ $ ∈ q.cft.Q →
      val (line (s ∘ $) 0) = val (s ∘ $)


-- val (s #) = val (s $ #)
def valRepeatReturn (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s,
    (s ∘ $) ∘ # ∈ q.cft.Q →
      val (s ∘ #) = val ((s ∘ $) ∘ #)

-- val (s i+1) (x) = val (s i) (x) if stmtm (s i) is `call expr args` and no args are passed by `ref`
def valCallReturnByValue (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i expr args proc,
    stmt q.cft (line s i) = some (Stmt.call expr args) ∧
    q.cft.tar (line s i) = some proc ∧
    ∀ x, Arg.ref x ∉ args →
      (val (line s (i+1)) x = val (line s i) x)

-- val (s i+1) (x) = val (s i #) (y) if stmt (s i) is `call expr args` and x was passed for param x by `ref`
def valCallReturnByRef (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i expr args proc,
    stmt q.cft (line s i) = some (Stmt.call expr args) ∧
    q.cft.tar (line s i) = some proc ∧
    ∀ x y, (y, Arg.ref x) ∈ List.zip proc.params args →
      (val (line s (i +1)) x = val ((line s i) ∘ #) y)

def validValuation (val: Valuation) (q: QuasiExecution) : Prop :=
  valRoot val q ∧
  valCallNoPar val q ∧
  valCallPar val q ∧
  valAssignHit val q ∧
  valAssignMiss val q ∧
  valAssignOther val q ∧
  valNoReturn val q ∧
  valReturn val q ∧
  valRepeat val q ∧
  valRepeatEntry val q ∧
  valRepeatReturn val q ∧
  valCallReturnByValue val q ∧
  valCallReturnByRef val q


-- constrain quasi executions to obtain executions

-- if stmt(s i) is returnIf `if e return` then s i+1 ∈ Q ↔ eval(s i, cond)
def execReturn (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s i e,
    stmt q.cft (line s i) = some (Stmt.returnIf e) →
      (line s (i+1) ∈ q.cft.Q ↔
       evalExpr q.cft val (line s i) e = 0)

-- if stmt(s) is `call expr args`, then tar(s) = eval(s, expr)
def execCallTarget (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s expr args proc,
    stmt q.cft s = some (Stmt.call expr args) ∧
    q.cft.tar s = some proc →
      proc.id = evalExpr q.cft val s expr

-- if stmt(s) is `call expr args`, then tar(s) = eval(s 0, @fn)
def execCallFn (val: Valuation) (q: QuasiExecution) : Prop :=
  ∀ s expr args proc,
    stmt q.cft s = some (Stmt.call expr args) ∧
    q.cft.tar s = some proc →
      proc.id = evalExpr q.cft val (line s 0) (Expr.access Var.fn (Expr.const 0))

def validExecution (val: Valuation) (q: QuasiExecution) : Prop :=
  execReturn val q ∧
  execCallTarget val q ∧
  execCallFn val q


/--An Execution is a quasi execution with valuation.
It also carries validity proofs for the CFTrace, valuation and execution-/
structure Execution where
  quasi : QuasiExecution
  val: Valuation

  hCFT: validCFTrace quasi.cft
  hVal: validValuation val quasi
  hExec: validExecution val quasi


def executionModel (e: Execution) :
  DL.KripkeModel DL.DynIdxSym Cond DynIndex where
  val := λ cond s ↦ s ∈ e.quasi.cft.Q ∧ evalCond e.quasi.cft e.val s cond = 1
  rel := λ a u ua ↦ u ∈ e.quasi.cft.Q ∧ ua ∈ e.quasi.cft.Q ∧ match a with
                                       | .line i =>
                                          ua = line u i
                                        | .dollar =>
                                          ua = u ∘ $
                                        | .hash =>
                                          ua = u ∘ #


end Logic.DL
