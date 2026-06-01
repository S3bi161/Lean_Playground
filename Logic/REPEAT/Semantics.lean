import Mathlib.Data.Set.Basic
import Logic.REPEAT.Syntax

namespace Logic.REPEAT



inductive DynIndex where
  | root : DynIndex
  | line : DynIndex → Nat → DynIndex
  | dollar: DynIndex → DynIndex
  | hash: DynIndex → DynIndex
deriving DecidableEq

/--
Encapsulates a control flow trace, which is a triple P = (Q, prompt, tar) where
* `Q` is a Set of States, represented as `Set DynIndex` => this is defined later inductively
* `prompt` is the initial call to a procedure
* `tar` is the call function mapping from states to called procedures
-/
structure CFTrace where
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
    | .line s i  => -- stmt(s i)

        match cft.tar s with --ctf.tar s is the current procedure
          | none => none          --shouldn't occur in valid cft (i.e. s i ∈ Q → ∃ p, tar s = some p)
          | some proc => --TODO: Why no list indices as line numbers?
              match proc.body.find? (λ ls => ls.line == i) with --extract statement at line i
                | none => none
                | some ls => some ls.stmt
    | _ => none



--notation for readability
notation "ε" => DynIndex.root
notation:max s "$" => DynIndex.dollar s
notation:max s "#" => DynIndex.hash s


/--
Inductive Proposition defining the states in Q.
TODO: Currently: On control flow branching at `if e return` both possibilities for val(e) = TRUE and val(e) = FALSE are added.
-/
inductive InQ (cft: CFTrace): DynIndex → Prop where
  -- ε in Q
  | root: InQ cft ε

  -- if s ∈ Q and stmt (s) is a call `call expr args` then s 0 ∈ Q
  | call
    (s: DynIndex)
    (expr: Expr)
    (args: List Arg)
    (hs: InQ cft s) -- s ∈ Q
    (hstmt: stmt cft s = some (Stmt.call expr args)): --stmt (s) is a call

    InQ cft (DynIndex.line s 0)

  -- if s i ∈ Q and stmt (s i) is an assignment `v[e₀] = e₁`, then s (i+1) ∈ Q
  | assign
    (s: DynIndex)
    (i: Nat)
    (v: Var)
    (e₀ e₁: Expr)
    (hsi: InQ cft (DynIndex.line s i)) -- s i ∈ Q
    (hassign: stmt cft (DynIndex.line s i) = some (Stmt.assign v e₀ e₁)): -- stmt (s i) is assignment

    InQ cft (DynIndex.line s (i + 1))

  -- if s i ∈ Q and stmt (s i) is a returnIf `if e return` then s (i+1) ∈ Q
  | return_next
    (s: DynIndex)
    (i: Nat)
    (e: Expr)
    (hsi: InQ cft (DynIndex.line s i)) -- s i ∈ Q
    (hreturn: stmt cft (DynIndex.line s i) = some (Stmt.returnIf e)): -- stmt (s i) is return

    InQ cft (DynIndex.line s (i + 1))

  -- if s i ∈ Q and stmt (s i) is a returnIf `if e return` then s # ∈ Q
  | return_exit
    (s: DynIndex)
    (i: Nat)
    (e: Expr)
    (hsi: InQ cft (DynIndex.line s i)) -- s i ∈ Q
    (hreturn: stmt cft (DynIndex.line s i) = some (Stmt.returnIf e)): -- stmt (s i) is return

    InQ cft (s #)

  -- if s i ∈ Q and stmt (s i) is `repeat` then s $ ∈ Q
  | repeat_iter
    (s: DynIndex)
    (i: Nat)
    (hsi: InQ cft (DynIndex.line s i)) -- s i ∈ Q
    (hrepeat: stmt cft (DynIndex.line s i) = some (Stmt.repeat)): -- stmt (s i) is repeat

    InQ cft (s $)

  -- if s i ∈ Q and stmt (s i) is `repeat` then s $ 0 ∈ Q
  | repeat_entry
    (s: DynIndex)
    (i: Nat)
    (hsi: InQ cft (DynIndex.line s i)) -- s i ∈ Q
    (hrepeat: stmt cft (DynIndex.line s i) = some (Stmt.repeat)): -- stmt (s i) is repeat

    InQ cft (DynIndex.line  (s $) 0)

  -- if s $ # ∈ Q then s # ∈ Q
  | repeat_return
    (s: DynIndex)
    (hs: InQ cft ((s $) #)): -- s $ # ∈ Q

    InQ cft (s #)

  -- if s i # ∈ Q, then s (i+1) ∈ Q
  | call_return
    (s: DynIndex)
    (i: Nat)
    (hsi: InQ cft  ((DynIndex.line s i) #) ): -- s i # ∈ Q

    InQ cft (DynIndex.line s (i+1))


def CFTrace.Q (cft: CFTrace): Set DynIndex :=
  { s | InQ cft s}

def wellFormedTar (cft: CFTrace): Prop :=

  -- given stmt (s) is a call `call expr args`, tar (s) maps to an arity-matching procedure
  (∀ s expr args,
   (s ∈ cft.Q ∧
    stmt cft s = some (Stmt.call expr args) →
    ∃ proc, (cft.tar s = some proc ∧ args.length = proc.params.length)
    ))
  ∧
  -- given stmt (s i) is a `repeat`, tar (s $) = tar (s)
  (∀ s i proc,
   (DynIndex.line s i ∈ cft.Q ∧
    stmt cft (DynIndex.line s i) = some (Stmt.repeat) ∧
    cft.tar s = some proc) →
    cft.tar (s $) = some proc)



def validCFTrace (cft: CFTrace) : Prop :=
    --ε in Q
    ε ∈ cft.Q
  ∧
    -- if s ∈ Q and stmt (s) is a call `call expr args`, then s 0 ∈ Q and tar(s) maps to a arity matching procedure
    ∀ s expr args,
    ((s ∈ cft.Q ∧ stmt cft s = some (Stmt.call expr args)) →

      DynIndex.line s 0 ∈ cft.Q ∧
      ∃ proc, (cft.tar s = some proc ∧ args.length = proc.params.length))
  ∧
    -- if s i ∈ Q and stmt(s i) is an assignment `v[e₀] = e₁`, then s (i+1) ∈ Q
    ∀ s i v e₀ e₁,
    (DynIndex.line s i ∈ cft.Q ∧
     stmt cft (DynIndex.line s i) = some (Stmt.assign v e₀ e₁) →

     DynIndex.line s (i + 1) ∈ cft.Q)

  ∧
    -- if s i ∈ Q and stmt(s i) is a returnIf `if e return ` then either s (i+1) ∈ Q or s # ∈ Q
    ∀ s i e,
    (DynIndex.line s i) ∈ cft.Q ∧
     stmt cft (DynIndex.line s i) = some (Stmt.returnIf e) →

     (DynIndex.line s (i + 1) ∈ cft.Q ∨ s # ∈ cft.Q)

  ∧
    -- if s i ∈ Q and stmt(s i) is `repeat`, then s $ ∈ Q, s $ 0 ∈ Q and tar(s $) = tar(s)
    ∀ s i proc,
    (DynIndex.line s i ∈ cft.Q ∧
     stmt cft (DynIndex.line s i) = some (Stmt.repeat) ∧
     cft.tar s = some proc) →

     (s $ ∈ cft.Q ∧
      DynIndex.line (s $) 0 ∈ cft.Q ∧
      cft.tar (s $) = some proc)
  ∧
    -- if s $ # ∈ Q, then s # ∈ Q
    ∀ s,
    (s $) # ∈ cft.Q → s # ∈ cft.Q

  ∧
    -- if s i # ∈ Q, then s (i + 1) ∈ Q
    ∀ s i,
    (DynIndex.line s i) # ∈ cft.Q → DynIndex.line s (i +1) ∈ cft.Q



end Logic.REPEAT
