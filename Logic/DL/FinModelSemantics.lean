import Logic.DL.Semantics

namespace Logic.DL


--helpers to extract states and relations directly from transition list
def relsFromList
  {RelType State: Type}
  [BEq RelType]
  (rels : List (RelType × State × State)):
  List RelType := (rels.map (λ (r, _, _) ↦ r)).eraseDups

def statesFromList
  {RelType State: Type}
  [BEq State]
  (rels: List (RelType × State × State)):
  List State := (rels.map (λ (_, s₀, s₁) ↦ [s₀, s₁])).flatten.eraseDups

--helpers to generate kripke model from lists
def valFromList
  {AtomType State: Type}
  [DecidableEq AtomType][DecidableEq State]
  (vals: List (AtomType × State)):
  AtomType → State → Prop :=
    λ atom state ↦ (atom, state) ∈ vals

def relFromList
  {RelType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (rels: List (RelType × State × State)):
  RelType → State → State → Prop :=
    λ relAtom s₁ s₂ ↦ (relAtom, s₁, s₂) ∈ rels

/-- Constructs a kripke model `M` from explicit valuation and relation lists:
* `valList: List (AtomType × State)` specifies `M.val` where a tuple `(a, s)` defines `a` holds at `s`

• `relList: List (RelType × State × State)` specifies `M.rel` where a triple `(r, s, s')` defines a transition s --r--> s'
-/
def mkModel
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq AtomType] [DecidableEq State]
  (valList: List (AtomType × State))
  (relList: List (RelType × State × State)):
  KripkeModel RelType AtomType State where
    rel := relFromList relList
    val := valFromList valList


-- Decidable instances required for computation
def valDecidable
  {AtomType State: Type}
  [DecidableEq AtomType] [DecidableEq State]
  (xs: List (AtomType × State)):
  ∀ atom state, Decidable ((valFromList xs) atom state) :=
  by
    intro atomType stateType
    simp[valFromList]
    infer_instance

def relDecidable
  {RelType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (xs: List (RelType × State × State)):
  ∀ rel s s', Decidable ((relFromList xs) rel s s') :=
  by
    intro rel s s'
    simp[relFromList]
    infer_instance


mutual --mutual block needed since successorStates, relBFS and evalRelB depend on each other

-- helper to get states reachable via one α step
def successorStates
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (states: List State) (rels: List RelType)
  (α: Relation RelType) (s: State): List State :=
    states.filter (λ s' ↦ evalRelB M relDecidableH states rels α s s')

def relBFS
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (states: List State) (rels: List RelType)
  (α: Relation RelType)
  (maxSteps: Nat) (fringe visited: List State) (target: State): Bool :=
    if target ∈ fringe then Bool.true
    else
      match maxSteps with
        | 0 => false
        | maxSteps' + 1 =>
          let next := fringe
                        |>.map (λ s ↦ (successorStates M relDecidableH states rels α s))
                        |>.flatten
                        |>.eraseDups
                        |>.filter (λ s ↦ !(s ∈ visited))
          relBFS M relDecidableH states rels α maxSteps' next (visited ++ next) target
/-
# Boolean evaluation logic for finite models
-/


/-- Boolean evaluation of a relation `α` between states `s₀` and `s₁` in a finite kripke model `M`

`evalRelB` is computational, i.e. it evaluates relation semantics to `Bool` using decidability of `M.rel` supplied via `relDecidableH` argument.
This Decidable instance can ge generated using `Logic.DL.relDecidable`.
The evaluation is inductively extended to non-atomic relations.

Explicit lists `List State` and `List RelType` containing states and atomic relations have to be provided.
`evalRelB` is intended for computation over a finite model rather than reasoning. For general reasoning, use `Logic.DL.evalRel` instead.
### Returns
`Bool.true` iff `α` is a transition between `s₀` and `s₁` in `M`, `Bool.false` otherwise.
-/
def evalRelB
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (states: List State) (rels: List RelType):
  Relation RelType → State → State → Bool

  | Relation.relAtom a, s₀, s₁ => @decide (M.rel a s₀ s₁) (relDecidableH a s₀ s₁)
  | Relation.emptyset, _, _ => false
  | Relation.wild, s₀, s₁ => rels.any (λ r ↦ @decide (M.rel r s₀ s₁) (relDecidableH r s₀ s₁))
  | Relation.comp α β, s₀, s₁ => states.any (λ s₂ ↦
                                                  evalRelB M relDecidableH states rels α s₀ s₂ &&
                                                  evalRelB M relDecidableH states rels β s₂ s₁)
  | Relation.alt α β, s₀, s₁ => evalRelB M relDecidableH states rels α s₀ s₁ ||
                                evalRelB M relDecidableH states rels β s₀ s₁
  | Relation.iter α, s₀, s₁ => relBFS M relDecidableH states rels α states.length [s₀] [s₀] s₁

end --end mutual block


/-- Boolean evaluation of a formula `φ` at a state `s` in a finite kripke model `M`

`evalB` is computional, i.e. it evaluates propositions of `AtomType` to `Bool` using decidability of `M.rel`, `M.val` supplied via `relDecidableH`, `valDecidableH` args.
These Decidable instances can be generated using `Logic.DL.relDecidable` and `Logic.DL.valDecidable`.
The evaluation is inductively extended to non-atomic formulas.

Explicit lists `List State` and `List RelType` containing states and atomic relations have to be provided.
`evalB` is intended for computation over a finite model rather than reasoning. For general reasoning, use `Logic.DL.eval` instead.
### Returns
`Bool.true` iff M, s ⊧ φ, `Bool.false` otherwise.
-/
def evalB
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq State]
  (M: KripkeModel RelType AtomType State)
  (relDecidableH: ∀ rel s s', Decidable (M.rel rel s s'))
  (valDecidableH: ∀ atom s, Decidable (M.val atom s))
  (states: List State) (rels: List RelType):
  DLForm RelType AtomType → State → Bool

  | DLForm.atom a, s => @decide (M.val a s) (valDecidableH a s)
  | DLForm.falsum, _ => false
  | DLForm.imp φ ψ, s => (! evalB M relDecidableH valDecidableH states rels φ s) ||
                         (evalB M relDecidableH valDecidableH states rels ψ s)
  | DLForm.diamond α φ, s => states.any (λ s' ↦
                                              evalRelB M relDecidableH states rels α s s' &&
                                              evalB M relDecidableH valDecidableH states rels φ s')

/-- Wrapper to evaluate a formula `φ` at state `s` in a finite kripke model `M` constructed from explicit valuation and relations list.

The modle `M` is not given directly, but inferred from:
* `vals: List (AtomType × State)` specifies which atomic propositions hold in specific states
* `rels: List (RelType × State × State)` specifies atomic state transitions

States and atomic relations are inferred from these lists and the resulting model is passed to `evalB`

### Returns
`Bool.true` iff M, s ⊧ φ, `Bool.false` otherwise
-/
def evalFromList
  {RelType AtomType State: Type}
  [DecidableEq RelType] [DecidableEq AtomType] [DecidableEq State]
  [BEq RelType]
  (vals: List (AtomType × State))
  (rels: List (RelType × State × State))
  (φ: DLForm RelType AtomType)
  (s: State): Bool :=
    let M := mkModel vals rels

    --generate Decidable instances
    let relH := relDecidable rels
    let valH := valDecidable vals

    --extract states/atomic relations in the model
    let states := statesFromList rels
    let atomicRels := relsFromList rels

    evalB M relH valH states atomicRels φ s

end Logic.DL
