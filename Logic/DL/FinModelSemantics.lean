import Logic.DL.Semantics
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace Logic.DL


--helpers to extract states and relations directly
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

/-
Boolean evaluation logic for finite models
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
  | Relation.iter α, s₀, s₁ => decide (s₀ = s₁) --reflexive only → TODO: implement transitive!

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


--wrapper to evaluate directly over model defining rel/val in list notation
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
