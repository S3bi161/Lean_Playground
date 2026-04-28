import Logic.DL.Syntax
import Mathlib.Logic.Relation
namespace Logic.DL

structure KripkeModel (RelType AtomType State: Type) where
  val : AtomType → State → Prop --valuation function "does atomic prop hold in state?"
  rel : RelType → State → State → Prop --transition function "atomic relation → state transition holds?"

-- inductive relation evaluation over model
def evalRel (M: KripkeModel RelType AtomType State):
  Relation RelType → State → State → Prop
  | Relation.relAtom a, s₀, s₁ => M.rel a s₀ s₁ --atomic defined by model.rel
  | Relation.emptyset, _, _ =>  False -- no transitions to another state at all
  | Relation.wild, s₀, s₁ => ∃ a, M.rel a s₀ s₁
  | Relation.comp α β, s₀, s₁ => ∃ s₂, evalRel M α s₀ s₂ ∧ evalRel M β s₂ s₁
  | Relation.alt α β, s₀, s₁ => evalRel M α s₀ s₁ ∨ evalRel M β s₀ s₁
  | Relation.iter α, s₀, s₁ => Relation.ReflTransGen (evalRel M α) s₀ s₁

--inductive formula evaluation over model
def eval (M: KripkeModel RelType AtomType State) :
  DLForm RelType AtomType → State → Prop
  | DLForm.atom a, s => M.val a s
  | DLForm.falsum, _ => False
  | DLForm.imp φ ψ, s => eval M φ s → eval M ψ s
  | DLForm.diamond α φ, s => ∃ s', evalRel M α s s' ∧ eval M φ s'


def equiv {RelType AtomType State: Type} (φ ψ: DLForm RelType AtomType): Prop :=
  ∀ (model: KripkeModel RelType AtomType State) (state: State), eval model φ state ↔ eval model ψ state

def nonBranching (model: KripkeModel RelType AtomType State): Prop :=
  ∀ (relAtom: RelType) (s₀ s₁ s₂: State), (model.rel relAtom s₀ s₁ ∧ model.rel relAtom s₀ s₂) → s₁ = s₂

def validPDL {RelType AtomType State: Type} (φ: DLForm RelType AtomType): Prop :=
  ∀ (model: KripkeModel RelType AtomType State) (s: State), eval model φ s

def validDPDL {RelType AtomType State: Type} (φ: DLForm RelType AtomType): Prop :=
  ∀ (model: KripkeModel RelType AtomType State) (s: State), nonBranching model → eval model φ s


theorem validPDL_imp_validDPDL {RelType AtomType State: Type} (φ: DLForm RelType AtomType):
  @validPDL RelType AtomType State φ → @validDPDL RelType AtomType State φ :=
  by
    intro validPDLH --assume pdl validity hypothesis
    intro M s -- fix model, state
    intro nBH -- assume nonBranching M
    exact validPDLH M s -- apply hypothesis

end Logic.DL
