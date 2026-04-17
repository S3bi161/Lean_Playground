import Logic.DL.Syntax
import Mathlib.Logic.Relation
namespace Logic.DL

-- simple Kripke style structure, with natural numbers as states
structure KripkeModel where
  val : String → Nat → Prop --valuation function "does atomic prop hold in state?"
  rel : Nat → Nat → Nat → Prop --transition function "atomic relation → state transition holds?"

-- inductive relation evaluation over model
def evalRel (M: KripkeModel) : Relation → Nat → Nat → Prop
  | Relation.relAtom a, s₀, s₁ => M.rel a s₀ s₁ --atomic defined by model.rel
  | Relation.anywhere, _, _ => True --neglect reachability
  | Relation.wild, s₀, s₁ => ∃ n, M.rel n s₀ s₁ --no notion of reachability in current implementation!
  | Relation.comp α β, s₀, s₁ => ∃ s₂, evalRel M α s₀ s₂ ∧ evalRel M β s₂ s₁
  | Relation.alt α β, s₀, s₁ => evalRel M α s₀ s₁ ∨ evalRel M β s₀ s₁
  | Relation.iter α, s₀, s₁ => Relation.ReflTransGen (evalRel M α) s₀ s₁ --need transitive closure over α

--inductive formula evaluation over model
def eval (M: KripkeModel) : DLForm → Nat → Prop
  | DLForm.atom a, s => M.val a s
  | DLForm.falsum, _ => False
  | DLForm.imp φ ψ, s => eval M φ s → eval M ψ s
  | DLForm.diamond α φ, s => ∃ s', evalRel M α s s' ∧ eval M φ s'


def equiv (φ ψ: DLForm): Prop :=
  ∀ (model: KripkeModel) (state: Nat), eval model φ state ↔ eval model ψ state

end Logic.DL
