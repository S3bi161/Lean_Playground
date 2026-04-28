import Logic.Prop.Syntax
import Logic.Prop.Semantics
import Logic.DL.Syntax
import Logic.DL.Semantics
import Logic.DL.Notation
import Logic.DL.FinModelSemantics

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


namespace Logic.DL

abbrev State := List DynamicIndices --use List of dynamic indices where [0, 1] corresponds to 0.1


def val: List (Atoms × State) :=
  [ ("q", []),
    ("p", [0]),
    ("q", [0, 1]),
    ("p", [0, 1])] -- "in state 0.1 p holds"

def rel: List (DynamicIndices × State × State) :=
  [ (0, [], [0]), -- [] --0--> [0]
    (1, [0], [0, 1]), -- [0] --1--> [0, 1]/0.1
    (#, [0, 1], [0, 1, #])]

def M₁: KripkeModel DynamicIndices Atoms State :=
  mkModel val rel


def relH := relDecidable rel
def valH := valDecidable val

def states := statesFromList rel
def rels := relsFromList rel


#check M₁
#check ⟨0⟩ "p"
#eval evalB M₁ relH valH states rels (⟨0⟩ "p") []
#eval evalB M₁ relH valH states rels ("p") []

#eval evalFromList val rel (⟨0⟩ "p") []
#eval evalFromList val rel (⟨0 ∪ 1⟩("p" ∧ "q")) []
#eval evalFromList val rel (⟨0 ∪ 1⟩("p" ∧ "q")) [0]
#eval evalFromList val rel ((⟨Relation.comp 0 (Relation.comp 1 •)⟩¬⊥)) []

def val': List (Atoms × State) :=
  [ ("p", [0]),
    ("q", [1])
  ]
def rel': List (DynamicIndices × State × State) :=
  [ (0, [], [0]),
    (0, [], [1]) --branching
  ]

#eval evalFromList val' rel' (⟨0 ∪ 1⟩"p") []
#eval evalFromList val' rel' (⟨•⟩ "p") []
#eval evalFromList val' rel' ([•] "q") []
#eval evalFromList val' rel' ((⟨0⟩ "p") ∧ (⟨0⟩ ¬ "p")) [] --true due to branching model
#eval evalFromList val' rel' (⟨•⟩ "q") []
#eval evalFromList val' rel' (⟨0⟩ "p" ∧ "q") []
#eval evalFromList val' rel' (⟨0⟩ ¬("p" ∨ "q")) []

end Logic.DL
