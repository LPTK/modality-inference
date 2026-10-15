import ModalityInference.ComparisonJointEncoding

/-! Separate each coordinate clause into its permitted scalar component and
an opposite-component scalar guard. One shared constant selects the side that
must hold uniformly; constants occupy odd atoms and inputs occupy even atoms. -/
namespace ModalityInference.ComparisonJointAxes

/-- State and head observations belong to the coordinate's own component. -/
def own (side : Nat → Bool) (component : Bool) (count heads v : Nat) : Bool :=
  decide (v < count + heads) || (side (v - (count + heads)) == component)

def ownPart (side : Nat → Bool) (component : Bool) (count heads : Nat) (clause : Clause) : Clause :=
  clause.filter fun literal => own side component count heads literal.1

def otherPart (side : Nat → Bool) (component : Bool) (count heads : Nat) (clause : Clause) : Clause :=
  (clause.filter fun literal => !own side component count heads literal.1).map
    fun literal => (literal.1 - (count + heads), literal.2)

def ownClauses (side : Nat → Bool) (component : Bool) (count heads : Nat) (clauses : CNF) : CNF :=
  clauses.zipIdx.map fun (clause, index) =>
    (2 * index + 1, false) :: (ownPart side component count heads clause).map
      (fun literal => (2 * literal.1, literal.2))

def otherClauses (side : Nat → Bool) (component : Bool) (count heads : Nat) (clauses : CNF) : CNF :=
  clauses.zipIdx.map fun (clause, index) =>
    (2 * index + 1, true) :: (otherPart side component count heads clause).map
      (fun literal => (2 * literal.1, literal.2))

def encode (choice inputs : Nat → Bool) (i : Nat) : Bool :=
  if i % 2 == 0 then inputs (i / 2) else choice (i / 2)

end ModalityInference.ComparisonJointAxes
