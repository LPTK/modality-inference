import ModalityInference.ComparisonWorldClauses
import ModalityInference.ComparisonJointModes

/-! The scalar blocks of a signed world query share one modality strategy.
World selectors and axis selectors occupy separate constant namespaces and
remain available to the joint nominal query. -/
namespace ModalityInference.ComparisonWorldModes

open ComparisonWorldClauses

def worldConstant (i : Nat) : Nat := 4*i+1
def axisConstant (i : Nat) : Nat := 4*i+3

def worldChoice (selectors : Nat → Bool) (i : Nat) : Bool :=
  selectors (worldConstant i)

def scalarBlocks (cs : List WorldClause) : List (Nat × Clause) :=
  cs.zipIdx.flatMap fun (c,i) => ((blocks c).filter (· != 0)).map fun b =>
    (selectorAtom i b,block b c)

def component (side : Nat → Bool) (axis : Bool) (entries : List (Nat × Clause)) : CNF :=
  entries.zipIdx.map fun (entry,i) =>
    [(worldConstant entry.1,false),(axisConstant i,!axis)] ++
      (entry.2.filter fun literal => side literal.1 == axis).map
        (fun literal => (2*literal.1,literal.2))

def prepare (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause) : ModalSynthesis.Prepared :=
  ComparisonJointModes.prepare side flex
    (component side true (scalarBlocks cs)) (component side false (scalarBlocks cs))

def query (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause) : CNF :=
  (choices cs).map (List.map fun literal => (worldConstant literal.1,literal.2)) ++ (prepare side flex cs).query

def witness (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause)
    (selectors : Nat → Bool) : SymbolicModes.Elimination flex :=
  ModalSynthesis.witness side flex (prepare side flex cs) selectors

end ModalityInference.ComparisonWorldModes
