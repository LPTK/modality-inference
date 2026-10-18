import ModalityInference.ComparisonWorldClauses

/-! Clause-index offsets give independent endpoint queries disjoint constant
selectors. Scalar coordinates retain their common names for a single solve. -/
namespace ModalityInference.ComparisonWorldOffsets
open ComparisonWorldClauses

def nominal (offset : Nat) (cs : List WorldClause) : CNF :=
  cs.zipIdx.map fun (c,i) => selected (offset+i) 0 c

def scalar (offset : Nat) (cs : List WorldClause) : CNF :=
  cs.zipIdx.flatMap fun (c,i) => ((blocks c).filter (· != 0)).map fun b =>
    selected (offset+i) b c

def choices (offset : Nat) (cs : List WorldClause) : CNF :=
  cs.zipIdx.map fun (c,i) => (blocks c).map fun b => (selectorAtom (offset+i) b,true)

end ModalityInference.ComparisonWorldOffsets
