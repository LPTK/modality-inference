import ModalityInference.ComparisonSignedNominal
import ModalityInference.ComparisonSignedEdges
import ModalityInference.ComparisonWorldOffsets

/-! Each endpoint query retains its own nominal point namespace while its
constant world selectors use a shared clause-index range. -/
namespace ModalityInference.ComparisonSignedNominalEdges
open ComparisonSignedEndpoints

def prepare (offset : Nat) (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) : Option (List CompiledClause) :=
  ComparisonSignedNominal.parse
    (ComparisonSignedWorlds.calls (clauses.map ComparisonSignedPoints.clause))
    (ComparisonWorldOffsets.nominal offset
      (ComparisonSignedStrategySynthesis.worlds size decode theory clauses))

def run (offset width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause) : Option CNF := do
  let parsed ← prepare offset size decode theory clauses
  ComparisonSignedEdges.compileWith
    (ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls clauses))
    width key size ComparisonSignedNominal.guardDecode [] parsed

end ModalityInference.ComparisonSignedNominalEdges
