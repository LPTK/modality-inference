import ModalityInference.ComparisonSignedPoints
import ModalityInference.ComparisonWorldModes

/-! A signed endpoint query uses independent nominal points with guarded basis
equalities, then separates world choices before one shared scalar solve. -/
namespace ModalityInference.ComparisonSignedStrategySynthesis

open ComparisonSignedEndpoints

def worlds (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) : List ComparisonWorldClauses.WorldClause :=
  ComparisonSignedWorlds.query (ComparisonSignedPoints.decode decode)
    (ComparisonSignedPoints.theory (ComparisonSignedWorlds.calls clauses) size theory)
    (clauses.map ComparisonSignedPoints.clause)

def scalarQuery (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat)
    (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause) : CNF :=
  ComparisonWorldModes.query side flex (worlds size decode theory clauses)

def nominalQuery (size : Nat → Nat) (decode : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) : CNF :=
  ComparisonWorldClauses.nominal (worlds size decode theory clauses)

def modes (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat)
    (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (selectors : Nat → Bool) : SymbolicModes.Elimination flex :=
  ComparisonWorldModes.witness side flex (worlds size decode theory clauses) selectors

end ModalityInference.ComparisonSignedStrategySynthesis
