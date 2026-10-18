import ModalityInference.ComparisonSignedNominalEdges
import ModalityInference.ComparisonSignedQuerySolver

/-! Endpoint queries keep local observer namespaces. Their world-clause ranges
index global selectors, and all scalar blocks enter one shared modality solve. -/
namespace ModalityInference.ComparisonSignedEndpointQueries
open ComparisonSignedEndpoints ComparisonSignedSynthesis ComparisonSignedQueries

structure Source where
  decode : Nat → Nat × Nat
  theory : CNF
  clauses : List CompiledClause

def Source.worlds (source : Source) (size : Nat → Nat) : List ComparisonWorldClauses.WorldClause :=
  ComparisonSignedStrategySynthesis.worlds size source.decode source.theory source.clauses

def Source.nominal (source : Source) (offset : Nat) (size : Nat → Nat) : Option Query := do
  let clauses ← ComparisonSignedNominalEdges.prepare offset size source.decode source.theory source.clauses
  return {
    payload := ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls source.clauses)
    decode := ComparisonSignedNominal.guardDecode
    theory := []
    clauses := clauses }

def prepare (size : Nat → Nat) : Nat → List Source → Option (List Query)
  | _,[] => some []
  | offset,source::sources => do
      let head ← source.nominal offset size
      let tail ← prepare size (offset+(source.worlds size).length) sources
      return head::tail

def worlds (size : Nat → Nat) (sources : List Source) : List ComparisonWorldClauses.WorldClause :=
  sources.flatMap fun source=>source.worlds size

def scalarQuery (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat) (sources : List Source) : CNF :=
  ComparisonWorldModes.query side flex (worlds size sources)

def modes (side : Nat → Bool) (flex : List Nat) (input : Input) (sources : List Source)
    (selectors : Nat → Bool) :=
  ComparisonWorldModes.witness side flex (worlds (fun n=>(input.bases n).length) sources) selectors

def run (fuel : Nat) (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) : RunResult ComparisonSignedQuerySolver.Solution :=
  match prepare (fun n=>(input.bases n).length) 0 sources with
  | none => .rejected "endpoint nominal parsing failed"
  | some queries => ComparisonSignedQuerySolver.run fuel input queries
      (scalarQuery side flex (fun n=>(input.bases n).length) sources)

end ModalityInference.ComparisonSignedEndpointQueries
