import ModalityInference.ComparisonSignedSynthesis
import ModalityInference.ComparisonSignedEdges

/-! Each query retains its own observer coordinates. Compiling their relations
before synthesis keeps image keys and constant parameters common to them all. -/
namespace ModalityInference.ComparisonSignedQueries
open ComparisonPropagation ComparisonSignedEndpoints ComparisonSignedSynthesis

structure Query where
  payload : Call → Nat → Nat
  decode : Nat → Sum Nat Nat
  theory : CNF
  clauses : List CompiledClause

def Query.compile (query : Query) (input : Input) : Option CNF :=
  ComparisonSignedEdges.compileWith query.payload input.width input.key
    (fun name=>(input.bases name).length) query.decode query.theory query.clauses

def compile (input : Input) : List Query → Option CNF
  | [] => some [[]]
  | query::queries => do
      let head ← query.compile input
      let tail ← compile input queries
      return join head tail

end ModalityInference.ComparisonSignedQueries
