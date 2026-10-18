import ModalityInference.ComparisonGuardedEndpointQueries
import ModalityInference.ComparisonSignedPreparation
import ModalityInference.ComparisonAnnotations
import ModalityInference.ComparisonGuardedTotal
import ModalityInference.SchemeModeSynthesis

/-! Scalar obligations for prepared structural comparison. Written endpoint
annotations contribute definedness obligations under the original assumptions;
all source modality parameters share one finite synthesized action. -/
namespace ModalityInference.ComparisonPreparedScalar

/-- Every written endpoint annotation is checked, including annotations inside
whole declared bounds and inside either side of source constraints. -/
def annotations (p : SchemePreparation.Prepared) : List ModExpr :=
  (ComparisonSignedObservation.endpoints p).flatMap fun pair =>
    ComparisonAnnotations.expressions pair.1 ++ ComparisonAnnotations.expressions pair.2

def required (p : SchemePreparation.Prepared) : Bounds :=
  ComparisonGuardedTotal.scalarBounds p.sourceBounds ++ (annotations p).map Constraint.defined

/-- The scalar source is always active and uses one scalar world. -/
def source (theory goals : CNF) : ComparisonGuardedEndpointQueries.Source where
  guard := []
  source := {
    decode := fun v => (1,v)
    theory := theory
    clauses := goals.map fun guard => ⟨guard,[]⟩ }

def run (fuel : Nat) (p : SchemePreparation.Prepared) :
    RunResult ComparisonGuardedEndpointQueries.Source := do
  let theory ← CompactCNF.toCNF fuel true (boundsModeFormula p.assumptions)
  let goals ← CompactCNF.toCNF fuel true (boundsModeFormula (required p))
  return source theory goals

def modeIds (p : SchemePreparation.Prepared) : List Nat :=
  List.range' p.firstMode (p.nextMode-p.firstMode)

def modeParameters (p : SchemePreparation.Prepared) : List (Nat × ModVar) :=
  SchemeModeSynthesis.parameters (modeIds p)

def flexibleAtoms (p : SchemePreparation.Prepared) : List Nat :=
  SchemeModeSynthesis.atoms (modeIds p)

def assemble (p : SchemePreparation.Prepared) (images : SymbolicModes.Elimination (flexibleAtoms p)) :
    Option Substitution :=
  SymbolicSchemeModes.assemble images (modeParameters p)

end ModalityInference.ComparisonPreparedScalar
