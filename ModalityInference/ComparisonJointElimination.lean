import ModalityInference.ComparisonJointBatchReification

/-! Shared type and modality elimination for structurally reduced comparison
obligations. Every group uses the same permitted scalar inputs and modality
substitution. The scalar implication is retained when there are no groups. -/
namespace ModalityInference.ComparisonJointElimination

def run (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) (allowed : List ModVar) (modeIds : List Nat)
    (minimumModes : Nat := 0) : RunResult ComparisonJointBatchReification.Output := do
  let groups ← ComparisonGroups.collect p shapes templates reduced
  let compiled ← ComparisonJointBatchReification.prepare fuel p.assumptions reduced.modes groups
  let scalar ← CompactCNF.toCNF fuel true
    (.imp (boundsModeFormula p.assumptions) (boundsModeFormula reduced.modes))
  let batch ← ComparisonJointBatch.run fuel ModalSynthesis.locality
    (SchemeModeSynthesis.atoms modeIds) (ComparisonJointBatchReification.entries compiled)
    minimumModes scalar
  match ComparisonJointBatchReification.assemble allowed modeIds compiled batch minimumModes with
  | some result => .success result
  | none => .rejected "comparison coordinates do not reify to a finite substitution"

end ModalityInference.ComparisonJointElimination
