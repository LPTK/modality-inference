import ModalityInference.ComparisonPreparedQueries
import ModalityInference.ComparisonPreparedScalar
import ModalityInference.ComparisonPreparedScalarPreflight
import ModalityInference.ComparisonPreparation
import ModalityInference.SchemeInstance

/-! Prepared structural comparison uses one guarded solve for the selected
endpoint layouts and every scalar obligation, then returns its finite images. -/
namespace ModalityInference.ComparisonPreparedDriver

def propagate (fuel first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : RunResult CompareSubstitution := do
  let program ← ComparisonPreparedQueries.compile fuel first p solved
  let scalar ← ComparisonPreparedScalar.run fuel p
  let input := ComparisonSignedBranchImages.input (ComparisonSignedBranchImages.entries first p solved)
  let sources := program.sources++[scalar]
  let result ← ComparisonGuardedEndpointQueries.run fuel input ModalSynthesis.locality
    (ComparisonPreparedScalar.flexibleAtoms p) sources program.condition
  let selectors := CNFPropagation.valuation result.selectors
  let modes := ComparisonGuardedEndpointQueries.modes ModalSynthesis.locality
    (ComparisonPreparedScalar.flexibleAtoms p) input sources selectors
  match ComparisonPreparedScalar.assemble p modes with
  | none => .rejected "shared modality image assembly failed"
  | some action =>
      match ComparisonSignedBranchImages.select first p solved
        (ComparisonGuardedEndpointQueries.shapeValue (fun n=>(input.bases n).length) sources selectors)
        result.images action.modes with
      | none => .rejected "selected structural image assembly failed"
      | some result => .success result

def run (fuel : Nat) (source target : Scheme) : RunResult CompareSubstitution := do
  if ¬source.typeParams.Nodup ∨ ¬source.modParams.Nodup then
    return ← .rejected "scheme quantifiers must be distinct"
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let _ ← ComparisonPreparedScalarPreflight.run fuel p
  let shapes ← ComparisonShapeSolver.prepare fuel p
  match shapes with
  | .infeasibleAssumptions =>
      .rejected "declared shapes require whole-edge certification"
  | .solved solved =>
      let result ← propagate fuel 0 p solved
      return ComparisonPreparation.reconstruct p result

end ModalityInference.ComparisonPreparedDriver
