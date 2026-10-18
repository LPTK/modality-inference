import ModalityInference.ComparisonPreparedDriver

/-! Prepared comparison retains the ambient bounds as a separate input.
Fresh source and target namespaces account for every ambient identifier. -/
namespace ModalityInference.ComparisonAmbientDriver

def run (fuel : Nat) (ambient : Bounds) (source target : Scheme) : RunResult CompareSubstitution := do
  if ¬source.typeParams.Nodup ∨ ¬source.modParams.Nodup then
    return ← .rejected "scheme quantifiers must be distinct"
  let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
  let _ ← ComparisonPreparedScalarPreflight.run fuel p
  let shapes ← ComparisonShapeSolver.prepare fuel p
  match shapes with
  | .infeasibleAssumptions =>
      .rejected "declared shapes require whole-edge certification"
  | .solved solved =>
      let result ← ComparisonPreparedDriver.propagate fuel 0 p solved
      return ComparisonPreparation.reconstruct p result

end ModalityInference.ComparisonAmbientDriver
