import ModalityInference.ComparisonJointElimination
import ModalityInference.ComparisonSetup
import ModalityInference.ComparisonPreparation
import ModalityInference.SchemeInstance

/-! Ordinary scheme comparison with one shared type and modality solve.
The source carries its body and quantified-image definedness obligations. -/
namespace ModalityInference.ComparisonJointChecker

open ComparisonChecker

def allowedModes (p : SchemePreparation.Prepared) : List ModVar :=
  ((p.assumptions.modeVariables ++ p.sourceBounds.modeVariables ++
    p.sourceType.modeVariables ++ p.targetType.modeVariables).filter
    (fun v => v.index < p.firstMode)).dedup

def restore (s : Setup) (result : ComparisonJointBatchReification.Output) : CompareSubstitution :=
  ComparisonExactContext.finish s.templates.substitution result.substitution

def propagate (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) : RunResult CompareSubstitution := do
  let known ← ComparisonBody.knownTotal fuel (p.assumptions ++ p.sourceBounds.assumptions)
    (ComparisonAnnotations.obligationExpressions p)
  let s : Setup := ⟨p, {}, shapes, known, false⟩
  let reduced ← ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared
  let result ← ComparisonJointElimination.run fuel s.work shapes s.templates (s.reduced reduced)
    (allowedModes p) s.modeIds (6 * p.firstMode)
  return restore s result

def run (fuel : Nat) (source target : Scheme) : RunResult CompareSubstitution := do
  if ¬source.typeParams.Nodup ∨ ¬source.modParams.Nodup then
    return ← .rejected "scheme quantifiers must be distinct"
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let shapes ← ComparisonShapeSolver.prepare fuel p
  match shapes with
  | .infeasibleAssumptions =>
      .rejected "declared shape equations are infeasible; outside residual-target comparison"
  | .solved shapes =>
      let action ← propagate fuel p shapes
      return ComparisonPreparation.reconstruct p action

end ModalityInference.ComparisonJointChecker
