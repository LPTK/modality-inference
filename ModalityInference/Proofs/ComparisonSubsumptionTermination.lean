import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.ComparisonJointCheckerTermination
import ModalityInference.Proofs.ComparisonDeclaredAnchorsTermination
import ModalityInference.Proofs.ComparisonNestedAnchorsTermination
import ModalityInference.Proofs.ComparisonPreparedDriverTermination

/-! Fuel stability and eventual completion of the public scheme comparison
interface, including its shared type and modality fallback. -/
namespace ModalityInference

open ComparisonPartialPropagation.Fuel

theorem comparisonFallback_settles (source target : Scheme) :
    Settles (fun fuel => comparisonFallback fuel source target) := by
  have hprepared (reason : String) : Settles (fun fuel =>
      if residualBounds target.bounds then .rejected reason
      else ComparisonPreparedDriver.run fuel source target) := by
    cases residualBounds target.bounds
    · exact ComparisonPreparedDriver.run_settles source target
    · exact Settles.rejected reason
  refine Settles.congr (Settles.recover (ComparisonJointChecker.run_settles source target)
    (fun _ => Settles.recover (ComparisonDeclaredAnchors.run_settles source target)
      (fun _ => Settles.recover (ComparisonNestedAnchors.run_settles source target)
        hprepared))) ?_
  intro fuel
  unfold comparisonFallback
  cases ComparisonJointChecker.run fuel source target <;> try rfl
  cases ComparisonDeclaredAnchors.run fuel source target <;> try rfl
  cases ComparisonNestedAnchors.run fuel source target <;> rfl

theorem checkSubsumption_settles (source target : Scheme) :
    Settles (fun fuel => checkSubsumption fuel source target) := by
  refine Settles.congr (Settles.recover (g := fun fuel _ => do
    let action ← comparisonFallback fuel source target
    pure (jointSubsumptionEvidence source target action))
    (ComparisonChecker.run_settles source.requireDefinedInstances target) ?_) ?_
  · intro _
    exact Settles.bind (comparisonFallback_settles source target)
      (fun action => Settles.pure (jointSubsumptionEvidence source target action))
  · intro fuel
    unfold checkSubsumption
    cases ComparisonChecker.run fuel source.requireDefinedInstances target <;> rfl

theorem checkSubsumption_terminates (source target : Scheme) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, checkSubsumption fuel source target = result :=
  (checkSubsumption_settles source target).2

theorem checkSubsumption_stable {small large : Nat} {source target : Scheme}
    {result : RunResult SubsumptionEvidence} (h : checkSubsumption small source target = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    checkSubsumption large source target = result :=
  (checkSubsumption_settles source target).1 hle h hr

theorem checkSubsumption_monotone {small large : Nat} {source target : Scheme}
    {result : SubsumptionEvidence} (h : checkSubsumption small source target = .success result)
    (hle : small ≤ large) : checkSubsumption large source target = .success result :=
  checkSubsumption_stable h (by simp) hle

end ModalityInference
