import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.ComparisonJointCheckerTermination

/-! Fuel stability and eventual completion of the public scheme comparison
interface, including its shared type and modality fallback. -/
namespace ModalityInference

open ComparisonPartialPropagation.Fuel

theorem checkSubsumption_settles (source target : Scheme) :
    Settles (fun fuel => checkSubsumption fuel source target) := by
  refine Settles.congr (Settles.recover (g := fun fuel _ => do
    let action ← ComparisonJointChecker.run fuel source target
    pure (jointSubsumptionEvidence source target action))
    (ComparisonChecker.run_settles source.requireDefinedInstances target) ?_) ?_
  · intro _
    exact Settles.bind (ComparisonJointChecker.run_settles source target)
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
