import ModalityInference.Proofs.ComparisonSubsumptionTermination
import ModalityInference.Proofs.ComparisonJointCheckerCompleteness
import ModalityInference.Proofs.Obligations

/-! Completeness of the public scheme comparison interface for defined
comparison witnesses under residual declared bounds. -/
namespace ModalityInference

/-- Every admissible comparison is accepted at every sufficiently large fuel. -/
theorem checkSubsumption_complete {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    ∃ n, ∀ fuel ≥ n, ∃ evidence, checkSubsumption fuel source target = .success evidence := by
  obtain ⟨n, result, hr, hn⟩ :=
    ComparisonChecker.run_terminates source.requireDefinedInstances target
  obtain ⟨m, hm⟩ := ComparisonJointChecker.run_complete ht hm hR h
  refine ⟨max n m, fun fuel hf => ?_⟩
  rw [checkSubsumption, hn fuel ((Nat.le_max_left n m).trans hf)]
  cases result with
  | success evidence => exact ⟨evidence, rfl⟩
  | exhausted => exact False.elim (hr rfl)
  | rejected reason =>
    obtain ⟨action, ha⟩ := hm fuel ((Nat.le_max_right n m).trans hf)
    exact ⟨jointSubsumptionEvidence source target action, by simp [ha, bind, pure, RunResult.bind]⟩

/-- The public implementation satisfies the unchanged scheme-comparison
completeness obligation. -/
theorem scheme_subsumption_complete : Obligations.SchemeSubsumptionComplete := by
  intro source target hsource _ hR h
  exact checkSubsumption_complete hsource.1 hsource.2 hR h

end ModalityInference
