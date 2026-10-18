import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.ComparisonResidualBounds
import ModalityInference.Proofs.ComparisonJointCheckerCompleteness
import ModalityInference.Proofs.ComparisonJointCheckerTermination
import ModalityInference.Proofs.ComparisonPreparedDriver

/-! A successful public comparison retains an existing certificate or returns
an admissible substitution from a subsequent certified phase. -/
namespace ModalityInference

theorem checkSubsumption_success_cases {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    ComparisonChecker.run fuel source.requireDefinedInstances target = .success evidence ∨
      ∃ action, comparisonFallback fuel source target = .success action ∧
        evidence = jointSubsumptionEvidence source target action := by
  cases hc : ComparisonChecker.run fuel source.requireDefinedInstances target <;>
    simp only [checkSubsumption, hc] at h
  case success result => cases h; exact .inl rfl
  case exhausted => contradiction
  case rejected reason =>
    cases hj : comparisonFallback fuel source target <;>
      simp only [hj, bind, pure, RunResult.bind] at h <;> try contradiction
    next action => cases h; exact .inr ⟨action, rfl, rfl⟩

theorem checkSubsumption_of_certificate {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : ComparisonChecker.run fuel source.requireDefinedInstances target = .success evidence) :
    checkSubsumption fuel source target = .success evidence := by
  simp only [checkSubsumption, h]

private theorem rejected_not_subsumes {fuel : Nat} {source target : Scheme} {reason : String}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds)
    (hr : ComparisonJointChecker.run fuel source target = .rejected reason) :
    ¬ AlgebraSubsumesUnder [] source target := by
  intro h
  obtain ⟨n, hn⟩ := ComparisonJointChecker.run_complete ht hm hR h
  obtain ⟨result, hs⟩ := hn (max fuel n) (Nat.le_max_right _ _)
  have hr' := ComparisonJointChecker.run_stable hr (by simp) (Nat.le_max_left fuel n)
  rw [hs] at hr'
  cases hr'

private theorem prepared_quantifiers_nodup {fuel : Nat} {source target : Scheme}
    {action : CompareSubstitution}
    (h : ComparisonPreparedDriver.run fuel source target = .success action) :
    source.typeParams.Nodup ∧ source.modParams.Nodup := by
  unfold ComparisonPreparedDriver.run at h
  split at h
  · cases h
  · simpa only [not_or, not_not] using ‹¬(¬source.typeParams.Nodup ∨ ¬source.modParams.Nodup)›

/-- A successful prepared structural comparison is retained unless a preceding
phase still requires more fuel. Any earlier completed success is also retained. -/
theorem checkSubsumption_of_prepared_result {fuel : Nat} {source target : Scheme}
    {action : CompareSubstitution}
    (hp : ComparisonPreparedDriver.run fuel source target = .success action)
    (hd : checkSubsumption fuel source target ≠ .exhausted) :
    ∃ evidence, checkSubsumption fuel source target = .success evidence := by
  cases hc : ComparisonChecker.run fuel source.requireDefinedInstances target with
  | success evidence => exact ⟨evidence, by simp [checkSubsumption, hc]⟩
  | exhausted => exact False.elim (hd (by simp [checkSubsumption, hc]))
  | rejected reason =>
      cases hj : ComparisonJointChecker.run fuel source target with
      | success result => exact ⟨jointSubsumptionEvidence source target result,
          by simp [checkSubsumption, hc, comparisonFallback, hj, bind, pure, RunResult.bind]⟩
      | exhausted => exact False.elim (hd
          (by simp [checkSubsumption, hc, comparisonFallback, hj, bind, RunResult.bind]))
      | rejected reason =>
          have hres : residualBounds target.bounds = false := by
            cases hr : residualBounds target.bounds with
            | false => rfl
            | true =>
                obtain ⟨ht, hm⟩ := prepared_quantifiers_nodup hp
                exact False.elim ((rejected_not_subsumes ht hm (residualBounds_sound hr) hj)
                  (ComparisonPreparedDriver.run_algebra_subsumesUnder hp))
          cases ha : ComparisonDeclaredAnchors.run fuel source target with
          | success result => exact ⟨jointSubsumptionEvidence source target result,
              by simp [checkSubsumption, hc, comparisonFallback, hj, ha, bind, pure, RunResult.bind]⟩
          | exhausted => exact False.elim (hd
              (by simp [checkSubsumption, hc, comparisonFallback, hj, ha, bind, RunResult.bind]))
          | rejected reason =>
              cases hn : ComparisonNestedAnchors.run fuel source target with
              | success result => exact ⟨jointSubsumptionEvidence source target result,
                  by simp [checkSubsumption, hc, comparisonFallback, hj, ha, hn,
                    bind, pure, RunResult.bind]⟩
              | exhausted => exact False.elim (hd
                  (by simp [checkSubsumption, hc, comparisonFallback, hj, ha, hn, bind, RunResult.bind]))
              | rejected reason => exact ⟨jointSubsumptionEvidence source target action,
                  by simp [checkSubsumption, hc, comparisonFallback, hj, ha, hn, hres, hp,
                    bind, pure, RunResult.bind]⟩

end ModalityInference
