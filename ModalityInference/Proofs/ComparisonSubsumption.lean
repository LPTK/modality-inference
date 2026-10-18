import ModalityInference.SchemeSubsumption

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

end ModalityInference
