import ModalityInference.Proofs.ComparisonSubsumption
import ModalityInference.Proofs.ComparisonPropagationSoundness
import ModalityInference.Proofs.ComparisonJointCheckerSoundness
import ModalityInference.Proofs.ComparisonDefinedInstances

/-! The actual substitution returned by successful public comparison has defined
images and a defined source body under the unchanged declared assumptions. -/
namespace ModalityInference

private theorem certificate_result {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : ComparisonChecker.run fuel source.requireDefinedInstances target = .success evidence) :
    let p := SchemePreparation.prepare [] source target
    CompareInstantiatesUnder p.assumptions source evidence.substitution ∧
      evidence.substitution.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (evidence.substitution.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (evidence.substitution.ty source.body) (.ofTy p.targetType) := by
  have hs := ComparisonChecker.PreparedSolution.result
    (ambient := []) (source := source.requireDefinedInstances) (target := target)
    (ComparisonChecker.run_solution h)
  have hi : CompareInstantiates source evidence.substitution :=
    ComparisonChecker.run_instantiates (source := source.requireDefinedInstances) h
  have hb : AlgebraEntailsAll (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions
      (evidence.substitution.bounds source.bounds) ∧
      AlgebraEntailsAll (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions
        (evidence.substitution.bounds source.instanceGuards) := by
    simpa only [Scheme.requireDefinedInstances, CompareSubstitution.bounds,
      List.map_append, AlgebraEntailsAll, List.mem_append, or_imp, forall_and] using hs.2.1
  obtain ⟨hw, hd⟩ := (CompareSubstitution.instance_guards_iff hi hs.1).mp hb.2
  have ha : (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions =
      (SchemePreparation.prepare [] source target).assumptions := by
    simp only [SchemePreparation.prepare_assumptions, Scheme.requireDefinedInstances_subsumptionIndices]
  have ht : (SchemePreparation.prepare [] source.requireDefinedInstances target).targetType =
      (SchemePreparation.prepare [] source target).targetType := by
    simp only [SchemePreparation.prepare, Scheme.requireDefinedInstances_subsumptionIndices]
  exact ⟨⟨hi, ha ▸ hw, ha ▸ hd⟩, ha ▸ hs.1, ha ▸ hb.1, by simpa only [ha, ht] using hs.2.2⟩

/-- Both public comparison paths certify their actual returned substitution,
including original source bounds and every instance-definedness obligation. -/
theorem checkSubsumption_evidence_result {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    let p := SchemePreparation.prepare [] source target
    CompareInstantiatesUnder p.assumptions source evidence.substitution ∧
      evidence.substitution.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (evidence.substitution.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (evidence.substitution.ty source.body) (.ofTy p.targetType) := by
  rcases checkSubsumption_success_cases h with hc | ⟨action, hj, rfl⟩
  · exact certificate_result hc
  · exact ComparisonJointChecker.run_result hj

theorem checkSubsumption_evidence_instantiatesUnder {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    CompareInstantiatesUnder (SchemePreparation.prepare [] source target).assumptions
      source evidence.substitution :=
  (checkSubsumption_evidence_result h).1

theorem checkSubsumption_evidence_defined {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    let declared := (SchemePreparation.prepare [] source target).assumptions
    evidence.substitution.WellFormedUnder declared ∧
      (evidence.substitution.ty source.body).DefinedUnder declared :=
  let hi := checkSubsumption_evidence_instantiatesUnder h
  ⟨hi.images, hi.body⟩

theorem checkSubsumption_query_valid {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    ∀ world, evidence.query.eval world = true := by
  rcases checkSubsumption_success_cases h with hc | ⟨action, _, rfl⟩
  · exact ComparisonChecker.run_query_valid hc
  · intro world
    rfl

end ModalityInference
