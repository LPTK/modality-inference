import ModalityInference.Proofs.ComparisonCheckerTermination
import ModalityInference.Proofs.ComparisonPropagationSoundness
import ModalityInference.Proofs.ComparisonDefinedInstances

/-! The actual substitution returned by successful public comparison has defined
images and a defined source body under the unchanged declared assumptions. -/
namespace ModalityInference

theorem checkSubsumption_evidence_instantiatesUnder {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    CompareInstantiatesUnder (SchemePreparation.prepare [] source target).assumptions
      source evidence.substitution := by
  have hr : ComparisonChecker.run fuel source.requireDefinedInstances target =
      .success evidence := h
  have hs := (ComparisonChecker.run_solution hr).result
  obtain ⟨action, he, _, _, _⟩ := ComparisonChecker.run_domains hr
  have hi : CompareInstantiates source evidence.substitution := by
    rw [he]
    exact ComparisonPreparation.reconstruct_instantiates [] source.requireDefinedInstances target action
  have hg : AlgebraEntailsAll
      (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions
      (evidence.substitution.bounds source.instanceGuards) := by
    intro c hc
    apply hs.2.1 c
    change c ∈ evidence.substitution.bounds (source.bounds ++ source.instanceGuards)
    rw [CompareSubstitution.bounds, List.map_append]
    exact List.mem_append_right _ hc
  obtain ⟨hw, hd⟩ := (CompareSubstitution.instance_guards_iff hi hs.1).mp hg
  have hp : (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions =
      (SchemePreparation.prepare [] source target).assumptions := by
    simp only [SchemePreparation.prepare_assumptions,
      Scheme.requireDefinedInstances_subsumptionIndices]
  exact ⟨hi, hp ▸ hw, hp ▸ hd⟩

theorem checkSubsumption_evidence_defined {fuel : Nat} {source target : Scheme}
    {evidence : SubsumptionEvidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    let declared := (SchemePreparation.prepare [] source target).assumptions
    evidence.substitution.WellFormedUnder declared ∧
      (evidence.substitution.ty source.body).DefinedUnder declared :=
  let hi := checkSubsumption_evidence_instantiatesUnder h
  ⟨hi.images, hi.body⟩

end ModalityInference
