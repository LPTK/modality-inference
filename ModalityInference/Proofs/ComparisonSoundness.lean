import ModalityInference.Proofs.ComparisonDefinedEvidence
import ModalityInference.Proofs.ComparisonAlgebraInstances
import ModalityInference.Proofs.Obligations
import ModalityInference.Proofs.ComparisonDefinedSemantics

/-! Executable inference and signature checking preserve the interpretation of
public schemes, including each instance's ownership and evaluation guarantees. -/
namespace ModalityInference

theorem checkSubsumption_defined_subsumes {fuel source target evidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    AlgebraSubsumesUnder [] source target := by
  obtain ⟨hi, hs, hb, ht⟩ := checkSubsumption_evidence_result h
  exact ⟨evidence.substitution, hi.domain, hs, hi.images, hi.body, hb, ht⟩

theorem checkSubsumption_algebra_subsumes {fuel source target evidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    AlgebraSubsumes [] source target :=
  (checkSubsumption_defined_subsumes h).to_algebra

theorem scheme_subsumption_sound : Obligations.SchemeSubsumptionSound := by
  intro fuel source target evidence _ _ _ h
  exact checkSubsumption_defined_subsumes h

/-- Successful signature checking preserves every admissible public ground
instance, including for source schemes without a typing derivation. -/
theorem checkSubsumption_ground_covers {fuel source target evidence ρ}
    (h : checkSubsumption fuel source target = .success evidence) :
    SchemeCovers ρ ρ source target :=
  (checkSubsumption_defined_subsumes h).ground_covers (by simp [GroundModels])

theorem inference_checked_ground_covers
    {inferenceFuel comparisonFuel Γ t result target evidence ρ}
    (hi : infer inferenceFuel Γ t = .success result)
    (hc : checkSubsumption comparisonFuel result.scheme target = .success evidence) :
    SchemeCovers ρ ρ result.scheme target :=
  inference_comparison_ground_covers hi (checkSubsumption_algebra_subsumes hc)
    (by simp [GroundModels])

theorem inference_checked_resource_semantic
    {inferenceFuel comparisonFuel Γ t result target evidence ρ w v reserved}
    (hi : infer inferenceFuel Γ t = .success result)
    (hc : checkSubsumption comparisonFuel result.scheme target = .success evidence)
    (hv : Runtime.ResourceSchemeInterpretation ρ w result.scheme v reserved) :
    Runtime.ResourceSchemeInterpretation ρ w target v reserved :=
  inference_comparison_resource_semantic hi (checkSubsumption_algebra_subsumes hc)
    (by simp [GroundModels]) hv

/-- A successfully inferred and checked closed program executes safely at every
admissible instance of the declared public signature. -/
theorem inference_checked_source_semantic
    {inferenceFuel comparisonFuel t result target evidence ρ η w ground}
    (hi : infer inferenceFuel [] t = .success result)
    (hc : checkSubsumption comparisonFuel result.scheme target = .success evidence)
    (hη : GroundInstantiates ρ target η) (ht : target.body.realize η = some ground) :
    Runtime.ResourceSemanticEvaluation w [] result.elaborated ground ∅ :=
  inference_comparison_source_semantic hi (checkSubsumption_algebra_subsumes hc)
    (by simp [GroundModels]) hη ht

end ModalityInference
