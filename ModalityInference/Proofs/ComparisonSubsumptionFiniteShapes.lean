import ModalityInference.Proofs.ComparisonSubsumptionTermination
import ModalityInference.Proofs.ComparisonSubsumption
import ModalityInference.Proofs.ComparisonPreparedDriverCompleteness

/-! Public scheme comparison accepts every admissible comparison whose declared
shape equations have a finite model. All earlier phases retain their successes;
the prepared structural driver supplies the final successful alternative. -/
namespace ModalityInference

/-- The public checker eventually accepts every admissible comparison with a
finite declared-shape model and duplicate-free source quantifiers. -/
theorem checkSubsumption_finite_shape_complete {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (h : AlgebraSubsumesUnder [] source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions φ) :
    ∃threshold, ∀fuel≥threshold, ∃evidence,
      checkSubsumption fuel source target=.success evidence := by
  obtain ⟨preparedFuel,action,hprepared⟩ :=
    ComparisonPreparedDriver.run_complete_finite_model ht hm h hdecl
  obtain ⟨publicFuel,result,hresult,hpublic⟩ := checkSubsumption_terminates source target
  refine ⟨max preparedFuel publicFuel,fun fuel hf => ?_⟩
  apply checkSubsumption_of_prepared_result
    (hprepared fuel ((Nat.le_max_left _ _).trans hf))
  simpa only [hpublic fuel ((Nat.le_max_right _ _).trans hf)] using hresult

end ModalityInference
