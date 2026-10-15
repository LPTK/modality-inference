import ModalityInference.ComparisonJointChecker
import ModalityInference.Proofs.ComparisonDefinedBatchWitness
import ModalityInference.Proofs.ComparisonJointBatchReification

/-! Completeness of the executable shared type and modality comparison path
for admissible scheme instances under the residual target assumptions. -/
namespace ModalityInference.ComparisonJointChecker

open ComparisonChecker ComparisonJointBatchReification

/-- Every comparison witness in the declared defined domain reaches success
through the actual joint comparison driver at all sufficiently large fuels. -/
theorem run_complete {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    ∃n, ∀fuel≥n, ∃result, run fuel source target = .success result := by
  obtain ⟨shapes, known, w, compiled, scalar, _, n, hn⟩ := algebra_joint_batch_complete ht hm hR h
  refine ⟨n, ?_⟩
  intro fuel hf
  obtain ⟨hshape, hknown, hreduce, hprepare, hscalar, batch, hbatch⟩ := hn fuel hf
  obtain ⟨output, hout⟩ := assemble_some hbatch
    (allowedModes (SchemePreparation.prepare [] source.requireDefinedInstances target))
    (fun i => (prepare_forall hprepare compiled[i] (List.getElem_mem i.isLt)).2)
    (fun i => w.nonempty _ (prepare_forall hprepare compiled[i] (List.getElem_mem i.isLt)).1)
  refine ⟨ComparisonPreparation.reconstruct
    (SchemePreparation.prepare [] source.requireDefinedInstances target)
    (restore ⟨SchemePreparation.prepare [] source.requireDefinedInstances target, {}, shapes, known, false⟩ output), ?_⟩
  simp [run, propagate, ComparisonJointElimination.run, ht, hm, hshape, hknown, hreduce,
    w.collection, hprepare, hscalar, hbatch, hout, bind, RunResult.bind, pure]

end ModalityInference.ComparisonJointChecker
