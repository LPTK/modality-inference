import ModalityInference.Proofs.ComparisonDefinedGroupInput
import ModalityInference.Proofs.ComparisonJointAssemblyCompleteness
import ModalityInference.Proofs.ComparisonJointBatchCompleteness
import ModalityInference.ComparisonJointBatchReification

/-! A defined admissible scheme witness reaches the actual joint group batch.
All groups retain one common type and modality action, and every scalar guard
is checked independently of whether any opaque group is present. -/
namespace ModalityInference.ComparisonJointBatchReification

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

theorem prepare_zipWith {fuel : Nat} {assumptions required : Bounds}
    {groups : List ComparisonGroups.Group} {inputs : List ComparisonJointGroup.Input}
    (h : groups.mapM (ComparisonJointGroup.prepare fuel assumptions required) = .success inputs) :
    prepare fuel assumptions required groups = .success (List.zipWith Compiled.mk groups inputs) := by
  induction groups generalizing inputs with
  | nil => cases h; rfl
  | cons group groups ih =>
    simp only [List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hg : ComparisonJointGroup.prepare fuel assumptions required group <;>
      simp only [hg] at h <;> try contradiction
    next input =>
      cases hs : groups.mapM (ComparisonJointGroup.prepare fuel assumptions required) <;>
        simp only [hs] at h <;> try contradiction
      next inputs' =>
        cases h
        simpa only [prepare, List.mapM_cons, hg, bind, pure, RunResult.bind, List.zipWith_cons_cons,
          RunResult.success.injEq] using congrArg (fun rest => do
            let tail ← rest
            pure (Compiled.mk group input :: tail)) (ih hs)

private theorem prepare_forall₂ {fuel : Nat} {assumptions required : Bounds}
    {groups : List ComparisonGroups.Group} {compiled : List Compiled}
    (h : prepare fuel assumptions required groups = .success compiled) :
    List.Forall₂ (fun group c => c.group = group ∧
      ComparisonJointGroup.prepare fuel assumptions required group = .success c.input) groups compiled := by
  induction groups generalizing compiled with
  | nil => cases h; exact .nil
  | cons group groups ih =>
    simp only [prepare, List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hg : ComparisonJointGroup.prepare fuel assumptions required group <;>
      simp only [hg] at h <;> try contradiction
    next input =>
      change (do
        let rest ← prepare fuel assumptions required groups
        pure (Compiled.mk group input :: rest)) = .success compiled at h
      cases hs : prepare fuel assumptions required groups <;>
        simp only [hs, bind, RunResult.bind, pure] at h <;> try contradiction
      next rest =>
        cases h
        exact .cons ⟨rfl, hg⟩ (ih hs)

theorem prepare_forall {fuel : Nat} {assumptions required : Bounds}
    {groups : List ComparisonGroups.Group} {compiled : List Compiled}
    (h : prepare fuel assumptions required groups = .success compiled) :
    ∀ c ∈ compiled, c.group ∈ groups ∧
      ComparisonJointGroup.prepare fuel assumptions required c.group = .success c.input := by
  have hr := prepare_forall₂ h
  clear h
  induction hr with
  | nil => simp
  | @cons group c groups compiled hc hr ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨by simp [hc.1], by simpa only [hc.1] using hc.2⟩
    · exact ⟨List.mem_cons_of_mem _ (ih d hd).1, (ih d hd).2⟩

theorem prepare_groups {fuel : Nat} {assumptions required : Bounds}
    {groups : List ComparisonGroups.Group} {compiled : List Compiled}
    (h : prepare fuel assumptions required groups = .success compiled) :
    compiled.map Compiled.group = groups := by
  have hr := prepare_forall₂ h
  clear h
  induction hr with
  | nil => rfl
  | cons hc hr ih => simp only [List.map_cons, hc.1, ih]

end ModalityInference.ComparisonJointBatchReification

namespace ModalityInference.ComparisonChecker

open ComparisonPropagation ComparisonJointGroup ComparisonJointGuarded
open ComparisonJointBatchReification

theorem prepared_batch_complete {source target : Scheme}
    {shapeFuel groupFuel scalarFuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    (hshape : ComparisonShapeSolver.prepare shapeFuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target) = .success (.solved shapes))
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (w : OrdinaryGroupWitness ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩) {compiled : List Compiled}
    (hcompiled : ComparisonJointBatchReification.prepare groupFuel
      (Setup.work ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
        {}, shapes, known, false⟩).assumptions
      ((Setup.reduced ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
        {}, shapes, known, false⟩) w.reduced).modes w.groups = .success compiled)
    {scalar : CNF} (hscalar : CompactCNF.toCNF scalarFuel true
      (.imp (boundsModeFormula (Setup.work ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
        {}, shapes, known, false⟩).assumptions)
        (boundsModeFormula ((Setup.reduced ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
          {}, shapes, known, false⟩) w.reduced).modes)) = .success scalar) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ∃n, ∀fuel≥n, ∃result, ComparisonJointBatch.run fuel ModalSynthesis.locality
      (SchemeModeSynthesis.atoms s.modeIds) (entries compiled) (6*s.original.firstMode) scalar = .success result := by
  let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
    {}, shapes, known, false⟩
  apply ComparisonJointBatch.run_complete_families (SchemeModeSynthesis.strategy w.core.mode)
    w.strategy_uniform
  · intro i
    have hi : i.val < compiled.length := by simpa only [entries, List.length_map] using i.isLt
    have hc := prepare_forall hcompiled compiled[i.val] (List.getElem_mem hi)
    have hp := prepared_group_input hshape ht hm w hc.1 hc.2
    obtain ⟨choice, hh⟩ := ComparisonJointAssembly.compile_complete hc.2
      (cutoff := s.original.firstMode) (minimumModes := 6*s.original.firstMode) le_rfl w.fixedImages
      (prepared_group_leaf_support hshape ht hm w hc.1) w.domains.mode_fixed hp.1 hp.2
    have he : (entries compiled)[i] = compiled[i.val].entry := by
      change (entries compiled)[i.val] = _
      exact List.getElem_map _
    rw [he]
    exact ⟨choice, nominalStore compiled[i.val].group w.core, hp.1, hh⟩
  · intro inputs
    exact (CompactCNF.toCNF_correct hscalar _).mpr (prepared_scalar_witness w inputs)

/-- Every admissible scheme witness reaches one successful shared batch at a
common fuel, with its original scalar guards retained even for an empty batch. -/
theorem algebra_joint_batch_complete {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    let p := SchemePreparation.prepare [] source.requireDefinedInstances target
    ∃shapes known, ∃w : OrdinaryGroupWitness ⟨p, {}, shapes, known, false⟩,
      ∃compiled : List Compiled, ∃scalar : CNF,
      compiled.map Compiled.group = w.groups ∧ ∃n, ∀fuel≥n,
        ComparisonShapeSolver.prepare fuel p = .success (.solved shapes) ∧
        ComparisonBody.knownTotal fuel (p.assumptions ++ p.sourceBounds.assumptions)
          (ComparisonAnnotations.obligationExpressions p) = .success known ∧
        ComparisonReduction.prepare fuel
          (Setup.work ⟨p, {}, shapes, known, false⟩)
          (Setup.templates ⟨p, {}, shapes, known, false⟩)
          (Setup.bare ⟨p, {}, shapes, known, false⟩) known false = .success w.reduced ∧
        ComparisonJointBatchReification.prepare fuel
          (Setup.work ⟨p, {}, shapes, known, false⟩).assumptions
          ((Setup.reduced ⟨p, {}, shapes, known, false⟩) w.reduced).modes w.groups = .success compiled ∧
        CompactCNF.toCNF fuel true
          (.imp (boundsModeFormula (Setup.work ⟨p, {}, shapes, known, false⟩).assumptions)
            (boundsModeFormula ((Setup.reduced ⟨p, {}, shapes, known, false⟩) w.reduced).modes)) = .success scalar ∧
        ∃result, ComparisonJointBatch.run fuel ModalSynthesis.locality
          (SchemeModeSynthesis.atoms (Setup.modeIds ⟨p, {}, shapes, known, false⟩))
          (entries compiled) (6*p.firstMode) scalar = .success result := by
  obtain ⟨shapes, known, w, inputs, _, n, hn⟩ := algebra_joint_group_input ht hm hR h
  obtain ⟨ns, scalar, hscalar, _⟩ := prepared_scalar_complete w
  have hcompiled := prepare_zipWith (hn n le_rfl).2.2.2
  obtain ⟨nb, hb⟩ := prepared_batch_complete (hn n le_rfl).1 ht hm w hcompiled (hscalar ns le_rfl)
  refine ⟨shapes, known, w, List.zipWith Compiled.mk w.groups inputs, scalar,
    prepare_groups hcompiled, max n (max ns nb), ?_⟩
  intro fuel hf
  obtain ⟨hshape, hknown, hreduce, hgroups⟩ := hn fuel (by omega)
  exact ⟨hshape, hknown, hreduce, prepare_zipWith hgroups, hscalar fuel (by omega), hb fuel (by omega)⟩

end ModalityInference.ComparisonChecker
