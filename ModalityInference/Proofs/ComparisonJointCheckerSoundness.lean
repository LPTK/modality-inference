import ModalityInference.Proofs.ComparisonJointEliminationSoundness
import ModalityInference.Proofs.ComparisonJointCheckerTrace
import ModalityInference.Proofs.ComparisonJointCheckerScope
import ModalityInference.Proofs.ComparisonJointRestoration
import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonSkeletonNames
import ModalityInference.Proofs.ComparisonPreparedCollection

/-! Every successful shared comparison returns an admissible substitution for
the original source scheme under the unchanged declared target assumptions. -/
namespace ModalityInference.ComparisonJointChecker

open ComparisonChecker

theorem PropagateTrace.sound {fuel : Nat} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {action : CompareSubstitution}
    (t : PropagateTrace fuel (SchemePreparation.prepare [] source.requireDefinedInstances target)
      shapes action)
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hs : ComparisonShapeSolver.prepare fuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target) = .success (.solved shapes)) :
    let p := SchemePreparation.prepare [] source.requireDefinedInstances target
    action.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (action.bounds p.sourceBounds) ∧
      AlgebraSubtype p.assumptions (action.ty p.sourceType) (.ofTy p.targetType) := by
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let s := executionSetup p shapes t.known
  have hg : SchemePreparation.BinderGuards s.original :=
    SchemePreparation.prepare_binderGuards [] source target ht hm
  have hwork := s.work_of_binderGuards rfl hg
  have htemplates := s.templates_of_binderGuards rfl hg rfl
  obtain ⟨e⟩ := ComparisonJointElimination.run_trace t.elimination_eq
  obtain ⟨hfixed, hrequired, hlabels, hscalar⟩ := collection_mode_scope ht hm t.reduced_eq e.collection
  have hshape : ∀ η, ComparisonShape.Models s.work.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v := by
    rw [hwork]
    intro η hη
    exact ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hη
  have hfresh : ∀leaf∈s.templates.leaves,
      ∀v∈s.work.assumptions.typeVariables ++ s.work.targetType.typeVariables ++
        s.work.sourceType.typeVariables ++ s.work.sourceBounds.typeVariables, v ≠ .flex leaf.name := by
    rw [hwork, htemplates]
    exact ComparisonGroups.prepared_leaves_fresh [] source.requireDefinedInstances target shapes
  have hn : (s.templates.leaves.map (·.name)).Nodup :=
    ComparisonSkeleton.allocate_leaf_names_nodup _ _ _ _ _
  have hname : ∀a∈s.templates.leaves, ∀b∈s.templates.leaves, a.name = b.name → a = b :=
    fun _ ha _ hb => ComparisonSkeleton.allocate_leaf_name_injective _ _ _ _ _ ha hb
  have hd : s.work.assumptions.TypeBoundsDefined := by
    rw [hwork]
    exact SchemePreparation.prepared_typeBoundsDefined source.requireDefinedInstances target
  have hguards : ComparisonReduction.OpaqueGuards (s.reduced t.reduced) :=
    (ComparisonReduction.prepare_opaqueGuards t.reduced_eq).prepend_modes _
  have he := e.sound hshape hfresh hn hname hfixed hrequired hlabels hd hguards hscalar
  have hf := ComparisonJointElimination.setup_run_prepared_fixed (s := s) rfl t.elimination_eq
  have hrest := restore_sound (s := s) rfl rfl hg t.known_eq t.reduced_eq
    (by simpa only [hwork] using he.1) (by simpa only [hwork] using he.2.1)
    hf.1 hf.2.1 hf.2.2
    (by simpa only [Setup.reduced, hwork] using he.2.2.2)
    (by simpa only [hwork] using he.2.2.1)
  rw [t.action_eq]
  exact hrest

theorem RunTrace.guarded_result {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (t : RunTrace fuel source target result) :
    let p := SchemePreparation.prepare [] source.requireDefinedInstances target
    result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.requireDefinedInstances.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨pt⟩ := propagate_trace t.propagate_eq
  obtain ⟨hs, hb, ht⟩ := pt.sound t.types_nodup t.modes_nodup t.shape_eq
  let guarded := source.requireDefinedInstances
  let p := SchemePreparation.prepare [] guarded target
  have htypes : ∀v∈guarded.body.typeVars ∪ guarded.bounds.typeVars,
      t.action.type v = .var v := by
    intro v hv
    apply t.action_domains.type_fixed
    apply SchemePreparation.original_type_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalTypeIds, List.mem_append,
      TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
    tauto
  have hmodes : ∀v∈guarded.body.modVars ∪ guarded.bounds.modVars,
      t.action.mode v = .var v := by
    intro v hv
    apply t.action_domains.mode_fixed
    apply SchemePreparation.original_mode_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalModeIds, List.mem_append,
      TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
    tauto
  rw [t.result_eq]
  refine ⟨ComparisonPreparation.reconstruct_wellShaped hs, ?_, ?_⟩
  · exact (ComparisonPreparation.reconstruct_algebra_bounds p t.action guarded.bounds p.assumptions
      (fun v hv => htypes v (Finset.mem_union_right _ hv))
      (fun v hv => hmodes v (Finset.mem_union_right _ hv))).mpr hb
  · change AlgebraSubtype p.assumptions ((ComparisonPreparation.reconstruct p t.action).ty guarded.body)
      (.ofTy p.targetType)
    rw [ComparisonPreparation.reconstruct_ty p t.action guarded.body
      (fun v hv => htypes v (Finset.mem_union_left _ hv))
      (fun v hv => hmodes v (Finset.mem_union_left _ hv))]
    exact ht

/-- The returned substitution realizes the source's original bounds and body;
its complete quantified image family is defined under the declared target. -/
theorem run_result {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target = .success result) :
    let p := SchemePreparation.prepare [] source target
    CompareInstantiatesUnder p.assumptions source result ∧
      result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨t⟩ := run_trace h
  have hs := t.guarded_result
  have hi := run_domain h
  have hb : AlgebraEntailsAll (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions
      (result.bounds source.bounds) ∧
      AlgebraEntailsAll (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions
        (result.bounds source.instanceGuards) := by
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

theorem run_algebra_subsumesUnder {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target = .success result) : AlgebraSubsumesUnder [] source target := by
  obtain ⟨hi, hs, hb, ht⟩ := run_result h
  exact ⟨result, hi.domain, hs, hi.images, hi.body, hb, ht⟩

theorem run_instantiatesUnder {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target = .success result) :
    CompareInstantiatesUnder (SchemePreparation.prepare [] source target).assumptions source result :=
  (run_result h).1

end ModalityInference.ComparisonJointChecker
