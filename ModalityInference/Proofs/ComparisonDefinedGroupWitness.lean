import ModalityInference.Proofs.ComparisonPreparedCollection
import ModalityInference.Proofs.ComparisonFixedModeScope
import ModalityInference.Proofs.BackendComplete

/-! Admissible comparison witnesses reach the actual finite opaque-group
obligations with one shared assignment of type and modality coordinates. -/

namespace ModalityInference.ComparisonChecker

open SchemePreparation ComparisonReduction

theorem scalarBounds_finish {before : Substitution} (hm : ∀v, before.mode v = .var v)
    (after : CompareSubstitution) (bounds : Bounds) :
    (ComparisonExactContext.finish before after).bounds (ComparisonGuardedTotal.scalarBounds bounds) =
      after.bounds (ComparisonGuardedTotal.scalarBounds bounds) := by
  have hf : (ComparisonExactContext.finish before after).mode = after.mode := by
    funext v
    rw [ComparisonExactContext.finish_mode, hm]
    rfl
  apply List.map_congr_left
  intro c hc
  have hc := (List.mem_filter.mp hc).2
  cases c <;> try contradiction
  all_goals simp only [CompareSubstitution.constraint, hf]

theorem template_scalarBounds {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {core : CompareSubstitution}
    (hb : AlgebraEntailsAll p.assumptions
      (core.bounds ((ComparisonSkeleton.prepare p solved).substitution.bounds p.sourceBounds))) :
    AlgebraEntailsAll p.assumptions (core.bounds (ComparisonGuardedTotal.scalarBounds p.sourceBounds)) := by
  have hb' : AlgebraEntailsAll p.assumptions
      ((ComparisonExactContext.finish (ComparisonSkeleton.prepare p solved).substitution core).bounds
        p.sourceBounds) := by
    rwa [ComparisonExactContext.finish_bounds]
  have hs := ComparisonGuardedTotal.scalarBounds_entails hb'
  simpa only [scalarBounds_finish (ComparisonSkeleton.prepare_mode p solved)] using hs

theorem prepared_core_reduction_complete {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ core : CompareSubstitution}
    {known : List ModExpr}
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (prepare [] source.requireDefinedInstances target) σ)
    (hR : Residual target.bounds)
    (hk : ComparisonBody.knownTotal fuel
      ((prepare [] source.requireDefinedInstances target).assumptions ++
        (prepare [] source.requireDefinedInstances target).sourceBounds.assumptions)
      (ComparisonAnnotations.obligationExpressions
        (prepare [] source.requireDefinedInstances target)) = .success known)
    (hdom : core.DomainsAbove (prepare [] source.requireDefinedInstances target).nextType
      (prepare [] source.requireDefinedInstances target).firstMode)
    (hws : core.WellShaped (prepare [] source.requireDefinedInstances target).assumptions)
    (hWF : core.WellFormedUnder (prepare [] source.requireDefinedInstances target).assumptions)
    (hb : AlgebraEntailsAll (prepare [] source.requireDefinedInstances target).assumptions
      (core.bounds ((ComparisonSkeleton.prepare (prepare [] source.requireDefinedInstances target) solved).substitution.bounds
        (prepare [] source.requireDefinedInstances target).sourceBounds)))
    (hd : (core.ty ((ComparisonSkeleton.prepare (prepare [] source.requireDefinedInstances target) solved).substitution.ty
      (prepare [] source.requireDefinedInstances target).sourceType)).DefinedUnder
        (prepare [] source.requireDefinedInstances target).assumptions)
    (hbody : AlgebraSubtype (prepare [] source.requireDefinedInstances target).assumptions
      (core.ty ((ComparisonSkeleton.prepare (prepare [] source.requireDefinedInstances target) solved).substitution.ty
        (prepare [] source.requireDefinedInstances target).sourceType))
      (.ofTy (prepare [] source.requireDefinedInstances target).targetType))
    (ho : OpaqueAction core) :
    let p := prepare [] source.requireDefinedInstances target
    ∃n reduced, (∀budget≥n, ComparisonReduction.prepare budget p
      (ComparisonSkeleton.prepare p solved) [] known false = .success reduced) ∧
      OrdinaryHolds p.assumptions core reduced := by
  let p := prepare [] source.requireDefinedInstances target
  have hR' : Residual p.assumptions := prepare_assumptions_residual hR
  have ht := (TypeExpr.bounded_iff _ _ _).mp
    (prepare_targetType_bounded_first [] source.requireDefinedInstances target)
  have htarget : core.ty p.targetType = .ofTy p.targetType :=
    CompareSubstitution.ty_fixed _
      (fun v hv => hdom.type_fixed v ((ht.1 v hv).trans_le (Nat.le_add_right _ _)))
      (fun v hv => hdom.mode_fixed v (ht.2 v hv))
  have hknown := hw.known_annotations hk
  have hsAnnotations : AnnotationsTotal known p.sourceType := fun m hm =>
    hknown m (List.mem_append_left _ (List.mem_append_left _ hm))
  have htAnnotations : AnnotationsTotal known p.targetType := fun m hm =>
    hknown m (List.mem_append_left _ (List.mem_append_right _ hm))
  have hp : DefinedPair p.assumptions core known
      ((ComparisonSkeleton.prepare p solved).substitution.ty p.sourceType, p.targetType) := by
    refine ⟨?_, hd, ?_, ComparisonSkeleton.prepare_annotations_total known p solved hsAnnotations,
      htAnnotations⟩
    · simpa only [PairHolds, htarget] using hbody
    · simpa only [htarget, CompareTy.definedUnder_ofTy] using hw.target_defined
  have hboundAnnotations : ∀c∈(ComparisonSkeleton.prepare p solved).substitution.bounds p.sourceBounds,
      ∀m∈ComparisonAnnotations.constraintExpressions c, ComparisonBody.isTotal known m = true := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    apply constraint_annotations_substitution _ (ComparisonSkeleton.prepare_mode p solved)
      (ComparisonSkeleton.prepare_type_annotations_total known p solved)
    intro m hm
    exact hknown m (List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, hm⟩))
  have hinit := initial_ordinary_holds hWF hb hp hboundAnnotations
  exact prepare_complete_ordinary hR' hws ho
    ⟨hinit.pending, hinit.inequalities, hinit.modes, rfl, rfl⟩

structure OrdinaryGroupWitness (s : Setup) where
  core : CompareSubstitution
  reduced : ComparisonReduction.State
  groups : List ComparisonGroups.Group
  budget : Nat
  reduction : ∀fuel≥budget, ComparisonReduction.prepare fuel s.work s.templates s.bare
    s.known s.shared = .success reduced
  collection : ComparisonGroups.collect s.work s.shapes s.templates (s.reduced reduced) = .success groups
  domains : core.DomainsAbove s.original.nextType s.original.firstMode
  shaped : core.WellShaped s.work.assumptions
  defined : core.WellFormedUnder s.work.assumptions
  holds : OrdinaryHolds s.work.assumptions core (s.reduced reduced)
  fixedImages : ComparisonFixedModeWitness.FixedImages s.original.firstMode core
  leafShape : ∀leaf∈s.templates.leaves, ComparisonShape.Equivalent s.work.assumptions
    (core.type (.flex leaf.name)).shape (.var leaf.shapeClass)
  modeSupport : ∀v∈ComparisonFixedModeWitness.inputModes (s.templates.substitution.bounds s.work.sourceBounds)
    (s.templates.substitution.ty s.work.sourceType), ∀w∈(core.mode v).vars, w.index < s.original.firstMode
  modeDomain : ∀entry∈core.modes, entry.1 ∈ s.modeIds
  covered : ∀g∈groups, ComparisonJointGroup.Covered g
  nonempty : ∀g∈groups, g.heads ≠ []

/-- The actual ordinary prepasses, reduction, and group collection admit one
defined, shape-correct coordinate witness using only fixed input modes. -/
theorem prepared_fixed_group_witness {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    {known : List ModExpr}
    (hshape : ComparisonShapeSolver.prepare fuel
      (prepare [] source.requireDefinedInstances target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (prepare [] source.requireDefinedInstances target) σ)
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds)
    (hk : ComparisonBody.knownTotal fuel
      ((prepare [] source.requireDefinedInstances target).assumptions ++
        (prepare [] source.requireDefinedInstances target).sourceBounds.assumptions)
      (ComparisonAnnotations.obligationExpressions
        (prepare [] source.requireDefinedInstances target)) = .success known) :
    Nonempty (OrdinaryGroupWitness ⟨prepare [] source.requireDefinedInstances target, {}, solved, known, false⟩) := by
  let p := prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, solved, known, false⟩
  have hg : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hwork := s.work_of_binderGuards rfl hg
  have htemplates := s.templates_of_binderGuards rfl hg rfl
  have hbare := s.bare_of_binderGuards rfl hg rfl
  have hmodeIds := s.modeIds_of_binderGuards rfl hg
  have ha : s.annotations.bounds = [] := by
    simpa only [Setup.annotations, s.absorbed_of_binderGuards rfl hg] using
      (annotations_trivial hg s.total).2.1
  have hinput := s.input_empty rfl
  obtain ⟨core, hdom, hs, hWF, hb, hd, hbody, hfixed, hleaf, hmode, ho, hupper⟩ :=
    ComparisonFixedModeWitness.prepared_template_fixed_scoped hshape hw hR
  obtain ⟨n, reduced, hr, hh⟩ := prepared_core_reduction_complete hw hR hk hdom hs hWF hb hd hbody ho
  have hscalar := template_scalarBounds hb
  obtain ⟨groups, hc⟩ := ComparisonGroups.prepared_collect_complete hshape
    (prepare_assumptions_residual (source := source.requireDefinedInstances) hR)
    (hr n le_rfl) hdom.type_fixed hleaf hh.inequalities
  have hcovered : ∀g∈groups, ComparisonJointGroup.Covered g :=
    fun g hg => ComparisonGroups.prepared_collect_covered hshape (hr n le_rfl) hc hg
  have hnonempty : ∀g∈groups, g.heads ≠ [] :=
    fun g hg => ComparisonGroups.prepared_collect_nonempty hshape (hr n le_rfl) hc hg
  dsimp only [s, p] at hwork htemplates hbare hmodeIds ha hinput
  refine ⟨{
    core := core
    reduced := reduced
    groups := groups
    budget := n
    reduction := ?_
    collection := ?_
    domains := hdom
    shaped := ?_
    defined := ?_
    holds := ?_
    fixedImages := hfixed
    leafShape := ?_
    modeSupport := ?_
    modeDomain := ?_
    covered := hcovered
    nonempty := hnonempty }⟩
  · simpa only [hwork, htemplates, hbare] using hr
  · simpa only [hwork, htemplates] using hc
  · simpa only [hwork] using hs
  · simpa only [hwork] using hWF
  · rw [hwork]
    refine ⟨hh.pending, hh.inequalities, ?_, hh.bare, hh.shared⟩
    simpa only [Setup.reduced, ha, hinput, List.nil_append,
      CompareSubstitution.bounds, List.map_append, AlgebraEntailsAll, List.mem_append,
      or_imp, forall_and] using And.intro hscalar hh.modes
  · simpa only [hwork, htemplates] using hleaf
  · simpa only [hwork, htemplates] using hmode
  · intro entry he
    rw [hmodeIds, htemplates]
    apply List.mem_range'_1.mpr
    have hlo := hdom.2 entry he
    have hhi := hupper entry he
    exact ⟨hlo, by omega⟩

/-- Every admissible comparison in the residual-target domain reaches the
actual ordinary group input at one common sufficiently large fuel. -/
theorem algebra_ordinary_group_witness {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    let p := prepare [] source.requireDefinedInstances target
    ∃solved known, ∃witness : OrdinaryGroupWitness ⟨p, {}, solved, known, false⟩,
      ∃n, ∀fuel≥n,
        ComparisonShapeSolver.prepare fuel p = .success (.solved solved) ∧
        ComparisonBody.knownTotal fuel (p.assumptions ++ p.sourceBounds.assumptions)
          (ComparisonAnnotations.obligationExpressions p) = .success known ∧
        ComparisonReduction.prepare fuel
          (Setup.work ⟨p, {}, solved, known, false⟩)
          (Setup.templates ⟨p, {}, solved, known, false⟩)
          (Setup.bare ⟨p, {}, solved, known, false⟩) known false = .success witness.reduced := by
  let p := prepare [] source.requireDefinedInstances target
  obtain ⟨σ, hw⟩ := ComparisonPreparation.prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨ns, solved, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete_residual hw.1
    (prepare_assumptions_residual (source := source.requireDefinedInstances) hR)
  obtain ⟨nk, known, hk⟩ := ComparisonBody.knownTotal_eventual_success
    (p.assumptions ++ p.sourceBounds.assumptions) (ComparisonAnnotations.obligationExpressions p)
  obtain ⟨witness⟩ := prepared_fixed_group_witness
    (hs (max ns nk) (Nat.le_max_left _ _)) hw ht hm hR
    (hk (max ns nk) (Nat.le_max_right _ _))
  refine ⟨solved, known, witness, max (max ns nk) witness.budget, ?_⟩
  intro fuel hf
  exact ⟨hs fuel (by omega), hk fuel (by omega), witness.reduction fuel (by omega)⟩

end ModalityInference.ComparisonChecker
