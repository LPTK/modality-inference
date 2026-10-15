import ModalityInference.Proofs.ComparisonDefinedReductionSetup

/-! The ordinary checker path carries an admissible prepared witness through
its actual template allocation and both structural reduction passes. -/

namespace ModalityInference.ComparisonChecker

open SchemePreparation ComparisonReduction

theorem prepared_reduction_complete {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    {known : List ModExpr}
    (hshape : ComparisonShapeSolver.prepare fuel
      (prepare [] source.requireDefinedInstances target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (prepare [] source.requireDefinedInstances target) σ)
    (hR : Residual target.bounds)
    (hk : ComparisonBody.knownTotal fuel
      ((prepare [] source.requireDefinedInstances target).assumptions ++
        (prepare [] source.requireDefinedInstances target).sourceBounds.assumptions)
      (ComparisonAnnotations.obligationExpressions
        (prepare [] source.requireDefinedInstances target)) = .success known) :
    let p := prepare [] source.requireDefinedInstances target
    ∃ trees : ComparisonSkeleton.CoordinateTrees p.assumptions p solved, ∃ n reduced,
      let core := ComparisonSkeleton.preparedForest p solved trees σ
      (∀ budget ≥ n, ComparisonReduction.prepare budget p
        (ComparisonSkeleton.prepare p solved) [] known false = .success reduced) ∧
      core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
      OrdinaryHolds p.assumptions core reduced ∧
      (∀ v, v.index < p.nextMode → core.mode v = σ.mode v) ∧
      (∀ v, v.index < p.nextType → core.type v = .var v) := by
  let p := prepare [] source.requireDefinedInstances target
  have hR' : Residual p.assumptions := prepare_assumptions_residual hR
  obtain ⟨trees, hs, hWF, hb, hd, hbody, hmode, htype⟩ :=
    ComparisonSkeleton.prepared_template_under hshape hw hR
  let core := ComparisonSkeleton.preparedForest p solved trees σ
  have hdom : core.DomainsAbove p.nextType p.firstMode :=
    ComparisonSkeleton.preparedForest_domains p solved trees σ (Nat.le_add_right _ _) hw.1.1
  have htargetBounds := (TypeExpr.bounded_iff _ _ _).mp
    (prepare_targetType_bounded_first [] source.requireDefinedInstances target)
  have htarget : core.ty p.targetType = .ofTy p.targetType := by
    apply CompareSubstitution.ty_fixed
    · intro v hv
      exact hdom.type_fixed v ((htargetBounds.1 v hv).trans_le (Nat.le_add_right _ _))
    · exact fun v hv => hdom.mode_fixed v (htargetBounds.2 v hv)
  have hknown := hw.known_annotations hk
  have hsourceAnnotations : AnnotationsTotal known p.sourceType := by
    intro m hm
    exact hknown m (List.mem_append_left _ (List.mem_append_left _ hm))
  have htargetAnnotations : AnnotationsTotal known p.targetType := by
    intro m hm
    exact hknown m (List.mem_append_left _ (List.mem_append_right _ hm))
  have hp : DefinedPair p.assumptions core known
      ((ComparisonSkeleton.prepare p solved).substitution.ty p.sourceType, p.targetType) := by
    refine ⟨?_, hd, ?_, ComparisonSkeleton.prepare_annotations_total known p solved hsourceAnnotations,
      htargetAnnotations⟩
    · simpa only [PairHolds, htarget] using hbody
    · simpa only [htarget, CompareTy.definedUnder_ofTy] using hw.target_defined
  have hboundAnnotations : ∀ c ∈ (ComparisonSkeleton.prepare p solved).substitution.bounds p.sourceBounds,
      ∀ m ∈ ComparisonAnnotations.constraintExpressions c, ComparisonBody.isTotal known m = true := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    apply constraint_annotations_substitution _ (ComparisonSkeleton.prepare_mode p solved)
      (ComparisonSkeleton.prepare_type_annotations_total known p solved)
    intro m hm
    exact hknown m (List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, hm⟩))
  have hinit := initial_ordinary_holds hWF hb hp hboundAnnotations
  have hi : OrdinaryHolds p.assumptions core
      (ordinaryInitial p (ComparisonSkeleton.prepare p solved) known) :=
    ⟨hinit.pending, hinit.inequalities, hinit.modes, rfl, rfl⟩
  obtain ⟨n, reduced, hr, hh⟩ := prepare_complete_ordinary hR' hs
    (ComparisonSkeleton.preparedForest_opaque hR' p solved trees σ) hi
  exact ⟨trees, n, reduced, hr, hs, hWF, hh, hmode, htype⟩

private theorem scalarBounds_substitution_congr {guards : Bounds} {σ τ : CompareSubstitution}
    (h : ∀ v ∈ guards.modVars, σ.mode v = τ.mode v) :
    σ.bounds (ComparisonGuardedTotal.scalarBounds guards) =
      τ.bounds (ComparisonGuardedTotal.scalarBounds guards) := by
  apply List.map_congr_left
  intro c hc
  have hm : ∀ v ∈ c.modVars, σ.mode v = τ.mode v := fun v hv =>
    h v (ComparisonGuardedTotal.scalarBounds_modVars guards
      ((Bounds.mem_modVars_iff _ _).mpr ⟨c, hc, hv⟩))
  have hkind := (List.mem_filter.mp hc).2
  cases c with
  | sub | equiv | equal => simp at hkind
  | mode a b =>
    exact congrArg₂ CompareConstraint.mode
      (a.subst_congr (fun v hv => hm v (Finset.mem_union_left _ hv)))
      (b.subst_congr (fun v hv => hm v (Finset.mem_union_right _ hv)))
  | defined a => exact congrArg CompareConstraint.defined (a.subst_congr hm)

/-- The actual ordinary propagation setup preserves the same witness, including
all source scalar guards retained in the final synthesis query. -/
theorem prepared_ordinary_reduction_complete {source target : Scheme}
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
    let p := prepare [] source.requireDefinedInstances target
    let s : Setup := ⟨p, {}, solved, known, false⟩
    ∃ trees : ComparisonSkeleton.CoordinateTrees p.assumptions p solved, ∃ n reduced,
      let core := ComparisonSkeleton.preparedForest p solved trees σ
      (∀ budget ≥ n, ComparisonReduction.prepare budget s.work s.templates s.bare known false =
        .success reduced) ∧
      core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
      OrdinaryHolds p.assumptions core (s.reduced reduced) ∧
      (∀ v, v.index < p.nextMode → core.mode v = σ.mode v) ∧
      (∀ v, v.index < p.nextType → core.type v = .var v) := by
  let p := prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, solved, known, false⟩
  have hg : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hwork := s.work_of_binderGuards rfl hg
  have htemplates := s.templates_of_binderGuards rfl hg rfl
  have hbare := s.bare_of_binderGuards rfl hg rfl
  obtain ⟨trees, n, reduced, hr, hs, hWF, hh, hmode, htype⟩ :=
    prepared_reduction_complete hshape hw hR hk
  let core := ComparisonSkeleton.preparedForest p solved trees σ
  have hscalar : AlgebraEntailsAll p.assumptions
      (core.bounds (ComparisonGuardedTotal.scalarBounds p.sourceBounds)) := by
    rw [scalarBounds_substitution_congr (τ := σ) (fun v hv => hmode v
      (((Bounds.bounded_iff _ _ _).mp
        (prepare_sourceBounds_bounded [] source.requireDefinedInstances target)).2 v hv))]
    exact ComparisonGuardedTotal.scalarBounds_entails hw.1.2.2.1
  have ha : s.annotations.bounds = [] := by
    simpa only [Setup.annotations, s.absorbed_of_binderGuards rfl hg] using
      (annotations_trivial hg s.total).2.1
  have hinput := s.input_empty rfl
  dsimp only [s, p] at hwork htemplates hbare ha hinput
  refine ⟨trees, n, reduced, ?_, hs, hWF, ?_, hmode, htype⟩
  · simpa only [hwork, htemplates, hbare] using hr
  · refine ⟨hh.pending, hh.inequalities, ?_, hh.bare, hh.shared⟩
    simpa only [Setup.reduced, ha, hinput, List.nil_append,
      CompareSubstitution.bounds, List.map_append, AlgebraEntailsAll, List.mem_append,
      or_imp, forall_and] using And.intro hscalar hh.modes

end ModalityInference.ComparisonChecker
