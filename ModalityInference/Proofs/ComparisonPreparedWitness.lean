import ModalityInference.Proofs.ComparisonPreparedQueryAlignment
import ModalityInference.Proofs.ComparisonPreparedScalar

namespace ModalityInference.ComparisonPreparedWitness
open ComparisonSignedObservation ComparisonStructuralEndpoints ComparisonSelectedBases
  ComparisonSignedBranchImages ComparisonPreparation ComparisonAlgebra

/-- Directed whole type endpoints and the independently checked scalar goals
supply exactly the original guarded source constraint list. -/
theorem source_bounds_entails {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hσ : σ.WellFormedUnder p.assumptions)
    (hscalar : EntailsAll p.assumptions
      ((ComparisonPreparedScalar.required p).map (Constraint.subst TypeExpr.var σ.mode)))
    (hpairs : ∀pair∈sourceEndpoints p,AlgebraSubtype p.assumptions (σ.ty pair.1) (σ.ty pair.2)) :
    AlgebraEntailsAll p.assumptions (σ.bounds p.sourceBounds) := by
  have hpair {c : Constraint} (hc : c∈p.sourceBounds) {pair : Ty×Ty} (hp : pair∈constraintPairs c) :
      AlgebraEntails p.assumptions (.sub (σ.ty pair.1) (σ.ty pair.2)) := by
    have hs : pair∈sourceEndpoints p := List.mem_append_left _ (List.mem_flatMap.mpr ⟨c,hc,hp⟩)
    have he : pair∈endpoints p := List.mem_append_right _ hs
    have hg:=ComparisonPreparedScalar.endpoint_guards hscalar he
    exact ⟨hpairs pair hs,
      ComparisonSignedClosedAlignment.defined_of_annotations hσ.types pair.1 (hg _ (by simp)),
      ComparisonSignedClosedAlignment.defined_of_annotations hσ.types pair.2 (hg _ (by simp))⟩
  intro c hc
  obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
  cases original with
  | sub a b => exact hpair ho List.mem_cons_self
  | equiv a b =>
    have hl:=hpair ho (pair:=(a,b)) (by simp [constraintPairs])
    have hr:=hpair ho (pair:=(b,a)) (by simp [constraintPairs])
    exact ⟨hl.1,hr.1,hl.2⟩
  | equal v a =>
    apply (CompareSubstitution.algebra_equal_iff σ p.assumptions v a).mpr
    exact ⟨hpair ho (pair:=(.var v,a)) (by simp [constraintPairs]),
      hpair ho (pair:=(a,.var v)) (by simp [constraintPairs])⟩
  | mode m n =>
    exact hscalar _ (List.mem_map.mpr ⟨.mode m n,
      List.mem_append_left _ (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_,ho,by simp [Constraint.assumptions]⟩,rfl⟩),rfl⟩)
  | defined m =>
    exact hscalar _ (List.mem_map.mpr ⟨.defined m,
      List.mem_append_left _ (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_,ho,by simp [Constraint.assumptions]⟩,rfl⟩),rfl⟩)


/-- Source endpoint and scalar certificates assemble the admissible prepared
witness, retaining the original target and all original source guards. -/
theorem prepared_of_endpoints {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hd : σ.DomainsAbove (SchemePreparation.prepare ambient source target).firstType
      (SchemePreparation.prepare ambient source target).firstMode)
    (hs : σ.WellShaped (SchemePreparation.prepare ambient source target).assumptions)
    (hf : σ.WellFormedUnder (SchemePreparation.prepare ambient source target).assumptions)
    (hscalar : EntailsAll (SchemePreparation.prepare ambient source target).assumptions
      ((ComparisonPreparedScalar.required (SchemePreparation.prepare ambient source target)).map
        (Constraint.subst TypeExpr.var σ.mode)))
    (hpairs : ∀pair∈sourceEndpoints (SchemePreparation.prepare ambient source target),
      AlgebraSubtype (SchemePreparation.prepare ambient source target).assumptions
        (σ.ty pair.1) (σ.ty pair.2)) :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ := by
  let p:=SchemePreparation.prepare ambient source target
  have hbody : (p.sourceType,p.targetType)∈sourceEndpoints p := List.mem_append_right _ List.mem_cons_self
  have he : (p.sourceType,p.targetType)∈endpoints p := List.mem_append_right _ hbody
  have hguard:=ComparisonPreparedScalar.endpoint_guards hscalar he
  refine ⟨⟨hd,hs,source_bounds_entails hf hscalar hpairs,?_⟩,hf,?_⟩
  · have hsub:=hpairs _ hbody
    rw [ty_fixed_bounded hd _ (SchemePreparation.prepare_targetType_bounded_first ambient source target)] at hsub
    exact hsub
  · exact ComparisonSignedClosedAlignment.defined_of_annotations hf.types p.sourceType
      (hguard _ (by simp))

theorem selected_assembled {shapeFuel first scalarFuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (hw : (layout first (SchemePreparation.prepare ambient source target) solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first (SchemePreparation.prepare ambient source target) solved)).reconstruct r parameters=some images)
    {modeImages : SymbolicModes.Elimination
      (ComparisonPreparedScalar.flexibleAtoms (SchemePreparation.prepare ambient source target))}
    {modeAction : Substitution}
    (hm : ComparisonPreparedScalar.assemble (SchemePreparation.prepare ambient source target) modeImages=some modeAction)
    {result : CompareSubstitution}
    (h : select first (SchemePreparation.prepare ambient source target) solved world images modeAction.modes=some result)
    {scalar : ComparisonGuardedEndpointQueries.Source}
    (hscalar : ComparisonPreparedScalar.run scalarFuel (SchemePreparation.prepare ambient source target)=.success scalar)
    {size : Nat→Nat} {shape : Nat→Bool} {family : Nat→(Nat→Bool)→Bool}
    (hv : scalar.Valid size shape family (fun world v=>(modeImages.substitute v).eval world))
    (hpairs : ∀pair∈sourceEndpoints (SchemePreparation.prepare ambient source target),
      AlgebraSubtype (SchemePreparation.prepare ambient source target).assumptions
        (result.ty pair.1) (result.ty pair.2)) :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) result := by
  have hmode : result.mode=modeAction.mode := select_mode h
  have hfixed : ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions
      ({modes:=modeAction.modes}:CompareSubstitution).mode :=
    ComparisonPreparedScalar.assemble_fixed_prepared hm
  apply prepared_of_endpoints (select_domains h ?_) (select_wellShaped hs hw hr hfixed h)
    (select_wellFormed hs hw hr hfixed h) ?_ hpairs
  · intro entry he
    have hn : entry.1∈ComparisonPreparedScalar.modeIds (SchemePreparation.prepare ambient source target) :=
      (ComparisonPreparedScalar.assemble_domain hm).2 ▸ List.mem_map.mpr ⟨entry,he,rfl⟩
    exact ((ComparisonPreparedScalar.mem_modeIds _ _).mp hn).1
  · rw [hmode]
    exact ComparisonPreparedScalar.assembled_entails hscalar hm hv

end ModalityInference.ComparisonPreparedWitness
