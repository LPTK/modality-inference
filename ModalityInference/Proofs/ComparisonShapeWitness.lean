import ModalityInference.Proofs.ComparisonSkeletonShapeRealizer

namespace ModalityInference.ComparisonSkeleton

open ComparisonShapeSolver ComparisonPreparation ComparisonStructuralProjection

/-- A declared-shape unifier can be instantiated by any source witness while
leaving every non-source shape parameter fixed. -/
theorem unify_fixed_realizer {fuel : Nat} {p : SchemePreparation.Prepared} {fixed : Assignment}
    (h : unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) = .success fixed)
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) (σ : CompareSubstitution) (v : TypeVar)
    (hv : sourceAllowed p v = false → σ.type v = .var v) :
    (action fixed v).subst (shapeRealizer p σ (action fixed)) = witnessShape σ (action fixed) v := by
  obtain ⟨hfixed, himages⟩ := unify_support h
    (Measure.vars (ComparisonShape.pairs p.assumptions)) Finset.Subset.rfl
  by_cases ha : sourceAllowed p v = true
  · have hn : v ∉ Measure.vars (ComparisonShape.pairs p.assumptions) := by
      intro hm
      exact Bool.noConfusion (ha.symm.trans (hscope v hm))
    rw [hfixed v hn]
    simp [ComparisonShape.subst, shapeRealizer, ha]
  · have ha : sourceAllowed p v = false := Bool.eq_false_iff.mpr ha
    rw [witnessShape, hv ha]
    change (action fixed v).subst _ = action fixed v
    refine (subst_congr _ ?_).trans (subst_id _)
    intro w hw
    have haw : sourceAllowed p w = false := by
      by_cases hmem : v ∈ Measure.vars (ComparisonShape.pairs p.assumptions)
      · exact hscope w (himages v hmem (List.mem_toFinset.mpr hw))
      · rw [hfixed v hmem] at hw
        have he : w = v := by simpa [ComparisonShape.vars] using hw
        exact he ▸ ha
    exact shapeRealizer_fixes p σ (action fixed) w haw

theorem unify_source_realizer {fuel : Nat} {p : SchemePreparation.Prepared} {fixed : Assignment}
    (h : unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) = .success fixed)
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) (σ : CompareSubstitution)
    (hm : ComparisonShapeSolver.Models (sourcePairs p) (witnessShape σ (action fixed)))
    (hf : ∀ v ∈ Measure.vars (sourcePairs p), sourceAllowed p v = false → σ.type v = .var v) :
    ComparisonShapeSolver.Models (mapPairs (action fixed) (sourcePairs p))
      (shapeRealizer p σ (action fixed)) := by
  apply (models_mapPairs _ _ _).mpr
  intro pair hp
  have he (side : ComparisonShape) (hh : ∀v∈side.vars, v ∈ Measure.vars (sourcePairs p)) :
      side.subst (fun v => (action fixed v).subst (shapeRealizer p σ (action fixed))) =
        side.subst (witnessShape σ (action fixed)) :=
    subst_congr side (fun v hv => unify_fixed_realizer h hscope σ v (hf v (hh v hv)))
  exact (he pair.1 (fun v hv => (Measure.mem_vars _ _).mpr ⟨pair.1, pair.2, hp, .inl hv⟩)).trans
    ((hm pair hp).trans (he pair.2
      (fun v hv => (Measure.mem_vars _ _).mpr ⟨pair.1, pair.2, hp, .inr hv⟩)).symm)

/-- Shape preparation eventually succeeds for every prepared semantic witness
whose declared shape equations have a model. This includes arbitrary partial
witness images and does not assume an already successful source unification. -/
theorem prepared_witness_shape_complete {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hw : PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (hdecl : ∃ρ, ComparisonShape.Models (SchemePreparation.prepare ambient source target).assumptions ρ) :
    ∃ n solved, ∀fuel ≥ n, ComparisonShapeSolver.prepare fuel
      (SchemePreparation.prepare ambient source target) = .success (.solved solved) := by
  obtain ⟨φ, hφ⟩ := hdecl
  obtain ⟨n, fixed, hf⟩ := unify_complete hφ
    (show Fixes (fun _ => true) φ from fun _ hv => Bool.noConfusion hv)
  have hfixed := hf n (Nat.le_refl _)
  have hm := prepared_witness_shape_model hw (unify_sound hfixed)
    (fun v hv => hw.1.type_fixed v (((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_targetType_bounded_first ambient source target)).1 v hv))
  have hsource := unify_source_realizer hfixed (prepared_assumptions_fixed ambient source target) σ hm
    (fun v hv => prepared_witness_fixed hw v (prepared_sourcePairs_bounded ambient source target hv))
  obtain ⟨m, sourceAction, hm⟩ := prepare_residual_complete hfixed hsource (shapeRealizer_fixes _ _ _)
  exact ⟨m, ⟨fixed, sourceAction⟩, hm⟩

theorem prepared_witness_shape_complete_residual {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hw : PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (hR : Residual (SchemePreparation.prepare ambient source target).assumptions) :
    ∃ n solved, ∀fuel ≥ n, ComparisonShapeSolver.prepare fuel
      (SchemePreparation.prepare ambient source target) = .success (.solved solved) :=
  prepared_witness_shape_complete hw ⟨unitShapes, residual_unitShapes hR⟩

end ModalityInference.ComparisonSkeleton
