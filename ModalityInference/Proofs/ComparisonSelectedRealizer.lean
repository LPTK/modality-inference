import ModalityInference.Proofs.ComparisonSelectedPreparation

namespace ModalityInference.ComparisonShapeRetraction

open ComparisonShapeSolver ComparisonSkeleton ComparisonWitnessRestriction

private theorem pairNames_mem {ps : Pairs} {v : TypeVar} :
    v ∈ ps.flatMap (fun (a, b) => a.vars ++ b.vars) ↔ v ∈ Measure.vars ps := by
  simp only [List.mem_flatMap, List.mem_append, Prod.exists, Measure.mem_vars]

theorem input_mem_anchorNames (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) {v : TypeVar} (hv : v ∈ inputTypes p) :
    v ∈ anchorNames p solved := by
  apply List.mem_append_right
  apply pairNames_mem.mpr
  simp only [inputTypes, Finset.mem_union] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · obtain ⟨a, b, hab, hv⟩ := (Measure.mem_vars _ _).mp ((vars_pairs _).symm ▸ hv)
    exact (Measure.mem_vars _ _).mpr ⟨a, b, List.mem_append_left _ hab, hv⟩
  · obtain ⟨a, b, hab, hv⟩ := (Measure.mem_vars _ _).mp ((vars_pairs _).symm ▸ hv)
    exact (Measure.mem_vars _ _).mpr
      ⟨a, b, List.mem_append_right _ (List.mem_append_left _ hab), hv⟩
  · exact (Measure.mem_vars _ _).mpr
      ⟨_, _, List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self)),
        Or.inl ((mem_vars_ofTy _ _).mpr hv)⟩
  · exact (Measure.mem_vars _ _).mpr
      ⟨_, _, List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self)),
        Or.inr ((mem_vars_ofTy _ _).mpr hv)⟩

theorem normalizedRealizer_type_shape {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (v : TypeVar) (hv : v.index < (SchemePreparation.prepare ambient source target).nextType) :
    let p := SchemePreparation.prepare ambient source target
    (σ.type v).shape.subst solved.fixedShapes =
      (solved.resolveAll v).subst (normalizedRealizer p σ solved) := by
  have he := normalizedRealizer_realizes h hw v hv solved.fixedShapes
    (unify_sound (prepare_solved_iff.mp h).1)
  simpa only [subst_values_fixed _ (normalizedRealizer_fixed h σ)] using he

theorem normalizedRealizer_ty_shape {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (t : Ty) (ht : ∀ v ∈ t.typeVars,
      v.index < (SchemePreparation.prepare ambient source target).nextType) :
    let p := SchemePreparation.prepare ambient source target
    (σ.ty t).shape.subst solved.fixedShapes =
      ((ComparisonShape.ofTy t).subst solved.resolveAll).subst (normalizedRealizer p σ solved) := by
  dsimp only
  simp only [σ.ty_shape, subst_comp]
  exact subst_congr _ (fun v hv => normalizedRealizer_type_shape h hw v
    (ht v ((mem_vars_ofTy t v).mp hv)))

theorem prepared_template_valid {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : prepare fuel p = .success (.solved solved)) (σ : CompareSubstitution)
    (s : ComparisonShape) :
    (Cut.ofTemplate (shapeChoices p solved) (normalizedRealizer p σ solved) s).Valid
      p.assumptions solved.fixedShapes := by
  apply Cut.ofTemplate_valid (unify_sound (prepare_solved_iff.mp h).1)
  · intro entry he
    exact List.mem_append_left _ (List.mem_map.mpr ⟨entry, he, rfl⟩)
  · intro a b hab
    exact List.mem_append_left _ (ComparisonShape.sub_left_mem_declaredTemplates hab)
  · exact normalizedRealizer_fixed h σ

theorem retained_source_body {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitness (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    retained (shapeChoices p solved) (normalizedRealizer p σ solved)
      ((ComparisonShape.ofTy p.sourceType).subst solved.resolveAll) = true := by
  let p := SchemePreparation.prepare ambient source target
  have hr := normalizedRealizer_ty_shape h hw p.sourceType
    (((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceType_bounded ambient source target)).1)
  have hb := hw.2.2.2.shape_equivalent solved.fixedShapes (unify_sound (prepare_solved_iff.mp h).1)
  rw [CompareTy.shape_ofTy] at hb
  apply retained_iff.mpr
  intro v hv
  exact ComparisonShape.matching_template_candidate hv
    (List.mem_append_right _ (List.mem_cons_self)) (hr.symm.trans hb)

theorem retained_variable_image {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (v : TypeVar) (hv : v.index < (SchemePreparation.prepare ambient source target).nextType)
    (hn : v ∈ inputTypes (SchemePreparation.prepare ambient source target))
    (he : σ.type v = .var v) :
    let p := SchemePreparation.prepare ambient source target
    retained (shapeChoices p solved) (normalizedRealizer p σ solved) (solved.resolveAll v) = true := by
  have hr := normalizedRealizer_type_shape h hw v hv
  rw [he] at hr
  apply retained_iff.mpr
  intro w hw'
  exact ComparisonShape.matching_fixed_candidate hw'
    (input_mem_anchorNames _ solved hn) hr.symm

end ModalityInference.ComparisonShapeRetraction
