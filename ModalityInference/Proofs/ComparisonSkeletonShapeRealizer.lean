import ModalityInference.Proofs.ComparisonSkeletonPublic
import ModalityInference.Proofs.ComparisonPreparationComplete
import ModalityInference.Proofs.ComparisonPreparedBounds

namespace ModalityInference.ComparisonSkeleton

open ComparisonShapeSolver ComparisonPreparation

def witnessShape (σ : CompareSubstitution) (φ : TypeVar → ComparisonShape)
    (v : TypeVar) : ComparisonShape := (σ.type v).shape.subst φ

theorem algebra_bounds_shape_model {Δ : Bounds} (σ : CompareSubstitution) (cs : Bounds)
    (hc : AlgebraEntailsAll Δ (σ.bounds cs)) {φ : TypeVar → ComparisonShape}
    (hφ : ComparisonShape.Models Δ φ) :
    ComparisonShapeSolver.Models (ComparisonShape.pairs cs) (witnessShape σ φ) := by
  intro pair hp
  obtain ⟨c, hmem, hp⟩ := List.mem_flatMap.mp hp
  have hh := hc (σ.constraint c) (List.mem_map.mpr ⟨c, hmem, rfl⟩)
  cases c with
  | sub a b =>
    simp only [List.mem_singleton] at hp
    subst pair
    simpa only [σ.ty_shape, subst_comp, witnessShape] using hh.1.shape_equivalent φ hφ
  | equiv a b =>
    simp only [List.mem_singleton] at hp
    subst pair
    simpa only [σ.ty_shape, subst_comp, witnessShape] using hh.1.shape_equivalent φ hφ
  | equal v a =>
    simp only [List.mem_singleton] at hp
    subst pair
    have he := ((σ.algebra_equal_iff Δ v a).mp hh).1.1.shape_equivalent φ hφ
    simpa only [σ.ty_shape, subst_comp, witnessShape, ComparisonShape.subst] using he
  | mode m n | defined m => simp at hp

theorem prepared_witness_shape_model {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : PreparedWitness p σ) {φ : TypeVar → ComparisonShape}
    (hφ : ComparisonShape.Models p.assumptions φ)
    (ht : ∀ v ∈ p.targetType.typeVars, σ.type v = .var v) :
    ComparisonShapeSolver.Models (sourcePairs p) (witnessShape σ φ) := by
  intro pair hp
  rcases List.mem_append.mp hp with hp | hp
  · exact algebra_bounds_shape_model σ p.sourceBounds h.2.2.1 hφ pair hp
  · simp only [List.mem_singleton] at hp
    subst pair
    have he := h.2.2.2.shape_equivalent φ hφ
    rw [σ.ty_shape, subst_comp, CompareTy.shape_ofTy] at he
    refine he.trans ?_
    exact subst_congr _ (fun v hv => by
      rw [witnessShape, ht v ((mem_vars_ofTy _ _).mp hv)]
      rfl)

def shapeRealizer (p : SchemePreparation.Prepared) (σ : CompareSubstitution)
    (φ : TypeVar → ComparisonShape) (v : TypeVar) : ComparisonShape :=
  if sourceAllowed p v then witnessShape σ φ v else .var v

theorem shapeRealizer_fixes (p : SchemePreparation.Prepared) (σ : CompareSubstitution)
    (φ : TypeVar → ComparisonShape) : Fixes (sourceAllowed p) (shapeRealizer p σ φ) := by
  intro v hv
  simp [shapeRealizer, hv]

theorem fixedShapes_realizer {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) (σ : CompareSubstitution) (v : TypeVar)
    (hv : sourceAllowed p v = false → σ.type v = .var v) :
    (solved.fixedShapes v).subst (shapeRealizer p σ solved.fixedShapes) =
      witnessShape σ solved.fixedShapes v := by
  obtain ⟨hfixed, himages⟩ := unify_support (prepare_solved_iff.mp h).1
    (Measure.vars (ComparisonShape.pairs p.assumptions)) Finset.Subset.rfl
  by_cases ha : sourceAllowed p v = true
  · have hn : v ∉ Measure.vars (ComparisonShape.pairs p.assumptions) := by
      intro hm
      exact Bool.noConfusion (ha.symm.trans (hscope v hm))
    change (action solved.fixed v).subst _ = _
    rw [hfixed v hn]
    simp [ComparisonShape.subst, shapeRealizer, ha]
  · have ha : sourceAllowed p v = false := Bool.eq_false_iff.mpr ha
    rw [witnessShape, hv ha]
    change (solved.fixedShapes v).subst _ = solved.fixedShapes v
    refine (subst_congr _ ?_).trans (subst_id _)
    intro w hw
    have haw : sourceAllowed p w = false := by
      by_cases hmem : v ∈ Measure.vars (ComparisonShape.pairs p.assumptions)
      · exact hscope w (himages v hmem (List.mem_toFinset.mpr hw))
      · change w ∈ (action solved.fixed v).vars at hw
        rw [hfixed v hmem] at hw
        have he : w = v := by simpa [ComparisonShape.vars] using hw
        exact he ▸ ha
    exact shapeRealizer_fixes p σ solved.fixedShapes w haw

theorem shapeRealizer_model {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) (σ : CompareSubstitution)
    (hm : ComparisonShapeSolver.Models (sourcePairs p) (witnessShape σ solved.fixedShapes))
    (hf : ∀ v ∈ Measure.vars (sourcePairs p), sourceAllowed p v = false → σ.type v = .var v) :
    ComparisonShapeSolver.Models (mapPairs solved.fixedShapes (sourcePairs p))
      (shapeRealizer p σ solved.fixedShapes) := by
  apply (models_mapPairs _ _ _).mpr
  intro pair hp
  have he (side : ComparisonShape) (hh : ∀v∈side.vars, v ∈ Measure.vars (sourcePairs p)) :
      side.subst (fun v => (solved.fixedShapes v).subst (shapeRealizer p σ solved.fixedShapes)) =
        side.subst (witnessShape σ solved.fixedShapes) :=
    subst_congr side (fun v hv => fixedShapes_realizer h hscope σ v (hf v (hh v hv)))
  exact (he pair.1 (fun v hv => (Measure.mem_vars _ _).mpr ⟨pair.1, pair.2, hp, .inl hv⟩)).trans
    ((hm pair hp).trans (he pair.2
      (fun v hv => (Measure.mem_vars _ _).mpr ⟨pair.1, pair.2, hp, .inr hv⟩)).symm)

theorem fixedShapes_equivalent {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (s : ComparisonShape) : ComparisonShape.Equivalent p.assumptions s (s.subst solved.fixedShapes) := by
  intro η hη
  rw [subst_comp]
  symm
  exact subst_congr s (fun v _ => unify_factor (prepare_solved_iff.mp h).1 hη v)

theorem shapeRealizer_resolves {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) (σ : CompareSubstitution)
    (hm : ComparisonShapeSolver.Models (sourcePairs p) (witnessShape σ solved.fixedShapes))
    (hf : ∀ v ∈ Measure.vars (sourcePairs p), sourceAllowed p v = false → σ.type v = .var v)
    {v : TypeVar} (hv : sourceAllowed p v = true) :
    ComparisonShape.Equivalent p.assumptions (σ.type v).shape
      ((solved.resolveAll v).subst (shapeRealizer p σ solved.fixedShapes)) := by
  rw [prepare_resolve_source h hscope hv,
    unify_factor (prepare_solved_iff.mp h).2 (shapeRealizer_model h hscope σ hm hf) v]
  simp only [shapeRealizer, hv, ↓reduceIte, witnessShape]
  exact fixedShapes_equivalent h _

theorem shapeRealizer_realizes {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) (σ : CompareSubstitution)
    (hm : ComparisonShapeSolver.Models (sourcePairs p) (witnessShape σ solved.fixedShapes))
    (hf : ∀ v ∈ Measure.vars (sourcePairs p), sourceAllowed p v = false → σ.type v = .var v)
    (v : TypeVar) (hv : sourceAllowed p v = false → σ.type v = .var v) :
    ComparisonShape.Equivalent p.assumptions (σ.type v).shape
      ((solved.resolveAll v).subst (shapeRealizer p σ solved.fixedShapes)) := by
  have hr : (solved.resolveAll v).subst (shapeRealizer p σ solved.fixedShapes) =
      (σ.type v).shape.subst solved.fixedShapes := by
    dsimp only [Solved.resolveAll]
    rw [subst_comp]
    exact (subst_congr _ (fun w _ =>
      unify_factor (prepare_solved_iff.mp h).2 (shapeRealizer_model h hscope σ hm hf) w)).trans
        (fixedShapes_realizer h hscope σ v hv)
  rw [hr]
  exact fixedShapes_equivalent h _

theorem prepared_sourcePairs_bounded (ambient : Bounds) (source target : Scheme)
    {v : TypeVar} (hv : v ∈ Measure.vars (sourcePairs (SchemePreparation.prepare ambient source target))) :
    v.index < (SchemePreparation.prepare ambient source target).nextType := by
  obtain ⟨a, b, hp, hv⟩ := (Measure.mem_vars _ _).mp hv
  rcases List.mem_append.mp hp with hp | hp
  · have hm := (Measure.mem_vars _ _).mpr ⟨a, b, hp, hv⟩
    rw [vars_pairs] at hm
    exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).1 v hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rcases hv with hv | hv
    · exact ((TypeExpr.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_sourceType_bounded ambient source target)).1 v
          ((mem_vars_ofTy _ _).mp hv)
    · exact ((TypeExpr.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_targetType_bounded ambient source target)).1 v
          ((mem_vars_ofTy _ _).mp hv)

theorem prepared_witness_fixed {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (h : PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (v : TypeVar) (hv : v.index < (SchemePreparation.prepare ambient source target).nextType)
    (ha : sourceAllowed (SchemePreparation.prepare ambient source target) v = false) :
    σ.type v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    apply h.1.type_fixed
    simp only [sourceAllowed, Bool.and_eq_false_iff, decide_eq_false_iff_not,
      not_le, not_lt, TypeVar.index] at ha hv ⊢
    omega

/-- Every prepared witness realizes the actual solved templates. Remaining
source shape variables are parameters, while declared shape classes stay fixed. -/
theorem prepared_witness_shape_realizer {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved))
    (hw : PreparedWitness (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    let ρ := shapeRealizer p σ solved.fixedShapes
    Fixes (sourceAllowed p) ρ ∧
      ∀ v, v.index < p.nextType → ComparisonShape.Equivalent p.assumptions (σ.type v).shape
        ((solved.resolveAll v).subst ρ) := by
  refine ⟨shapeRealizer_fixes _ _ _, ?_⟩
  intro v hv
  apply shapeRealizer_realizes h (prepared_assumptions_fixed ambient source target) σ
  · exact prepared_witness_shape_model hw (unify_sound (prepare_solved_iff.mp h).1)
      (fun v hv => hw.1.type_fixed v (((TypeExpr.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_targetType_bounded_first ambient source target)).1 v hv))
  · exact fun v hv => prepared_witness_fixed hw v (prepared_sourcePairs_bounded ambient source target hv)
  · exact prepared_witness_fixed hw v hv

end ModalityInference.ComparisonSkeleton
