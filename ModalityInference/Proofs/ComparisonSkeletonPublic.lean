import ModalityInference.Proofs.ComparisonSkeletonRebase

namespace ModalityInference.ComparisonSkeletonCoordinates

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeleton ComparisonShapeSolver

/-- Renaming compatible opaque shape classes does not change any extracted
coordinate expression or the reified witness. -/
theorem normalize_reify_shape_independent {Δ : Bounds} (hΔ : Residual Δ)
    (s t : ComparisonShape) (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (es : ComparisonShape.Equivalent Δ a.shape s) (et : ComparisonShape.Equivalent Δ a.shape t) :
    (normalize hΔ s a hs hd es).reify = (normalize hΔ t a hs hd et).reify := by
  induction s generalizing t a with
  | var v =>
    cases t <;> try rfl
    all_goals have hh := rootTag_equivalent hΔ (es.symm.trans et)
    all_goals simp only [rootTag] at hh; omega
  | unit =>
    cases t <;> try rfl
    all_goals have hh := rootTag_equivalent hΔ (es.symm.trans et)
    all_goals simp only [rootTag] at hh; omega
  | credit =>
    cases t <;> try rfl
    all_goals have hh := rootTag_equivalent hΔ (es.symm.trans et)
    all_goals simp only [rootTag] at hh; omega
  | prod s₁ s₂ ih₁ ih₂ | sum s₁ s₂ ih₁ ih₂ | fn s₁ s₂ ih₁ ih₂ =>
    cases t
    all_goals try
      have hh := rootTag_equivalent hΔ (es.symm.trans et)
      simp only [rootTag] at hh
      omega
    all_goals dsimp only [normalize, Tree.reify]
    all_goals congr 2
    all_goals first | apply ih₁ | apply ih₂

theorem normalize_public_at {Δ : Bounds} (hΔ : Residual Δ) (a : Ty)
    (ha : (CompareTy.ofTy a).DefinedUnder Δ) (s : ComparisonShape)
    (he : ComparisonShape.Equivalent Δ (CompareTy.ofTy a).shape s) :
    let tree := normalize hΔ s (.ofTy a) (CompareTy.wellShaped_ofTy a Δ) ha he
    AlgebraSubtype Δ tree.reify (.ofTy a) ∧ AlgebraSubtype Δ (.ofTy a) tree.reify := by
  dsimp only
  rw [normalize_reify_shape_independent hΔ s (ComparisonShape.ofTy a) _ _ _ he
    (by rw [CompareTy.shape_ofTy]; exact .refl)]
  exact normalize_public_correct hΔ a ha

theorem rebase_public_at {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ) (a : Ty)
    (ha : (CompareTy.ofTy a).DefinedUnder Δ) (s : ComparisonShape) (hf : FixedShape p s)
    (he : ComparisonShape.Equivalent Δ (CompareTy.ofTy a).shape (s.subst ρ)) :
    let tree := rebase hΔ p ρ hρ s (.ofTy a) (CompareTy.wellShaped_ofTy a Δ) ha he
    AlgebraSubtype Δ tree.reify (.ofTy a) ∧ AlgebraSubtype Δ (.ofTy a) tree.reify := by
  dsimp only
  rw [rebase_fixed_reify hΔ p ρ hρ s hf]
  exact normalize_public_at hΔ a ha s _

end ModalityInference.ComparisonSkeletonCoordinates
