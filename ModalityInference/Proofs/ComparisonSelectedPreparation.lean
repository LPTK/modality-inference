import ModalityInference.ComparisonSelectedPreparation
import ModalityInference.Proofs.ComparisonShapeSelection
import ModalityInference.Proofs.ComparisonStructuralPrepared

/-! Actual prepared witnesses supply normalized shape choices and finite input
anchors. The target body is retained as a whole, including partial annotations. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonShapeSolver ComparisonSkeleton ComparisonWitnessRestriction

def normalizedRealizer (p : SchemePreparation.Prepared) (σ : CompareSubstitution)
    (solved : ComparisonShapeSolver.Solved) (v : TypeVar) : ComparisonShape :=
  (shapeRealizer p σ solved.fixedShapes v).subst solved.fixedShapes

theorem fixedShapes_idempotent {fuel : Nat} {p : SchemePreparation.Prepared} {solved : ComparisonShapeSolver.Solved}
    (h : prepare fuel p = .success (.solved solved)) (s : ComparisonShape) :
    (s.subst solved.fixedShapes).subst solved.fixedShapes = s.subst solved.fixedShapes := by
  rw [subst_comp]
  exact subst_congr s (fun v _ => unify_factor (prepare_solved_iff.mp h).1
    (unify_sound (prepare_solved_iff.mp h).1) v)

theorem normalizedRealizer_fixed {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} (h : prepare fuel p = .success (.solved solved))
    (σ : CompareSubstitution) (v : TypeVar) :
    (normalizedRealizer p σ solved v).subst solved.fixedShapes =
      normalizedRealizer p σ solved v := fixedShapes_idempotent h _

theorem normalizedRealizer_realizes {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitness (SchemePreparation.prepare ambient source target) σ)
    (v : TypeVar) (hv : v.index < (SchemePreparation.prepare ambient source target).nextType) :
    let p := SchemePreparation.prepare ambient source target
    ComparisonShape.Equivalent p.assumptions (σ.type v).shape
      ((solved.resolveAll v).subst (normalizedRealizer p σ solved)) := by
  have hr := (prepared_witness_shape_realizer h hw).2 v hv
  simpa only [subst_comp, normalizedRealizer] using hr.trans (fixedShapes_equivalent h _)

end ModalityInference.ComparisonShapeRetraction
