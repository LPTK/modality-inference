import ModalityInference.ComparisonSelectedBases
import ModalityInference.ComparisonShapeSelectorMatches

/-! Fixed input names and the target body constrain the common source-shape
selectors without introducing new type or modality assumptions. -/
namespace ModalityInference.ComparisonSelectedBases

/-- Source shape choices retain the unquantified input names and match the
whole target body after the declared equations have been resolved. -/
def anchorEquations (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved) :
    List (ComparisonShape × ComparisonShape) :=
  ((inputNames p).filter fun v => v.index < p.firstType).map
    (fun v => (solved.resolveAll v, solved.fixedShapes v)) ++
  [((ComparisonShape.ofTy p.sourceType).subst solved.resolveAll,
    (ComparisonShape.ofTy p.targetType).subst solved.fixedShapes)]

def anchorTheory (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : BoolExpr :=
  (layout first p solved).matchTheory solved.fixedShapes (anchorEquations p solved)

end ModalityInference.ComparisonSelectedBases
