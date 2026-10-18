import ModalityInference.ComparisonShapeSolver
import ModalityInference.ComparisonShapeCandidates

/-! Input anchors and the finite source-shape choice family. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonShapeSolver

def anchorNames (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved) : List TypeVar :=
  solved.fixed.map Prod.fst ++
    (ComparisonShape.pairs p.assumptions ++ sourcePairs p).flatMap
      (fun (a, b) => a.vars ++ b.vars)

def anchorTemplates (p : SchemePreparation.Prepared) : List ComparisonShape :=
  ComparisonShape.declaredTemplates p.assumptions ++ [ComparisonShape.ofTy p.targetType]

def shapeChoices (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved) : List ComparisonShape :=
  ComparisonShape.candidates (anchorNames p solved) solved.fixedShapes (anchorTemplates p)

end ModalityInference.ComparisonShapeRetraction
