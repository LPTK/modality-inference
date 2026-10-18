import ModalityInference.ComparisonShapeSelectors
import ModalityInference.ComparisonSelectedPreparation
import ModalityInference.ComparisonStructuralBasis

/-! Guarded structural bases for one shared finite choice of source shapes. -/
namespace ModalityInference.ComparisonSelectedBases

open ComparisonShapeSelectors ComparisonShapeRetraction ComparisonControls

def inputNames (p : SchemePreparation.Prepared) : List TypeVar :=
  (p.assumptions.typeVariables ++ p.sourceBounds.typeVariables ++
    p.sourceType.typeVariables ++ p.targetType.typeVariables).dedup

def inputModes (p : SchemePreparation.Prepared) : List ModVar :=
  (p.assumptions.modeVariables ++ p.sourceBounds.modeVariables ++
    p.sourceType.modeVariables ++ p.targetType.modeVariables).dedup

def layout (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : Layout :=
  ofTemplates first (shapeChoices p solved) ((anchorNames p solved).map solved.resolveAll)

structure Branch where
  shape : ComparisonShape
  guard : BoolExpr
  basis : Basis
  deriving Repr

/-- Only branches with a nonempty common-shape basis contribute to a type image. -/
def bases (layout : Layout) (names : List TypeVar) (modes : List ModVar)
    (fixed : TypeVar → ComparisonShape) (s : ComparisonShape) : List Branch :=
  (layout.branches s).filterMap fun branch =>
    (ComparisonStructuralBasis.basis names modes fixed (branch.shape.subst fixed)).map fun b =>
      ⟨branch.shape.subst fixed, branch.guard, b⟩

def prepared (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (v : TypeVar) : List Branch :=
  bases (layout first p solved) (inputNames p) (inputModes p) solved.fixedShapes (solved.resolveAll v)

end ModalityInference.ComparisonSelectedBases
