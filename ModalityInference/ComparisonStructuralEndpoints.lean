import ModalityInference.ComparisonSelectedBases
import ModalityInference.ComparisonStructuralNormalization

/-! Whole declared and required type inequalities remain intact when assigned
to structural nodes. Equalities contribute their two directed obligations. -/
namespace ModalityInference.ComparisonStructuralEndpoints

def constraintPairs : Constraint → List (Ty × Ty)
  | .sub a b => [(a, b)]
  | .equal v a => [(.var v, a), (a, .var v)]
  | .equiv a b => [(a, b), (b, a)]
  | .mode _ _ | .defined _ => []

def source (p : SchemePreparation.Prepared) (action : CompareSubstitution) :
    List (CompareTy × CompareTy) :=
  (p.sourceBounds.flatMap constraintPairs).map (fun pair =>
    (action.ty pair.1, action.ty pair.2)) ++
  [(action.ty p.sourceType, .ofTy p.targetType)]

def declared (p : SchemePreparation.Prepared) : List (CompareTy × CompareTy) :=
  p.assumptions.filterMap fun c => match c with
    | .sub a b => some (.ofTy a, .ofTy b)
    | _ => none

def all (p : SchemePreparation.Prepared) (action : CompareSubstitution) :
    List (CompareTy × CompareTy) :=
  declared p ++ source p action

structure Pair where
  shape : ComparisonShape
  left : CompareTy
  right : CompareTy
  deriving Repr

def atShape (pairs : List Pair) (shape : ComparisonShape) : List (CompareTy × CompareTy) :=
  pairs.filterMap fun pair =>
    if pair.shape == shape then some (pair.left, pair.right) else none

def normalizePair (fuel : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (pair : CompareTy × CompareTy) : RunResult Pair := do
  let left ← ComparisonStructuralNormalization.run fuel (ComparisonSelectedBases.inputNames p)
    (ComparisonSelectedBases.inputModes p) solved.fixedShapes pair.1
  let right ← ComparisonStructuralNormalization.run fuel (ComparisonSelectedBases.inputNames p)
    (ComparisonSelectedBases.inputModes p) solved.fixedShapes pair.2
  return ⟨pair.1.shape.subst solved.fixedShapes, left, right⟩

def normalizeList (fuel : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : List (CompareTy × CompareTy) → RunResult (List Pair)
  | [] => .success []
  | pair :: rest => do
      return (← normalizePair fuel p solved pair) :: (← normalizeList fuel p solved rest)

def run (fuel : Nat) (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (action : CompareSubstitution) : RunResult (List Pair) :=
  normalizeList fuel p solved (all p action)

end ModalityInference.ComparisonStructuralEndpoints
