import ModalityInference.ComparisonInputAction
import ModalityInference.ComparisonSignedObservation
import ModalityInference.ComparisonStructuralEndpoints

/-! Public endpoint pairs for the signed structural comparison. Whole declared
edges and required source comparisons retain their original syntax. -/
namespace ModalityInference.ComparisonSignedObservation

def declaredEndpoints (p : SchemePreparation.Prepared) : List (Ty × Ty) :=
  p.assumptions.filterMap fun c => match c with
    | .sub a b => some (a,b)
    | _ => none

def sourceEndpoints (p : SchemePreparation.Prepared) : List (Ty × Ty) :=
  p.sourceBounds.flatMap ComparisonStructuralEndpoints.constraintPairs ++
    [(p.sourceType,p.targetType)]

def endpoints (p : SchemePreparation.Prepared) : List (Ty × Ty) :=
  declaredEndpoints p ++ sourceEndpoints p

end ModalityInference.ComparisonSignedObservation
