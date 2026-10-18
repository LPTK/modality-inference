import ModalityInference.ComparisonShapes

/-! Finite structural shapes obtained from fixed input anchors. The unit shape
also permits an absorbing default when no declared endpoint can be encountered. -/

namespace ModalityInference.ComparisonShape

/-- Every subtree, including the root. Repetitions retain a linear traversal. -/
def subshapes (s : ComparisonShape) : List ComparisonShape :=
  s :: match s with
    | .var _ | .unit | .credit => []
    | .prod a b | .sum a b | .fn a b => a.subshapes ++ b.subshapes

/-- Candidate shapes from declared fixed names and fixed structural templates. -/
def candidates (names : List TypeVar) (fixed : TypeVar → ComparisonShape)
    (templates : List ComparisonShape) : List ComparisonShape :=
  .unit :: (names.map fixed ++ templates.map (subst fixed)).flatMap subshapes

/-- Whole declared endpoints are anchors even when they contain constructors. -/
def declaredTemplates (Δ : Bounds) : List ComparisonShape :=
  (pairs Δ).flatMap fun (a, b) => [a, b]

/-- Retain anchored choices and default every other parameter simultaneously. -/
def select (names : List TypeVar) (fixed : TypeVar → ComparisonShape)
    (templates : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (v : TypeVar) : ComparisonShape :=
  if (candidates names fixed templates).contains (ρ v) then ρ v else .unit

end ModalityInference.ComparisonShape
