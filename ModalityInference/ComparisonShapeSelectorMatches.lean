import ModalityInference.ComparisonShapeSelectors

/-! Shared selectors retain prescribed input shapes through guarded matches
of their finite structural branches. -/
namespace ModalityInference.ComparisonShapeSelectors

/-- Match a selected template after resolving the declared shape equations. -/
def Layout.matches (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (template target : ComparisonShape) : BoolExpr :=
  .any ((layout.branches template).map fun branch =>
    if branch.shape.subst fixed == target then branch.guard else .const false)

def Layout.matchesAll (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape)) : BoolExpr :=
  .all (equations.map fun pair => layout.matches fixed pair.1 pair.2)

def Layout.matchTheory (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape)) : BoolExpr :=
  .and layout.theory (layout.matchesAll fixed equations)

def Layout.compileMatches (layout : Layout) (fuel : Nat) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape)) : RunResult CNF :=
  CompactCNF.toCNF fuel true (layout.matchTheory fixed equations)

end ModalityInference.ComparisonShapeSelectors
