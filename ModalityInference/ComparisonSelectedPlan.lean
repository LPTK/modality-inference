import ModalityInference.ComparisonSelectedMatches

/-! A finite selector plan retains the input anchor equations and requires an
inhabited structural basis for every selected input shape. -/
namespace ModalityInference.ComparisonSelectedBases

structure Plan where
  selectors : ComparisonShapeSelectors.Layout
  branches : List (TypeVar × List Branch)
  clauses : CNF
  deriving Repr

def branchEntries (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : List (TypeVar × List Branch) :=
  (inputNames p).map fun v => (v, prepared first p solved v)

def branchCoverage (entries : List (TypeVar × List Branch)) : BoolExpr :=
  .all (entries.map fun entry => .any (entry.2.map Branch.guard))

def selectorFormula (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : BoolExpr :=
  .and (anchorTheory first p solved) (branchCoverage (branchEntries first p solved))

def compilePlan (fuel first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : RunResult Plan := do
  let clauses ← CompactCNF.toCNF fuel true (selectorFormula first p solved)
  pure ⟨layout first p solved, branchEntries first p solved, clauses⟩

end ModalityInference.ComparisonSelectedBases
