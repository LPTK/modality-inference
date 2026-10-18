import ModalityInference.ComparisonSelectedBases
import ModalityInference.ComparisonPropagation

/-! Reconstruct a type polynomial from the basis selected by the common shape
assignment, then apply the common modality substitution to its annotations. -/
namespace ModalityInference.ComparisonSelectedBases

def enabled (world : Nat → Bool) : List Branch → Option Branch
  | [] => none
  | b :: bs => if b.guard.eval world then some b else enabled world bs

def reifyImage (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (v : TypeVar) (clauses : CNF) : Option CompareTy := do
  let branch ← enabled world (prepared first p solved v)
  ComparisonPropagation.reify branch.basis.types clauses

def reifyClosedImage (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (modes : ModVar → ModExpr) (v : TypeVar) (clauses : CNF) : Option CompareTy :=
  (reifyImage first p solved world v clauses).map (fun t => t.subst CompareTy.var modes)

end ModalityInference.ComparisonSelectedBases
