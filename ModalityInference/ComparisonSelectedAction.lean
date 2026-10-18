import ModalityInference.ComparisonSelectedReification

/-! Reconstruct all selected type images with the same shape assignment and
modality action. The input key list, including duplicates, is retained exactly. -/
namespace ModalityInference.ComparisonSelectedBases

def reifyEntries (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (modes : ModVar → ModExpr) : List (Nat × CNF) → Option (List (Nat × CompareTy))
  | [] => some []
  | (n,clauses) :: rest => do
      let type ← reifyClosedImage first p solved world modes (.flex n) clauses
      let tail ← reifyEntries first p solved world modes rest
      return (n,type) :: tail

def reifyAction (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (modes : List (Nat × ModExpr)) (entries : List (Nat × CNF)) : Option CompareSubstitution := do
  let types ← reifyEntries first p solved world ({modes := modes} : CompareSubstitution).mode entries
  return ⟨types,modes⟩

end ModalityInference.ComparisonSelectedBases
