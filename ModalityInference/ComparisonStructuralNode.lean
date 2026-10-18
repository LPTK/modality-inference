import ModalityInference.ComparisonLatticeCompiler

/-! A structural node retains each declared endpoint pair as one implication.
Its signed-control equations and whole-type constraints share one namespace. -/
namespace ModalityInference.ComparisonStructuralNode

open ComparisonControls

structure Bound where
  left : CNF
  right : CNF
  deriving Repr

def prepare (basis : Basis) : List (CompareTy × CompareTy) → Option (List Bound)
  | [] => some []
  | (left, right) :: rest => do
      let lower ← ComparisonLatticeCompiler.compile basis left
      let upper ← ComparisonLatticeCompiler.compile basis right
      let tail ← prepare basis rest
      return ⟨lower, upper⟩ :: tail

def clauses (basisAtom : Nat → Nat) (bounds : List Bound) : CNF :=
  bounds.flatMap fun bound =>
    ComparisonPropagation.rename basisAtom (ComparisonPropagation.implies bound.left bound.right)

def compile (fuel : Nat) (basis : Basis) (basisAtom headAtom modeAtom : Nat → Nat)
    (coordinate : Coordinate) (bounds : List Bound) : RunResult CNF := do
  let controls ← CompactCNF.toCNF fuel true (basis.theoryAt basisAtom headAtom modeAtom coordinate)
  return controls ++ clauses basisAtom bounds

def run (fuel : Nat) (basis : Basis) (basisAtom headAtom modeAtom : Nat → Nat)
    (coordinate : Coordinate) (input : List (CompareTy × CompareTy)) : RunResult CNF :=
  match prepare basis input with
  | none => .rejected "structural endpoint is outside its finite lattice basis"
  | some bounds => compile fuel basis basisAtom headAtom modeAtom coordinate bounds

end ModalityInference.ComparisonStructuralNode
