import ModalityInference.HornPropagation
import ModalityInference.CNFPropagation

/-! Modality consistency by finite constraint propagation.

The polarized domain uses direct Horn propagation. The unrestricted public
constraint API uses ordered Boolean bound elimination, whose intermediate
representation may be exponential. Neither path guesses assignments, and both
construct witnesses separately from the symbolic solution and residual bounds.
-/
namespace ModalityInference.ModeConsistency

/-- General-domain compatibility: eliminate each Boolean atom by crossing all
of its lower and upper bounds, then reconstruct a witness in reverse order. -/
def general (fuel : Nat) (cs : Bounds) : RunResult ModeAssignment := do
  let clauses ← toCNF fuel true (boundsModeFormula cs)
  let assignment ← CNFPropagation.solve fuel clauses
  return ModeAssignment.ofBooleans cs (CNFPropagation.valuation assignment)

/-- Recognize the projected polarized grammar before choosing its direct path. -/
def isPolarized (cs : Bounds) : Bool :=
  let e := boundsModeFormula cs
  (HornPropagation.horn (HornPropagation.domain e) e).isSome

def solve (fuel : Nat) (cs : Bounds) : RunResult ModeAssignment :=
  if isPolarized cs then HornPropagation.satisfiableModes fuel cs
  else general fuel cs

end ModalityInference.ModeConsistency

namespace ModalityInference

/-- Public modality consistency uses propagation; search is only an optional oracle. -/
def satisfiableModes := ModeConsistency.solve

end ModalityInference
