import ModalityInference.ModalSynthesis
import ModalityInference.SymbolicSchemeModes

/-! Finite scheme-comparison modality witnesses. Every selected variable contributes
all three coordinates, including coordinates absent from the input formula. -/
namespace ModalityInference.SchemeModeSynthesis

def atoms (modeIds : List Nat) : List Nat :=
  modeIds.flatMap fun n => (List.range 3).map (ModVar.atomIndex (.flex n))

def parameters (modeIds : List Nat) : List (Nat × ModVar) :=
  modeIds.map fun n => (n, .flex n)

structure Result where
  substitution : Substitution
  flexibleAtoms : List Nat
  query : BoolExpr

/-- The input formula already contains the rigid assumptions and all guards. The
returned finite substitution has exactly the requested fresh modality domain. -/
def run (fuel : Nat) (modeIds : List Nat) (formula : BoolExpr) : RunResult Result := do
  let flexibleAtoms := atoms modeIds
  let images ← ModalSynthesis.synthesize fuel flexibleAtoms formula
  match SymbolicSchemeModes.assemble images (parameters modeIds) with
  | none => .rejected "internal error: symbolic modality witness could not be assembled"
  | some substitution =>
      return ⟨substitution, flexibleAtoms, SymbolicCNF.substitute images.substitute formula⟩

end ModalityInference.SchemeModeSynthesis
