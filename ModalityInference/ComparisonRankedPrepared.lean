import ModalityInference.ComparisonRankedDecision
import ModalityInference.ComparisonPreparedScalar
import ModalityInference.ComparisonPreparation
import ModalityInference.ComparisonInputAction
import ModalityInference.ComparisonObserverBoundary
import ModalityInference.ModeBackend

/-! Guarded prepared comparison at one supplied constructor rank and one
shared finite modality action. Guards are checked against the original bounds;
the observer count is computed from the input and the supplied rank. -/
namespace ModalityInference.ComparisonRankedPrepared

open ComparisonSelectedBases ComparisonRankedBasis ComparisonRankedDecision

def imageBasis (p : SchemePreparation.Prepared) (rank : Nat) : ComparisonControls.Basis :=
  basis (inputNames p) (inputModes p) rank

def endpoints (p : SchemePreparation.Prepared) : List (Ty × Ty) :=
  ComparisonSignedObservation.endpoints p

def generators (p : SchemePreparation.Prepared) (rank : Nat) : List CompareTy :=
  (imageBasis p (rank + endpointRank (endpoints p))).types

def typeNames (p : SchemePreparation.Prepared) (rank : Nat) : List TypeVar :=
  ComparisonObserverBoundary.retainedTypes p.assumptions (generators p rank)

def modeNames (p : SchemePreparation.Prepared) (rank : Nat) : List ModVar :=
  ComparisonObserverBoundary.retainedModes p.assumptions (generators p rank)

def count (p : SchemePreparation.Prepared) (rank : Nat) : Nat :=
  ComparisonObserverBoundary.sizeBound p.assumptions (generators p rank)

def input (p : SchemePreparation.Prepared) (rank : Nat) : ComparisonSignedSynthesis.Input :=
  ⟨inputTypeKeys p, fun _ => (imageBasis p rank).types⟩

def modeFunction (modes : List (Nat × ModExpr)) : ModVar → ModExpr :=
  ({ modes := modes } : CompareSubstitution).mode

def modeScope (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) : Bool :=
  modes.all fun entry => decide (p.firstMode ≤ entry.1)

def supported (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) : Bool :=
  (inputModes p).all fun v =>
    (modeFunction modes v).freeVariables.all (inputModes p).contains

def guards (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) : Bounds :=
  ((ComparisonPreparedScalar.required p).map (Constraint.subst TypeExpr.var (modeFunction modes))) ++
    modes.map fun entry => .defined entry.2

def scalarQuery (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) : BoolExpr :=
  .imp (boundsModeFormula p.assumptions) (boundsModeFormula (guards p modes))

def run (fuel : Nat) (p : SchemePreparation.Prepared) (rank : Nat)
    (modes : List (Nat × ModExpr)) : RunResult CompareSubstitution := do
  if !modeScope p modes then
    return ← .rejected "modality action changes the fixed namespace"
  if !supported p modes then
    return ← .rejected "modality action exceeds the input names"
  let scalar ← ConcreteBackend.decideFormula fuel (scalarQuery p modes)
  if !scalar.valid then
    return ← .rejected "original bounds do not entail the modality guards"
  let result ← ComparisonRankedDecision.run fuel p.assumptions (input p rank)
    (typeNames p rank) (modeNames p rank) (count p rank) (modeFunction modes) (endpoints p)
  return { types := result.images, modes := modes }

def compare (fuel : Nat) (ambient : Bounds) (source target : Scheme) (rank : Nat)
    (modes : List (Nat × ModExpr)) : RunResult CompareSubstitution := do
  let p := SchemePreparation.prepare ambient source target
  let action ← run fuel p rank modes
  return ComparisonPreparation.reconstruct p action

end ModalityInference.ComparisonRankedPrepared
