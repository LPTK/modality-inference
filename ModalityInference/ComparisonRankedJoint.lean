import ModalityInference.ComparisonRankedModes
import ModalityInference.ComparisonRankedPrepared

/-! Simultaneous finite-rank type and modality synthesis. Only fixed input
mode names occur inside the shared type-image generator basis. -/
namespace ModalityInference.ComparisonRankedJoint

open ComparisonSelectedBases ComparisonRankedBasis

def fixedNames (p : SchemePreparation.Prepared) : List ModVar :=
  (inputModes p).filter fun v => decide (v.index < p.firstMode)

def modeIds (p : SchemePreparation.Prepared) : List Nat :=
  (inputModes p).filterMap fun v => match v with
    | .flex n => if p.firstMode ≤ n then some n else none
    | .rigid _ => none

def imageBasis (p : SchemePreparation.Prepared) (n : Nat) : ComparisonControls.Basis :=
  basis (inputNames p) (fixedNames p) n

def generators (p : SchemePreparation.Prepared) (n : Nat) : List CompareTy :=
  (imageBasis p (n + ComparisonRankedDecision.endpointRank
    (ComparisonSignedObservation.endpoints p))).types

def typeNames (p : SchemePreparation.Prepared) (n : Nat) : List TypeVar :=
  ComparisonObserverBoundary.retainedTypes p.assumptions (generators p n)

def modeNames (p : SchemePreparation.Prepared) (n : Nat) : List ModVar :=
  ComparisonObserverBoundary.retainedModes p.assumptions (generators p n)

def count (p : SchemePreparation.Prepared) (n : Nat) : Nat :=
  ComparisonObserverBoundary.sizeBound p.assumptions (generators p n)

def run (fuel : Nat) (p : SchemePreparation.Prepared) (n : Nat) :
    RunResult ComparisonSignedQuerySolver.Solution := do
  let scalar ← ComparisonPreparedScalar.run fuel p
  ComparisonRankedModes.run fuel p.assumptions (inputTypeKeys p)
    (typeNames p n) (modeNames p n) (modeIds p)
    (count p n) (imageBasis p n) (ComparisonSignedObservation.endpoints p) [scalar.source]

def synthesize (fuel : Nat) (p : SchemePreparation.Prepared) (n : Nat) :
    RunResult CompareSubstitution := do
  let scalar ← ComparisonPreparedScalar.run fuel p
  ComparisonRankedModes.synthesize fuel p.assumptions (inputTypeKeys p)
    (typeNames p n) (modeNames p n) (modeIds p)
    (count p n) (imageBasis p n) (ComparisonSignedObservation.endpoints p) [scalar.source]

def compare (fuel : Nat) (ambient : Bounds) (source target : Scheme) (n : Nat) :
    RunResult CompareSubstitution := do
  let p := SchemePreparation.prepare ambient source target
  let action ← synthesize fuel p n
  return ComparisonPreparation.reconstruct p action

end ModalityInference.ComparisonRankedJoint
