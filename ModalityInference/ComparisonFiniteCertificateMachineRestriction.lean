import ModalityInference.ComparisonFiniteCertificate
import ModalityInference.ComparisonObserverMachineRestriction
import ModalityInference.ComparisonObserverBoundary

/-! A canonical list of atom names for the original raw context and supplied
comparison endpoints. Machine restriction retains exactly these atom entries
and the certificate's control names. -/
namespace ModalityInference.ComparisonFiniteCertificate

def inputTypes (Δ : Bounds) (queries : List CompareTy) : List TypeVar :=
  (Δ.typeVariables ++ queries.flatMap ComparisonObserverBoundary.typeList).dedup

def Candidate.restrictMachine {Δ : Bounds} {names : List ModVar}
    (C : Candidate Δ names) (types : List TypeVar) : Candidate Δ names :=
  { C with
    types := types
    modes := names
    machine := fun i => ComparisonObserverMachineRestriction.restrict C.types C.modes types names (C.machine i) }

end ModalityInference.ComparisonFiniteCertificate
