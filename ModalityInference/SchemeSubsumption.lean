import ModalityInference.ComparisonChecker
import ModalityInference.SchemeInstance

/-! Scheme comparison uses fresh shape templates, symbolic lattice propagation,
and uniform modality synthesis. Internal witnesses use `CompareTy`; public
schemes retain the join-free type grammar. Body and image definedness are
source obligations discharged under the unchanged declared assumptions. -/
namespace ModalityInference

abbrev SubsumptionEvidence := ComparisonChecker.Evidence

def checkSubsumption (fuel : Nat) (inferred declared : Scheme) :
    RunResult SubsumptionEvidence :=
  ComparisonChecker.run fuel inferred.requireDefinedInstances declared

end ModalityInference
