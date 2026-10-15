import ModalityInference.ComparisonChecker

/-! Scheme comparison uses fresh shape templates, symbolic lattice propagation,
and uniform modality synthesis. Internal witnesses use `CompareTy`; public
schemes retain the join-free type grammar. -/
namespace ModalityInference

abbrev SubsumptionEvidence := ComparisonChecker.Evidence

def checkSubsumption (fuel : Nat) (inferred declared : Scheme) :
    RunResult SubsumptionEvidence :=
  ComparisonChecker.run fuel inferred declared

end ModalityInference
