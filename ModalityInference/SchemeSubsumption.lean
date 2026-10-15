import ModalityInference.ComparisonChecker
import ModalityInference.ComparisonJointChecker
import ModalityInference.SchemeInstance

/-! Scheme comparison uses fresh shape templates, symbolic lattice propagation,
and uniform modality synthesis. Internal witnesses use `CompareTy`; public
schemes retain the join-free type grammar. Body and image definedness are
source obligations discharged under the unchanged declared assumptions. -/
namespace ModalityInference

abbrev SubsumptionEvidence := ComparisonChecker.Evidence

/-- The joint solver returns an action in the original quantified namespace.
Its obligations retain every source bound and instance-definedness guard. -/
def jointSubsumptionEvidence (source target : Scheme) (action : CompareSubstitution) :
    SubsumptionEvidence :=
  let p := SchemePreparation.prepare [] source target
  { substitution := action
    assumptions := p.assumptions
    obligations := action.bounds source.requireDefinedInstances.bounds
    body := (action.ty source.body, .ofTy p.targetType)
    flexibleAtoms := []
    query := .const true
    backend := ⟨[], [], true⟩ }

def checkSubsumption (fuel : Nat) (inferred declared : Scheme) :
    RunResult SubsumptionEvidence :=
  match ComparisonChecker.run fuel inferred.requireDefinedInstances declared with
  | .rejected _ => do
      let action ← ComparisonJointChecker.run fuel inferred declared
      return jointSubsumptionEvidence inferred declared action
  | result => result

end ModalityInference
