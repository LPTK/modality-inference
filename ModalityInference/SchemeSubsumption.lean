import ModalityInference.ComparisonChecker
import ModalityInference.ComparisonJointChecker
import ModalityInference.ComparisonDeclaredAnchors
import ModalityInference.SchemeInstance

/-! Scheme comparison uses fresh shape templates, symbolic lattice propagation,
and uniform modality synthesis. Internal witnesses use `CompareTy`; public
schemes retain the join-free type grammar. Body and image definedness are
source obligations discharged under the unchanged declared assumptions. -/
namespace ModalityInference

abbrev SubsumptionEvidence := ComparisonChecker.Evidence

/-- Certified phases return an action in the original quantified namespace.
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

/-- Whole declared edges remain available after an ordinary structural solve
rejects. Completed positive results and exhaustion keep their original meaning. -/
def comparisonFallback (fuel : Nat) (source target : Scheme) : RunResult CompareSubstitution :=
  match ComparisonJointChecker.run fuel source target with
  | .rejected _ => ComparisonDeclaredAnchors.run fuel source target
  | result => result

def checkSubsumption (fuel : Nat) (inferred declared : Scheme) :
    RunResult SubsumptionEvidence :=
  match ComparisonChecker.run fuel inferred.requireDefinedInstances declared with
  | .rejected _ => do
      let action ← comparisonFallback fuel inferred declared
      return jointSubsumptionEvidence inferred declared action
  | result => result

end ModalityInference
