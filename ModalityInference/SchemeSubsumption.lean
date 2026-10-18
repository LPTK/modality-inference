import ModalityInference.ComparisonChecker
import ModalityInference.ComparisonJointChecker
import ModalityInference.ComparisonDeclaredAnchors
import ModalityInference.ComparisonNestedAnchors
import ModalityInference.ComparisonPreparedDriver
import ModalityInference.ComparisonResidualBounds
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

/-- Certified comparison phases retain completed positive results and
exhaustion. Residual declared bounds are decided by the joint phase; additional
prepared structural queries handle the remaining declared-bound forms. -/
def comparisonFallback (fuel : Nat) (source target : Scheme) : RunResult CompareSubstitution :=
  match ComparisonJointChecker.run fuel source target with
  | .rejected _ =>
      match ComparisonDeclaredAnchors.run fuel source target with
      | .rejected _ =>
          match ComparisonNestedAnchors.run fuel source target with
          | .rejected reason =>
              if residualBounds target.bounds then .rejected reason
              else ComparisonPreparedDriver.run fuel source target
          | result => result
      | result => result
  | result => result

def checkSubsumption (fuel : Nat) (inferred declared : Scheme) :
    RunResult SubsumptionEvidence :=
  match ComparisonChecker.run fuel inferred.requireDefinedInstances declared with
  | .rejected _ => do
      let action ← comparisonFallback fuel inferred declared
      return jointSubsumptionEvidence inferred declared action
  | result => result

end ModalityInference
