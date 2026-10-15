import ModalityInference.ComparisonChecker
import ModalityInference.Proofs.ComparisonAlgebraPreparation
import ModalityInference.Proofs.ComparisonInstance
import ModalityInference.Proofs.Backend

/-! Evidence invariants for the assembled comparison checker. -/
namespace ModalityInference.ComparisonChecker

def PreparedEvidence (p : SchemePreparation.Prepared) (e : Evidence) : Prop :=
  ∃ action, e.substitution = ComparisonPreparation.reconstruct p action ∧
    e.assumptions = p.assumptions ∧ e.obligations = action.bounds p.sourceBounds ∧
    e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
    ∀ σ, e.query.eval σ = true

theorem propagate_evidence {fuel p shapes shared before e}
    (h : propagate fuel p shapes shared before = .success e) : PreparedEvidence p e := by
  simp only [propagate, bind, pure, RunResult.bind] at h
  repeat' first | contradiction | split at h
  all_goals cases h
  all_goals refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals rename_i _ report hr hv _
  all_goals exact (ConcreteBackend.decideFormula_correct hr).mp (by simpa using hv)

theorem variants_evidence {fuel p shapes before e}
    (h : variants fuel p shapes before = .success e) : PreparedEvidence p e := by
  cases hp : propagate fuel p shapes false before <;> simp only [variants, hp] at h
  case success => cases h; exact propagate_evidence hp
  case exhausted => contradiction
  case rejected reason =>
    cases hq : propagate fuel p shapes true before <;> simp only [hq] at h
    case success => cases h; exact propagate_evidence hq
    all_goals contradiction

theorem refineContexts_evidence {fuel p shapes before e}
    (h : refineContexts fuel p shapes before = .success e) : PreparedEvidence p e := by
  cases hv : variants fuel p shapes before <;> simp only [refineContexts, hv] at h
  case success => cases h; exact variants_evidence hv
  case exhausted => contradiction
  case rejected =>
    simp only [bind, RunResult.bind] at h
    repeat' first | contradiction | exact variants_evidence h | split at h

theorem run_evidence {fuel source target e}
    (h : run fuel source target = .success e) :
    PreparedEvidence (SchemePreparation.prepare [] source target) e := by
  simp only [run, bind, pure, RunResult.bind] at h
  repeat' first | contradiction | exact refineContexts_evidence h | split at h
  cases h
  refine ⟨_, rfl, rfl, rfl, rfl, ?_⟩
  rename_i result hi
  exact (ConcreteBackend.decideFormula_correct
    (ComparisonInstance.run_spec (ComparisonInstance.attempt_some_iff.mp hi)).2.2.2.1).mp
    (ComparisonInstance.run_spec (ComparisonInstance.attempt_some_iff.mp hi)).2.2.2.2

/-- Every successful branch returns precisely the original source domain. -/
theorem run_instantiates {fuel source target e}
    (h : run fuel source target = .success e) : CompareInstantiates source e.substitution := by
  obtain ⟨action, he, _⟩ := run_evidence h
  exact he ▸ ComparisonPreparation.reconstruct_instantiates [] source target action

theorem run_query_valid {fuel source target e}
    (h : run fuel source target = .success e) : ∀ σ, e.query.eval σ = true :=
  (run_evidence h).choose_spec.2.2.2.2

end ModalityInference.ComparisonChecker
