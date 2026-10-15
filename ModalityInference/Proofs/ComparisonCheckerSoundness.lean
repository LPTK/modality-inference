import ModalityInference.Proofs.ComparisonCheckerSolution
import ModalityInference.Proofs.ComparisonContextSupport
import ModalityInference.Proofs.ComparisonCapsuleContext
import ModalityInference.Proofs.ComparisonParameterization
import ModalityInference.Proofs.ComparisonPreparedBounds

/-! Semantic composition of the successful comparison branches. -/
namespace ModalityInference

theorem ComparisonContext.Scoped.exact {p : SchemePreparation.Prepared} {action : Substitution}
    (h : Scoped p action) : ComparisonExactContext.Scoped p action := by
  refine ⟨?_, h.2⟩
  simp only [h.1, List.not_mem_nil, false_implies, implies_true]

namespace ComparisonChecker

def PropagationSound (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) : Prop :=
  ∀ {before : Substitution} {shared : Bool} {e : Evidence},
    ComparisonExactContext.Scoped p before → before.Bounded p.nextType p.nextMode →
    propagate fuel p shapes shared before = .success e → PreparedSolution p e

theorem variants_solution_of_propagate {fuel p shapes before e}
    (hprop : PropagationSound fuel p shapes)
    (hs : ComparisonExactContext.Scoped p before) (hb : before.Bounded p.nextType p.nextMode)
    (h : variants fuel p shapes before = .success e) : PreparedSolution p e := by
  cases hp : propagate fuel p shapes false before <;> simp only [variants, hp] at h
  case success => cases h; exact hprop hs hb hp
  case exhausted => contradiction
  case rejected reason =>
    cases hq : propagate fuel p shapes true before <;> simp only [hq] at h
    case success => cases h; exact hprop hs hb hq
    all_goals contradiction

theorem refineContexts_solution_of_propagate {fuel p shapes before e}
    (hprop : PropagationSound fuel p shapes)
    (ht : p.targetType.Bounded p.nextType p.nextMode)
    (hs : ComparisonExactContext.Scoped p before) (hb : before.Bounded p.nextType p.nextMode)
    (h : refineContexts fuel p shapes before = .success e) : PreparedSolution p e := by
  cases hv : variants fuel p shapes before <;> simp only [refineContexts, hv] at h
  case success => cases h; exact variants_solution_of_propagate hprop hs hb hv
  case exhausted => contradiction
  case rejected =>
    simp only [bind, RunResult.bind] at h
    repeat' first | contradiction | split at h
    all_goals first
      | exact variants_solution_of_propagate hprop hs hb h
      | (refine variants_solution_of_propagate hprop (hs.compose ?_) (hb.compose ?_) h
         · first
           | (have hselected := ComparisonContext.prepare_scoped (by assumption)
              exact hselected.exact)
           | (have hselected := ComparisonExactContext.prepare_scoped (by assumption)
              exact hselected)
         · first
           | (have hselected := ComparisonContext.prepare_bounded (by assumption) (by exact ht)
              exact hselected)
           | (have hselected := ComparisonExactContext.prepare_bounded (by assumption) (by exact ht)
              exact hselected))

theorem core_solution_of_propagate {fuel source target e}
    (ht : (SchemePreparation.prepare [] source target).targetType.Bounded
      (SchemePreparation.prepare [] source target).nextType
      (SchemePreparation.prepare [] source target).nextMode)
    (hprop : ∀ shapes, ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved shapes) → PropagationSound fuel (SchemePreparation.prepare [] source target) shapes)
    (h : core fuel source target = .success e) :
    PreparedSolution (SchemePreparation.prepare [] source target) e := by
  simp only [core, bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (apply refineContexts_solution_of_propagate (hprop _ (by assumption)) ht ?_ ?_ h
       · first
         | exact ComparisonExactContext.neutral_scoped _
         | simp [ComparisonExactContext.Scoped]
       · first
         | exact ComparisonExactContext.neutral_bounded _
         | exact Substitution.bounded_empty _ _)
    | split at h
  cases h
  exact exact_solution (by assumption)

theorem partial_solution {fuel source target result}
    (h : ComparisonPartialPropagation.attempt fuel (SchemePreparation.prepare [] source target) =
      .success (some result)) :
    PreparedSolution (SchemePreparation.prepare [] source target)
      (partialEvidence (SchemePreparation.prepare [] source target) result) := by
  obtain ⟨hs, hb, ht⟩ := ComparisonPartialPropagation.attempt_sound h
  exact ⟨result.action, rfl, rfl, rfl, partial_action_domains h, hs, hb, ht⟩

theorem capsuleCore_solution_of_propagate {fuel source target e}
    (hprop : ∀ source target shapes,
      ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
        .success (.solved shapes) → PropagationSound fuel (SchemePreparation.prepare [] source target) shapes)
    (h : capsuleCore fuel source target = .success e) :
    PreparedSolution (SchemePreparation.prepare [] source target) e := by
  simp only [capsuleCore, bind, pure, RunResult.bind] at h
  repeat' first | contradiction | cases h | split at h
  rename_i _ known hknown hnonempty _ result hcore
  have hs := core_solution_of_propagate
    (SchemePreparation.prepare_targetType_bounded [] _ _) (hprop _ _) hcore
  have hc := ComparisonParameterization.result_sound source target _ _ _ hs
  exact ⟨_, rfl, rfl, rfl,
    capsuleAction_domains (by simp [SchemePreparation.prepare]) hcore, hc⟩

theorem run_solution_of_propagate {fuel source target e}
    (ht : (SchemePreparation.prepare [] source target).targetType.Bounded
      (SchemePreparation.prepare [] source target).nextType
      (SchemePreparation.prepare [] source target).nextMode)
    (hprop : ∀ source target shapes,
      ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
        .success (.solved shapes) → PropagationSound fuel (SchemePreparation.prepare [] source target) shapes)
    (h : run fuel source target = .success e) :
    PreparedSolution (SchemePreparation.prepare [] source target) e := by
  cases hc : core fuel source target <;> simp only [run, hc] at h
  case success => cases h; exact core_solution_of_propagate ht (hprop source target) hc
  case exhausted => contradiction
  case rejected reason =>
    cases hp : ComparisonPartialPropagation.attempt fuel
        (SchemePreparation.prepare [] source target) <;>
      simp only [hp, bind, pure, RunResult.bind] at h
    case success result =>
      cases result with
      | none =>
        cases hs : capsuleCore fuel source target <;> simp only [hs] at h
        case success => cases h; exact capsuleCore_solution_of_propagate hprop hs
        all_goals contradiction
      | some result => cases h; exact partial_solution hp
    all_goals contradiction

theorem run_algebra_subsumes_of_propagate {fuel source target e}
    (ht : (SchemePreparation.prepare [] source target).targetType.Bounded
      (SchemePreparation.prepare [] source target).nextType
      (SchemePreparation.prepare [] source target).nextMode)
    (hprop : ∀ source target shapes,
      ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
        .success (.solved shapes) → PropagationSound fuel (SchemePreparation.prepare [] source target) shapes)
    (h : run fuel source target = .success e) : AlgebraSubsumes [] source target :=
  (run_solution_of_propagate ht hprop h).subsumes

end ComparisonChecker
end ModalityInference
