import ModalityInference.Proofs.ComparisonCheckerSolution
import ModalityInference.Proofs.ComparisonContextSupport

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

theorem run_solution_of_propagate {fuel source target e}
    (ht : (SchemePreparation.prepare [] source target).targetType.Bounded
      (SchemePreparation.prepare [] source target).nextType
      (SchemePreparation.prepare [] source target).nextMode)
    (hprop : ∀ shapes, ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved shapes) → PropagationSound fuel (SchemePreparation.prepare [] source target) shapes)
    (h : run fuel source target = .success e) :
    PreparedSolution (SchemePreparation.prepare [] source target) e := by
  simp only [run, bind, pure, RunResult.bind] at h
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

theorem run_algebra_subsumes_of_propagate {fuel source target e}
    (ht : (SchemePreparation.prepare [] source target).targetType.Bounded
      (SchemePreparation.prepare [] source target).nextType
      (SchemePreparation.prepare [] source target).nextMode)
    (hprop : ∀ shapes, ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved shapes) → PropagationSound fuel (SchemePreparation.prepare [] source target) shapes)
    (h : run fuel source target = .success e) : AlgebraSubsumes [] source target :=
  (run_solution_of_propagate ht hprop h).subsumes

end ComparisonChecker
end ModalityInference
