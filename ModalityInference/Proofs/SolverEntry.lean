import ModalityInference.Constraints

/-! The worklist accepts only an acyclic accumulated substitution. Empty
substitutions used by inference satisfy the executable check unconditionally. -/
namespace ModalityInference

theorem Substitution.checkAcyclic_iff (σ : Substitution) :
    σ.checkAcyclic = true ↔ σ.Acyclic := by
  simp only [Substitution.checkAcyclic, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Substitution.Acyclic, Prod.forall, and_assoc]

@[simp] theorem Substitution.checkAcyclic_empty : ({} : Substitution).checkAcyclic = true := rfl

theorem runSolver_input_acyclic {fuel s result} (h : runSolver fuel s = .success result) :
    s.substitution.Acyclic := by
  by_cases hc : s.substitution.checkAcyclic = true
  · exact (s.substitution.checkAcyclic_iff).mp hc
  · simp [runSolver, hc, bind, RunResult.bind] at h

namespace SolverEntry

/-- The previous public entry checked only pending/residual type shapes. -/
def formerRunSolver (fuel : Nat) (s : SolverState) : RunResult SolverState := do
  checkShapes fuel (s.pending ++ s.bounds)
  runWorklist fuel s

theorem empty_input_unchanged {fuel s} (hσ : s.substitution = {}) :
    runSolver fuel s = formerRunSolver fuel s := by
  simp [runSolver, formerRunSolver, hσ, bind, RunResult.bind]

def cyclicState : SolverState :=
  { pending := [.sub (.var (.flex 0)) (.var (.flex 1))]
    substitution := { types := [(0, .fn (.var (.flex 0)) .unit)] }
    nextType := 2 }

theorem cyclic_not_acyclic : ¬ cyclicState.substitution.Acyclic := by
  rw [← Substitution.checkAcyclic_iff]
  decide

theorem former_shape_precheck :
    checkShapes 3 (cyclicState.pending ++ cyclicState.bounds) = .success () := rfl

theorem former_exhausted_twenty : formerRunSolver 20 cyclicState = .exhausted := by rfl

theorem corrected_rejects (fuel : Nat) : runSolver fuel cyclicState =
    .rejected "initial solver substitution is cyclic, duplicated, or not normalized" := rfl

end SolverEntry

end ModalityInference
