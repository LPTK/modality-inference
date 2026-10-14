import ModalityInference.Proofs.SolverFresh
import ModalityInference.Proofs.SolverUnbound

/-! Successful solver runs never move the fresh identifier supplies backward. -/
namespace ModalityInference

theorem stepMode_counters {s a b t} (h : stepMode s a b = .success t) :
    s.nextType ≤ t.nextType ∧ s.nextMode ≤ t.nextMode := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp [SolverState.emit, SolverState.retain, recordModeBound]

theorem stepType_counters {s a b t} (h : stepType s a b = .success t) :
    s.nextType ≤ t.nextType ∧ s.nextMode ≤ t.nextMode := by
  simp only [stepType, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h <;> simp [SolverState.emit, SolverState.retain, s.skeleton_counters]

theorem solverStep_counters {s t} (h : solverStep s = .success t) :
    s.nextType ≤ t.nextType ∧ s.nextMode ≤ t.nextMode := by
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals first
    | have hh := stepType_counters h; exact hh
    | have hh := stepMode_counters h; exact hh
    | cases h <;> simp [SolverState.emit, SolverState.retain]

theorem runWorklist_counters {fuel s t} (h : runWorklist fuel s = .success t) :
    s.nextType ≤ t.nextType ∧ s.nextMode ≤ t.nextMode := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h; exact ⟨le_rfl, le_rfl⟩
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ⟨(solverStep_counters ht).1.trans (ih h).1,
        (solverStep_counters ht).2.trans (ih h).2⟩

theorem runSolver_counters {fuel s t} (h : runSolver fuel s = .success t) :
    s.nextType ≤ t.nextType ∧ s.nextMode ≤ t.nextMode :=
  runWorklist_counters (runSolver_worklist h)

theorem solveFrom_counters {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) :
    nt ≤ result.nextType ∧ nm ≤ result.nextMode := by
  simp only [solveFrom, bind, pure, RunResult.bind] at h
  repeat' split at h <;> try contradiction
  cases h
  exact runSolver_counters ‹runSolver fuel _ = .success _›

end ModalityInference
