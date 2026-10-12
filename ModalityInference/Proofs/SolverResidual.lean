import ModalityInference.Proofs.SolverSubstitution

/-! Successful solving returns constraints in the declared residual grammar. -/
namespace ModalityInference

theorem SolverState.retain_residual {s : SolverState} (hs : Residual s.bounds)
    {c r} (hc : Residual [c]) : Residual (s.retain r c).bounds := by
  unfold SolverState.retain
  split
  · exact hs
  · exact (List.forall_cons _ _ _).mpr ⟨hc, hs⟩

theorem recordModeBound_residual {s : SolverState} (hs : Residual s.bounds) (a b : ModExpr) :
    Residual (recordModeBound s a b).bounds :=
  s.retain_residual hs (r := .modeBound) trivial

theorem stepMode_residual {s a b t} (hs : Residual s.bounds)
    (h : stepMode s a b = .success t) : Residual t.bounds := by
  unfold stepMode at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals first
    | exact hs
    | exact SolverState.retain_residual hs trivial
    | exact recordModeBound_residual hs _ _

theorem SolverState.skeleton_bounds (s : SolverState) (a : Ty) :
    (s.skeleton a).2.bounds = s.bounds := by
  cases a <;> rfl

theorem stepType_residual {s a b t} (hs : Residual s.bounds)
    (h : stepType s a b = .success t) : Residual t.bounds := by
  unfold stepType at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals first
    | exact hs
    | exact SolverState.retain_residual hs (r := .variableBound) ⟨_, _, _, _, rfl, rfl⟩
    | skip
  all_goals
    have he := congrArg (fun p : Ty × SolverState => p.2.bounds) ‹s.skeleton _ = (_, _)›
    simp only [SolverState.skeleton_bounds] at he
    exact Eq.mp (congrArg Residual he) hs

theorem solverStep_residual {s t} (hs : Residual s.bounds)
    (h : solverStep s = .success t) : Residual t.bounds := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals first
    | (apply stepType_residual (h := h); exact hs)
    | (apply stepMode_residual (h := h); exact hs)
    | skip
  all_goals cases h
  all_goals first
    | exact hs
    | exact (show Residual [] from True.intro)
    | skip
  rename_i m he hf
  apply SolverState.retain_residual (r := .defined)
  · simp [he, Residual, List.Forall]
  · exact hs

theorem runWorklist_residual {fuel s t} (hs : Residual s.bounds)
    (h : runWorklist fuel s = .success t) : Residual t.bounds := by
  induction fuel generalizing s
  case zero => cases h
  case succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h; exact hs
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_residual hs ht) h

theorem runSolver_residual {fuel s t} (hs : Residual s.bounds)
    (h : runSolver fuel s = .success t) : Residual t.bounds := by
  have hσ := runSolver_input_acyclic h
  simp only [runSolver, (s.substitution.checkAcyclic_iff).mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind] at h
  split at h <;> first | exact runWorklist_residual hs h | cases h

theorem solveFrom_residual {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) : Residual result.bounds := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  split at h <;> cases h
  apply runSolver_residual (h := hs)
  trivial

theorem solve_residual {fuel cs result} (h : solve fuel cs = .success result) :
    Residual result.bounds := solveFrom_residual h

end ModalityInference
