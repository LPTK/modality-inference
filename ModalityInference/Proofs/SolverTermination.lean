import ModalityInference.Proofs.ShapeWitness
import ModalityInference.Proofs.ShapeWorklist
import ModalityInference.Proofs.ModeSearchComplete

/-! Eventual termination of initialized constraint solving. -/
namespace ModalityInference

theorem runSolver_eventually {s : SolverState} (hs : s.Fresh) (hu : s.Unbound) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, runSolver fuel s = result := by
  cases he : s.substitution.checkAcyclic with
  | false =>
    refine ⟨0, .rejected "initial solver substitution is cyclic, duplicated, or not normalized",
      by simp, fun fuel _ => ?_⟩
    simp [runSolver, he, bind, RunResult.bind]
  | true =>
    have hσ := s.substitution.checkAcyclic_iff.mp he
    obtain ⟨n, result, hn, hr⟩ := checkShapes_eventually (s.substitution.bounds (s.pending ++ s.bounds))
    cases result with
    | exhausted => exact False.elim (hn rfl)
    | rejected reason =>
      refine ⟨n, .rejected reason, by simp, fun fuel hf => ?_⟩
      simp [runSolver, he, hr fuel hf, bind, RunResult.bind]
    | success u =>
      cases u
      obtain ⟨ρ, hρ⟩ := SolverShape.checkShapes_model (hr n le_rfl)
      have hfix : s.substitution.bounds (s.pending ++ s.bounds) = s.pending ++ s.bounds :=
        Substitution.bounds_fixed hu.modes (fun c hc =>
          (List.mem_append.mp hc).elim (hu.pending c) (hu.bounds c))
      rw [hfix] at hρ
      obtain ⟨k, result, hk, hs'⟩ := SolverShape.runWorklist_eventually hs hu hσ
        (SolverShape.models_append.mp hρ)
      refine ⟨max n k, result, hk, fun fuel hf => ?_⟩
      simp [runSolver, he, hr fuel (by omega), hs' fuel (by omega), bind, RunResult.bind]

theorem solveFrom_terminates {cs : Bounds} {nt nm} (hc : cs.Bounded nt nm) :
    ∃ n, ∀ fuel ≥ n, solveFrom fuel nt nm cs ≠ .exhausted := by
  have hf : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Fresh :=
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩
  have hu : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Unbound :=
    ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩
  obtain ⟨n, result, hn, hr⟩ := runSolver_eventually hf hu
  cases result with
  | exhausted => exact False.elim (hn rfl)
  | rejected reason =>
    exact ⟨n, fun fuel hf => by simp [solveFrom, hr fuel hf, bind, RunResult.bind]⟩
  | success s =>
    obtain ⟨k, hk⟩ := satisfiableModes_terminates s.bounds
    refine ⟨max n k, fun fuel hf => ?_⟩
    have hh := hk fuel (by omega)
    cases hm : satisfiableModes fuel s.bounds <;>
      simp_all [solveFrom, hr fuel (by omega), bind, RunResult.bind]

theorem solve_terminates (cs : Bounds) : ∃ n, ∀ fuel ≥ n, solve fuel cs ≠ .exhausted :=
  solveFrom_terminates cs.bounded_freshIndices

end ModalityInference
