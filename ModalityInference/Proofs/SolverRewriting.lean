import ModalityInference.Proofs.WorklistCorrespondence
import ModalityInference.Proofs.SolverCompleteness

/-! Abstract guarded-rewriting derivations for successful executable solves,
and the complete principal worklist schedule on flexible constraints. -/
namespace ModalityInference

theorem solveFrom_rewriteStar {fuel nt nm cs result} (hc : cs.Bounded nt nm)
    (h : solveFrom fuel nt nm cs = .success result) :
    RewriteStar ⟨cs, [], {}⟩ ⟨[], result.bounds, result.substitution⟩ := by
  unfold solveFrom at h
  cases hr : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hr, bind, RunResult.bind] at h
  split at h <;> cases h
  obtain ⟨_, hp⟩ := runSolver_definedInvariant
    (s := {pending := cs, nextType := nt, nextMode := nm})
    ⟨rfl, by simp [DefinedConstraints], by simp⟩ hr
  have hb := (cs.bounded_iff nt nm).mp hc
  have he := runSolver_correspondence
    (by simpa using hb.1) (by simpa using hb.2) rfl rfl rfl hr
  simpa only [hp] using he

theorem solve_rewriteStar {fuel cs result} (h : solve fuel cs = .success result) :
    RewriteStar ⟨cs, [], {}⟩ ⟨[], result.bounds, result.substitution⟩ :=
  solveFrom_rewriteStar cs.bounded_freshIndices h

/-- The worklist reaches a consistent residual abstract configuration and
represents every original ground solution on every reserved finite scope. -/
theorem solveFrom_rewriting_complete {cs : Bounds} {nt nm : Nat} {scope : Scope}
    (hc : cs.Bounded nt nm) (hf : cs.Flexible) (hscope : scope.Bounded nt nm)
    (hs : ∃ ρ, GroundModels ρ cs) :
    ∃ threshold, ∀ fuel ≥ threshold, ∃ result,
      solveFrom fuel nt nm cs = .success result ∧
      RewriteStar ⟨cs, [], {}⟩ ⟨[], result.bounds, result.substitution⟩ ∧
      Residual result.bounds ∧ (∃ η, GroundModels η result.bounds) ∧
      ∀ ρ, GroundModels ρ cs → GroundFactorization scope result.bounds result.substitution ρ := by
  obtain ⟨threshold, hthreshold⟩ := solveFrom_complete hc hf hs
  refine ⟨threshold, fun fuel hle => ?_⟩
  obtain ⟨result, hresult⟩ := hthreshold fuel hle
  exact ⟨result, hresult, solveFrom_rewriteStar hc hresult, solveFrom_residual hresult,
    ⟨_, solveFrom_ground_model hresult⟩,
    fun ρ hρ => solveFrom_ground_factorization hc hf hscope hresult hρ⟩

/-- On the original input identifiers, a successful abstract worklist schedule
is eventually produced and has the ground principal factorization property. -/
theorem solve_rewriting_complete {cs : Bounds} (hf : cs.Flexible)
    (hs : BoundsSatisfiable cs) :
    ∃ threshold, ∀ fuel ≥ threshold, ∃ result,
      solve fuel cs = .success result ∧
      RewriteStar ⟨cs, [], {}⟩ ⟨[], result.bounds, result.substitution⟩ ∧
      Residual result.bounds ∧ (∃ η, GroundModels η result.bounds) ∧
      ∀ ρ, GroundModels ρ cs →
        GroundFactorization ⟨cs.typeVars, cs.modVars⟩ result.bounds result.substitution ρ := by
  obtain ⟨threshold, hthreshold⟩ := solve_complete hf hs
  refine ⟨threshold, fun fuel hle => ?_⟩
  obtain ⟨result, hresult⟩ := hthreshold fuel hle
  exact ⟨result, hresult, solve_rewriteStar hresult, solve_residual hresult,
    ⟨_, solve_ground_model hresult⟩, solve_ground_principal hf hresult⟩

end ModalityInference
