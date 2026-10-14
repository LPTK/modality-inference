import ModalityInference.Proofs.SolverGround
import ModalityInference.Proofs.GroundPrincipality

/-! Complete solving and ground principality on the original identifiers. -/
namespace ModalityInference

theorem solveFrom_complete {cs : Bounds} {nt nm} (hc : cs.Bounded nt nm)
    (hf : cs.Flexible) (hm : ∃ ρ, GroundModels ρ cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solveFrom fuel nt nm cs = .success result := by
  obtain ⟨ρ, hρ⟩ := hm
  have hs : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Fresh :=
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩
  have hu : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Unbound :=
    ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩
  obtain ⟨n, s, hmodel, hr⟩ := SolverGround.runSolver_eventual_complete
    (scope := ⟨∅, ∅⟩) hs hu (({} : Substitution).checkAcyclic_iff.mp rfl)
    ⟨hf, Bounds.flexible_nil, Substitution.flexible_empty⟩ (by simp [Scope.Bounded])
    (Deferred.ConfigModels.initial hρ)
  obtain ⟨η, hη, _⟩ := hmodel
  have hp := (runSolver_definedInvariant
    ⟨rfl, by simp [DefinedConstraints], by simp⟩ (hr n le_rfl)).2
  have hbounds : GroundModels η s.bounds := by
    simpa only [SolverState.config, RewriteConfig.constraints, hp, List.nil_append] using hη
  obtain ⟨k, hk⟩ := satisfiableModes_complete hbounds.modeModels
  refine ⟨max n k, fun fuel hbudget => ?_⟩
  obtain ⟨w, hw⟩ := hk fuel (by omega)
  exact ⟨⟨s.substitution, s.bounds, w, s.nextType, s.nextMode, s.trace.reverse⟩,
    by simp [solveFrom, hr fuel (by omega), hw, bind, pure, RunResult.bind]⟩

theorem solve_complete {cs : Bounds} (hf : cs.Flexible) (hs : BoundsSatisfiable cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel cs = .success result :=
  solveFrom_complete cs.bounded_freshIndices hf hs.ground

theorem solveFrom_ground_factorization {cs : Bounds} {nt nm fuel result scope ρ}
    (hc : cs.Bounded nt nm) (hf : cs.Flexible) (hscope : scope.Bounded nt nm)
    (hr : solveFrom fuel nt nm cs = .success result) (hρ : GroundModels ρ cs) :
    GroundFactorization scope result.bounds result.substitution ρ := by
  have hs : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Fresh :=
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩
  have hu : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Unbound :=
    ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩
  simp only [solveFrom, bind, pure, RunResult.bind] at hr
  repeat' split at hr <;> try contradiction
  cases hr
  rename_i run s hr search witness hw
  rcases SolverGround.runSolver_complete fuel hs hu (({} : Substitution).checkAcyclic_iff.mp rfl)
      ⟨hf, Bounds.flexible_nil, Substitution.flexible_empty⟩ hscope
      (Deferred.ConfigModels.initial hρ) with he | ⟨t, he, ht⟩
  · simp [hr] at he
  · have heq : s = t := RunResult.success.inj (hr.symm.trans he)
    subst t
    exact ht.factorization (runSolver_definedInvariant
      ⟨rfl, by simp [DefinedConstraints], by simp⟩ hr).2

/-- Every original ground solution factors through every successful solver result,
with fresh auxiliaries hidden and type images compared by mutual subtyping. -/
theorem solve_ground_principal {cs : Bounds} {fuel result} (hf : cs.Flexible)
    (hr : solve fuel cs = .success result) :
    ∀ ρ, GroundModels ρ cs →
      GroundFactorization ⟨cs.typeVars, cs.modVars⟩ result.bounds result.substitution ρ :=
  fun _ hρ => solveFrom_ground_factorization cs.bounded_freshIndices hf
    ((cs.bounded_iff _ _).mp cs.bounded_freshIndices) hr hρ

end ModalityInference
