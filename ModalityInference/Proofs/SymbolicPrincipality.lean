import ModalityInference.Proofs.SymbolicFactorization
import ModalityInference.Proofs.Obligations

namespace ModalityInference.SymbolicSolver

theorem solverStep_factors {scope θ Δ s t} (hΔ : Residual Δ) (hs : s.Fresh)
    (hu : s.Unbound) (hσ : s.substitution.Acyclic)
    (hscope : scope.Bounded s.nextType s.nextMode)
    (he : solverStep s = .success t) (hm : Factors scope s Δ θ) :
    Factors scope t Δ θ := by
  obtain ⟨σ, hw⟩ := hm
  have hnorm : ∀c rest, s.pending = c :: rest →
      Entails Δ (σ.constraint (s.substitution.constraint c).normalize) := by
    intro c rest hp
    rw [(hu.pending c (by simp [hp])).fixed hu.modes]
    exact (Constraint.normalize_substitute hw.wellFormed).mpr
      (hw.models c (by simp [hp]))
  have htail : ∀c rest seen, s.pending = c :: rest →
      Models Δ σ {s with pending := rest, seen := seen} := by
    intro c rest seen hp d hd
    exact hw.models d (by rw [hp]; exact List.mem_cons_of_mem _ hd)
  have hcons : ∀c rest seen, s.pending = c :: rest →
      Factors scope {s with pending := (s.substitution.constraint c).normalize :: rest, seen := seen} Δ θ := by
    intro c rest seen hp
    refine ⟨σ, hw.wellFormed, ?_, hw.types, hw.modes⟩
    intro d hd
    exact (List.mem_cons.mp hd).elim (fun hh => hh ▸ hnorm c rest hp) (htail c rest seen hp d)
  simp only [solverStep, bind, pure, RunResult.bind] at he
  repeat' split at he
  case h_2 =>
    rename_i pending c rest hp hseen normalized a b hn
    exact stepType_factors hΔ (hs.advance hp (by simp))
      (hn ▸ hs.normalized_head hp).1 (hn ▸ hs.normalized_head hp).2 hscope he
      (by simpa only [hn] using hcons c rest ((s.substitution.constraint c).normalize :: s.seen) hp)
  case h_3 =>
    rename_i pending c rest hp hseen normalized a b hn
    exact stepMode_factors hΔ he
      (by simpa only [hn] using hcons c rest ((s.substitution.constraint c).normalize :: s.seen) hp)
  all_goals cases he
  case h_2.isFalse.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a v n hn hrefl hocc
    have hh := substitute_factors
      (s := {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen})
      (s.substitution.normalized_equal_fresh hσ hn).1
      (by simpa only [hn] using hcons c rest ((s.substitution.constraint c).normalize :: s.seen) hp)
    obtain ⟨τ, hτ⟩ := hh
    exact ⟨τ, hτ.wellFormed, hτ.models, hτ.types, hτ.modes⟩
  all_goals refine ⟨σ, hw.wellFormed, ?_, hw.types, hw.modes⟩
  all_goals first
    | exact hw.models
    | exact htail _ _ _ ‹s.pending = _ :: _›
    | exact (htail _ _ _ ‹s.pending = _ :: _›).emit _ (cs := [])
        (by simp [Substitution.bounds, EntailsAll])
    | exact (htail _ _ _ ‹s.pending = _ :: _›).retain _ (hnorm _ _ ‹s.pending = _ :: _›)
    | skip
  case h_1.refl =>
    rename_i pending c rest hp hseen normalized a b hn
    have hc : Entails Δ (σ.constraint (.equiv a b)) := hn ▸ hnorm c rest hp
    apply (htail c rest _ hp).emit
    simpa [Substitution.bounds, EntailsAll, Substitution.constraint, Constraint.subst,
      Entails, and_assoc, and_left_comm, and_comm] using hc
  case h_2.isFalse.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a v n hn hrefl hocc
    have hc : Entails Δ (σ.constraint (.equal (.flex n) a)) := hn ▸ hnorm c rest hp
    have hh := (σ.constraint_subst_entails _ Δ).mp hc
    apply (htail c rest _ hp).emit
    simpa [Substitution.bounds, EntailsAll, Substitution.constraint, Constraint.subst,
      Entails, Substitution.ty, TypeExpr.subst, and_assoc, and_left_comm, and_comm] using hh

theorem runWorklist_factors {scope θ Δ fuel s t} (hΔ : Residual Δ) (hs : s.Fresh)
    (hu : s.Unbound) (hσ : s.substitution.Acyclic)
    (hscope : scope.Bounded s.nextType s.nextMode)
    (he : runWorklist fuel s = .success t) (hm : Factors scope s Δ θ) :
    Factors scope t Δ θ := by
  induction fuel generalizing s with
  | zero => cases he
  | succ fuel ih =>
    simp only [runWorklist] at he
    split at he
    · cases he
      exact hm
    · cases hr : solverStep s <;> simp [hr, bind, RunResult.bind] at he
      have hc := solverStep_counters hr
      exact ih (solverStep_fresh hs hr) (solverStep_unbound hu hs hσ hr)
        (solverStep_acyclic hσ hr)
        ⟨fun v hv => (hscope.1 v hv).trans_le hc.1,
         fun v hv => (hscope.2 v hv).trans_le hc.2⟩ he
        (solverStep_factors hΔ hs hu hσ hscope hr hm)

theorem runSolver_factors {scope θ Δ fuel s t} (hΔ : Residual Δ) (hs : s.Fresh)
    (hu : s.Unbound) (hscope : scope.Bounded s.nextType s.nextMode)
    (he : runSolver fuel s = .success t) (hm : Factors scope s Δ θ) :
    Factors scope t Δ θ :=
  runWorklist_factors hΔ hs hu (runSolver_input_acyclic he) hscope (runSolver_worklist he) hm

end ModalityInference.SymbolicSolver

namespace ModalityInference

theorem solveFrom_symbolic_factorization {fuel nt nm cs result Δ θ} {scope : Scope}
    (hΔ : Residual Δ) (hc : cs.Bounded nt nm) (hscope : scope.Bounded nt nm)
    (hr : solveFrom fuel nt nm cs = .success result)
    (hcs : Solution cs Δ θ) (hθ : θ.WellFormedUnder Δ) :
    ∃τ : Substitution, τ.WellFormedUnder Δ ∧ EntailsAll Δ (τ.bounds result.bounds) ∧
      (∀v ∈ scope.types, Subtype Δ (θ.type v) (τ.ty (result.substitution.type v)) ∧
        Subtype Δ (τ.ty (result.substitution.type v)) (θ.type v)) ∧
      (∀v ∈ scope.modes,
        Submode Δ (θ.mode v) ((result.substitution.mode v).subst τ.mode) ∧
        Submode Δ ((result.substitution.mode v).subst τ.mode) (θ.mode v)) := by
  simp only [solveFrom, bind, pure, RunResult.bind] at hr
  repeat' split at hr <;> try contradiction
  cases hr
  rename_i run s hs search witness hw
  have hf : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Fresh :=
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩
  have hu : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Unbound :=
    ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩
  obtain ⟨τ, hτ⟩ := SymbolicSolver.runSolver_factors hΔ hf hu hscope hs
    (SymbolicSolver.initial hθ hcs)
  have hp := (runSolver_definedInvariant ⟨rfl, by simp [DefinedConstraints], by simp⟩ hs).2
  refine ⟨τ, hτ.wellFormed, ?_, fun v hv => (hτ.types v hv).2, hτ.modes⟩
  simpa only [hp, List.nil_append] using hτ.models.solution

theorem principal_factorization : Obligations.PrincipalFactorization := by
  intro fuel cs result Δ θ hΔ hr hs hw
  exact solveFrom_symbolic_factorization (scope := ⟨cs.typeVars, cs.modVars⟩) hΔ cs.bounded_freshIndices
    ((cs.bounded_iff _ _).mp cs.bounded_freshIndices) hr hs hw

end ModalityInference
