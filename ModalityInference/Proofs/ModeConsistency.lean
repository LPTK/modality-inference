import ModalityInference.ModeConsistency
import ModalityInference.Proofs.HornPropagation
import ModalityInference.Proofs.CNFPropagation
import ModalityInference.Proofs.CNFNormalization
import ModalityInference.Proofs.ModeWitness
/-! Soundness, completeness, termination, and fuel stability of the public propagation backend. -/
namespace ModalityInference.ModeConsistency

theorem isPolarized_iff (cs : Bounds) :
    isPolarized cs = true ↔ (boundsModeFormula cs).IsHorn := by
  simpa only [isPolarized, Option.isSome_iff_exists] using
    HornPropagation.horn_domain_iff (boundsModeFormula cs)

theorem solve_of_polarized {fuel cs} (h : (boundsModeFormula cs).IsHorn) :
    solve fuel cs = HornPropagation.satisfiableModes fuel cs := by
  simp only [solve, (isPolarized_iff cs).mpr h, ↓reduceIte]

theorem horn_witness {fuel cs result}
    (h : HornPropagation.satisfiableModes fuel cs = .success result) :
    ∃ η, ModeModels cs η ∧ ∀ v ∈ cs.modVars, result.lookup v = some (η v) := by
  unfold HornPropagation.satisfiableModes at h
  cases hm : HornPropagation.checkFormula fuel (boundsModeFormula cs) <;>
    simp [hm, bind, pure, RunResult.bind] at h
  rename_i model
  subst result
  exact ⟨projectedModes model.eval,
    (boundsModeFormula_correct _ _).mp (HornPropagation.checkFormula_sound hm),
    fun _ hv => ModeAssignment.ofBooleans_lookup hv⟩

theorem horn_complete {cs η} (hp : (boundsModeFormula cs).IsHorn)
    (hη : ModeModels cs η) :
    ∃ n, ∀ fuel ≥ n, ∃ result, HornPropagation.satisfiableModes fuel cs = .success result := by
  have he : (boundsModeFormula cs).eval (encodeModes η) = true := by
    simpa only [boundsModeFormula_correct, projectedModes_encodeModes] using hη
  obtain ⟨model, hm⟩ := HornPropagation.checkFormula_complete hp ⟨_, he⟩
  exact ⟨HornPropagation.requiredFuel (boundsModeFormula cs), fun fuel hf =>
    ⟨ModeAssignment.ofBooleans cs model.eval, by
      simp [HornPropagation.satisfiableModes, hm fuel hf, bind, pure, RunResult.bind]⟩⟩

theorem horn_terminates (cs : Bounds) :
    ∃ n, ∀ fuel ≥ n, HornPropagation.satisfiableModes fuel cs ≠ .exhausted := by
  refine ⟨HornPropagation.requiredFuel (boundsModeFormula cs), fun fuel hf => ?_⟩
  have hn := HornPropagation.checkFormula_not_exhausted hf
  cases hm : HornPropagation.checkFormula fuel (boundsModeFormula cs) <;>
    simp_all [HornPropagation.satisfiableModes, bind, pure, RunResult.bind]

theorem horn_monotone {n cs result}
    (h : HornPropagation.satisfiableModes n cs = .success result) :
    ∀ fuel ≥ n, HornPropagation.satisfiableModes fuel cs = .success result := by
  intro fuel hf
  simp only [HornPropagation.satisfiableModes, bind, pure, RunResult.bind] at h ⊢
  split at h <;> try contradiction
  rename_i model hm
  simpa only [HornPropagation.checkFormula_mono hf hm] using h

theorem general_witness {fuel cs result}
    (h : general fuel cs = .success result) :
    ∃ η, ModeModels cs η ∧ ∀ v ∈ cs.modVars, result.lookup v = some (η v) := by
  unfold general at h
  cases hc : toCNF fuel true (boundsModeFormula cs) <;>
    simp [hc, bind, RunResult.bind] at h
  rename_i clauses
  cases hs : CNFPropagation.solve fuel clauses <;> simp [hs, pure] at h
  rename_i assignment
  subst result
  exact ⟨projectedModes (CNFPropagation.valuation assignment),
    (boundsModeFormula_correct _ _).mp
      ((toCNF_correct hc _).mp (CNFPropagation.solve_sound hs)),
    fun _ hv => ModeAssignment.ofBooleans_lookup hv⟩

theorem general_complete {cs η} (hη : ModeModels cs η) :
    ∃ n, ∀ fuel ≥ n, ∃ result, general fuel cs = .success result := by
  obtain ⟨n, clauses, hc⟩ := toCNF_complete (boundsModeFormula cs) true
  have hm : CNFHolds (encodeModes η) clauses := by
    simpa only [toCNF_correct (hc n le_rfl), boundsModeFormula_correct,
      projectedModes_encodeModes] using hη
  obtain ⟨m, hs⟩ := CNFPropagation.solve_complete hm
  refine ⟨max n m, fun fuel hf => ?_⟩
  obtain ⟨assignment, ha⟩ := hs fuel (by omega)
  exact ⟨ModeAssignment.ofBooleans cs (CNFPropagation.valuation assignment), by
    simp [general, hc fuel (by omega), ha, bind, pure, RunResult.bind]⟩

theorem general_terminates (cs : Bounds) :
    ∃ n, ∀ fuel ≥ n, general fuel cs ≠ .exhausted := by
  obtain ⟨n, clauses, hc⟩ := toCNF_complete (boundsModeFormula cs) true
  obtain ⟨m, hm⟩ := CNFPropagation.solve_terminates clauses
  refine ⟨max n m, fun fuel hf => ?_⟩
  have hn := hm fuel (by omega)
  cases hs : CNFPropagation.solve fuel clauses <;>
    simp_all [general, hc fuel (by omega), bind, pure, RunResult.bind]

theorem general_monotone {n cs result} (h : general n cs = .success result) :
    ∀ fuel ≥ n, general fuel cs = .success result := by
  intro fuel hf
  simp only [general, bind, pure, RunResult.bind] at h ⊢
  repeat' (split at h <;> try contradiction)
  rename_i _ clauses hc _ assignment ha
  simpa only [toCNF_monotone hc fuel hf, CNFPropagation.solve_monotone ha fuel hf] using h

theorem solve_witness {fuel cs result} (h : solve fuel cs = .success result) :
    ∃ η, ModeModels cs η ∧ ∀ v ∈ cs.modVars, result.lookup v = some (η v) := by
  unfold solve at h
  split at h
  · exact horn_witness h
  · exact general_witness h

theorem solve_sound {fuel cs result} (h : solve fuel cs = .success result) :
    ModeModels cs result.total := by
  obtain ⟨η, hη, hv⟩ := solve_witness h
  exact (ModeModels.congr cs (fun v hm => by simp [ModeAssignment.total, hv v hm])).mpr hη

theorem solve_complete {cs η} (hη : ModeModels cs η) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel cs = .success result := by
  by_cases hp : isPolarized cs = true
  · simpa only [solve, hp, ↓reduceIte] using horn_complete ((isPolarized_iff cs).mp hp) hη
  · simpa only [solve, hp, ↓reduceIte] using general_complete hη

theorem solve_terminates (cs : Bounds) :
    ∃ n, ∀ fuel ≥ n, solve fuel cs ≠ .exhausted := by
  by_cases hp : isPolarized cs = true
  · simpa only [solve, hp, ↓reduceIte] using horn_terminates cs
  · simpa only [solve, hp, ↓reduceIte] using general_terminates cs

theorem solve_monotone {n cs result} (h : solve n cs = .success result) :
    ∀ fuel ≥ n, solve fuel cs = .success result := by
  by_cases hp : isPolarized cs = true
  · simp only [solve, hp, ↓reduceIte] at h ⊢
    exact horn_monotone h
  · simp only [solve, hp] at h ⊢
    exact general_monotone h

theorem solve_nil {fuel : Nat} (hf : 2 ≤ fuel) : solve fuel [] = .success [] := by
  simp [ModeConsistency.solve, ModeConsistency.isPolarized, HornPropagation.satisfiableModes,
    HornPropagation.checkFormula, HornPropagation.requiredFuel, HornPropagation.domain,
    boundsModeFormula, BoolExpr.all, BoolExpr.nodes, BoolExpr.atoms, HornPropagation.horn,
    RightExpr.hornSolve, RightExpr.iterate_opt, RightExpr.eval, ModeAssignment.ofBooleans,
    Bounds.modeVariables, show ¬fuel < 2 by omega, bind, pure, RunResult.bind]

end ModalityInference.ModeConsistency
