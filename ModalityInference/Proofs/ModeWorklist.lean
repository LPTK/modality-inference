import ModalityInference.Proofs.WorklistOrder

/-! Eventual termination of a worklist containing only modality obligations. -/
namespace ModalityInference

theorem stepMode_ne_exhausted (s : SolverState) (a b : ModExpr) :
    stepMode s a b ≠ .exhausted := by
  unfold stepMode
  repeat' split
  all_goals simp [bind, pure, RunResult.bind]

theorem stepType_ne_exhausted (s : SolverState) (a b : Ty) :
    stepType s a b ≠ .exhausted := by
  unfold stepType
  repeat' split
  all_goals simp [bind, pure, RunResult.bind]

theorem solverStep_ne_exhausted (s : SolverState) : solverStep s ≠ .exhausted := by
  simp only [solverStep, bind, pure, RunResult.bind]
  repeat' split
  all_goals first
    | exact stepType_ne_exhausted _ _ _
    | exact stepMode_ne_exhausted _ _ _
    | simp

theorem solverStep_modality_progress {s t : SolverState}
    (hm : s.substitution.modes = []) (hs : ∀ c ∈ s.pending, c.IsModality)
    (hp : s.pending ≠ []) (h : solverStep s = .success t) :
    (∀ c ∈ t.pending, c.IsModality) ∧ t.substitution = s.substitution ∧
      WorklistOrder.Lt t.pending s.pending := by
  cases hpend : s.pending with
  | nil => exact False.elim (hp hpend)
  | cons c rest =>
    have hc := hs c (hpend ▸ List.mem_cons_self)
    have hr : ∀ d ∈ rest, d.IsModality := fun d hd => hs d (hpend ▸ List.mem_cons_of_mem _ hd)
    have hfix := Constraint.modality_substitution hc hm
    simp only [solverStep, hpend, hfix, bind, pure, RunResult.bind] at h
    split at h
    · cases h
      exact ⟨hr, rfl, hpend ▸ WorklistOrder.tail c rest⟩
    · cases c <;> simp only [Constraint.IsModality] at hc
      all_goals simp only [Constraint.normalize] at h
      case mode a b =>
        have hsub := stepMode_substitution h
        exact ⟨fun d hd => (stepMode_modality_pending h d hd).elim (hr d) id,
          hsub, WorklistOrder.stepMode_decreases rfl h⟩
      case defined a =>
        repeat' split at h
        all_goals cases h
        all_goals exact ⟨hr, rfl, WorklistOrder.tail _ _⟩

theorem runWorklist_modality_eventually (s : SolverState)
    (hm : s.substitution.modes = []) (hs : ∀ c ∈ s.pending, c.IsModality) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, runWorklist fuel s = result := by
  revert hm hs
  induction s using (InvImage.wf SolverState.pending WorklistOrder.wellFounded).induction with
  | h s ih =>
    intro hm hs
    by_cases hp : s.pending = []
    · refine ⟨1, .success s, by simp, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel => simp [runWorklist, hp]
    cases he : solverStep s with
    | exhausted => exact False.elim (solverStep_ne_exhausted s he)
    | rejected reason =>
      refine ⟨1, .rejected reason, by simp, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel => simp [runWorklist, hp, he, bind, RunResult.bind]
    | success t =>
      obtain ⟨ht, hsub, hlt⟩ := solverStep_modality_progress hm hs hp he
      obtain ⟨n, result, hn, hr⟩ := ih t hlt (hsub ▸ hm) ht
      refine ⟨n + 1, result, hn, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel => simpa [runWorklist, hp, he, bind, RunResult.bind] using hr fuel (by omega)

end ModalityInference
