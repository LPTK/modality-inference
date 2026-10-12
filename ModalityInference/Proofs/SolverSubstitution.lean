import ModalityInference.Proofs.Normalization
import ModalityInference.Proofs.SubstitutionSupport
import ModalityInference.Proofs.SolverEntry

/-! The executable worklist preserves normalized acyclic substitutions. -/
namespace ModalityInference

theorem SolverState.skeleton_substitution (s : SolverState) (a : Ty) :
    (s.skeleton a).2.substitution = s.substitution := by
  cases a <;> rfl

theorem stepType_substitution {s a b t} (h : stepType s a b = .success t) :
    t.substitution = s.substitution := by
  unfold stepType at h
  repeat' split at h
  all_goals simp_all [bind, pure, RunResult.bind, SolverState.emit, SolverState.retain]
  all_goals subst t
  all_goals first | rfl |
    simpa only [SolverState.skeleton_substitution] using
      (congrArg (fun p : Ty × SolverState => p.2.substitution) ‹s.skeleton _ = (_, _)›).symm

theorem stepMode_substitution {s a b t} (h : stepMode s a b = .success t) :
    t.substitution = s.substitution := by
  unfold stepMode at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h; rfl

theorem Substitution.normalized_equal_fresh {σ : Substitution} (hσ : σ.Acyclic)
    {c n t} (h : (σ.constraint c).normalize = .equal (.flex n) t) :
    n ∉ σ.types.map Prod.fst ∧ ∀ k ∈ σ.types.map Prod.fst, TypeVar.flex k ∉ t.typeVars := by
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Constraint.normalize] at h
  all_goals try contradiction
  rename_i v a
  cases v with
  | rigid j => simp at h
  | flex j =>
    cases he : σ.types.lookup j <;> simp only [he, reduceCtorEq] at h
    cases h
    refine ⟨?_, fun k hk => by simpa using σ.ty_avoids hσ hk a⟩
    rintro hn
    obtain ⟨⟨j, a⟩, ha, rfl⟩ := List.mem_map.mp hn
    simpa using (List.lookup_eq_none_iff.mp he) (j, a) ha

theorem solverStep_acyclic {s t} (hσ : s.substitution.Acyclic)
    (h : solverStep s = .success t) : t.substitution.Acyclic := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals first
    | exact (stepType_substitution h).symm ▸ hσ
    | exact (stepMode_substitution h).symm ▸ hσ
    | skip
  all_goals cases h
  all_goals try exact hσ
  rename_i a v n he hsame hoccurs
  obtain ⟨hn, ht⟩ := s.substitution.normalized_equal_fresh hσ he
  apply Substitution.extendType_acyclic hσ hn
  simpa using And.intro (show TypeVar.flex n ∉ a.typeVars by simpa using hoccurs) ht

theorem runWorklist_acyclic {fuel s t} (hσ : s.substitution.Acyclic)
    (h : runWorklist fuel s = .success t) : t.substitution.Acyclic := by
  induction fuel generalizing s
  case zero => cases h
  case succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h; exact hσ
    · cases hs : solverStep s <;> simp [hs, bind, RunResult.bind] at h
      exact ih (solverStep_acyclic hσ hs) h

theorem runSolver_output_acyclic {fuel s t} (h : runSolver fuel s = .success t) :
    t.substitution.Acyclic := by
  have hσ := runSolver_input_acyclic h
  simp only [runSolver, (s.substitution.checkAcyclic_iff).mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind] at h
  split at h <;> first | exact runWorklist_acyclic hσ h | cases h

theorem solveFrom_acyclic {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) : result.substitution.Acyclic := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  split at h <;> cases h
  exact runSolver_output_acyclic hs

theorem solve_acyclic {fuel cs result} (h : solve fuel cs = .success result) :
    result.substitution.Acyclic := solveFrom_acyclic h

end ModalityInference
