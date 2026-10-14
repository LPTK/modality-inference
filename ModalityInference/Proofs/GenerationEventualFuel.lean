import ModalityInference.Proofs.GenerationSupplies
import ModalityInference.Proofs.ModeSearchComplete

/-! Increasing a successful execution budget preserves the complete result. -/
namespace ModalityInference

theorem searchCNF_stable {n todo r} (hr : r ≠ .exhausted)
    (h : searchCNF n todo = r) : ∀ fuel ≥ n, searchCNF fuel todo = r := by
  induction n generalizing todo r
  case zero => exact False.elim (hr h.symm)
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (todo r) (hs : searchCNF n todo = r) (hne : r ≠ .exhausted) :
        searchCNF fuel todo = r := ih hne hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases todo
    all_goals simp only [searchCNF] at h ⊢
    all_goals repeat' (split at h <;> try exact False.elim (hr h.symm))
    all_goals simp_all

theorem satisfiableModes_monotone {n cs result}
    (h : satisfiableModes n cs = .success result) :
    ∀ fuel ≥ n, satisfiableModes fuel cs = .success result :=
  ModeConsistency.solve_monotone h

theorem checkShapePairs_stable {n ps r} (hr : r ≠ .exhausted)
    (h : checkShapePairs n ps = r) :
    ∀ fuel ≥ n, checkShapePairs fuel ps = r := by
  induction n generalizing ps r
  case zero => exact False.elim (hr h.symm)
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (ps r) (hs : checkShapePairs n ps = r) (hne : r ≠ .exhausted) :
        checkShapePairs fuel ps = r := ih hne hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases ps
    all_goals simp only [checkShapePairs] at h ⊢
    all_goals repeat' (split at h <;> try exact False.elim (hr h.symm))
    all_goals simp_all

theorem runWorklist_stable {n s r} (hr : r ≠ .exhausted)
    (h : runWorklist n s = r) : ∀ fuel ≥ n, runWorklist fuel s = r := by
  induction n generalizing s r
  case zero => exact False.elim (hr h.symm)
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (s r) (hs : runWorklist n s = r) (hne : r ≠ .exhausted) :
        runWorklist fuel s = r := ih hne hs fuel (Nat.le_of_succ_le_succ hFuel)
    simp only [runWorklist, bind, RunResult.bind] at h ⊢
    repeat' (split at h <;> try exact False.elim (hr h.symm))
    all_goals simp_all

theorem runSolver_monotone {n s result} (h : runSolver n s = .success result) :
    ∀ fuel ≥ n, runSolver fuel s = .success result := by
  intro fuel hf
  simp only [runSolver, checkShapes, bind, RunResult.bind] at h ⊢
  repeat' (split at h <;> try contradiction)
  rename_i hacyclic _ shape hs
  simpa only [hacyclic, ↓reduceIte, checkShapePairs_stable (by simp) hs fuel hf]
    using runWorklist_stable (by simp) h fuel hf

theorem solveFrom_monotone {n nt nm cs result}
    (h : solveFrom n nt nm cs = .success result) :
    ∀ fuel ≥ n, solveFrom fuel nt nm cs = .success result := by
  intro fuel hf
  simp only [solveFrom, bind, pure, RunResult.bind] at h ⊢
  repeat' (split at h <;> try contradiction)
  rename_i _ state hs _ witness hw
  simpa only [runSolver_monotone hs fuel hf, satisfiableModes_monotone hw fuel hf] using h

theorem generate_monotone {n Γ t s result}
    (h : generate n Γ t s = .success result) :
    ∀ fuel ≥ n, generate fuel Γ t s = .success result := by
  induction n generalizing Γ t s result
  case zero => cases h
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (Γ t s r) (hs : generate n Γ t s = .success r) :
        generate fuel Γ t s = .success r := ih hs fuel (Nat.le_of_succ_le_succ hFuel)
    have solveStep (nt nm cs r) (hs : solveFrom n nt nm cs = .success r) :
        solveFrom fuel nt nm cs = .success r :=
      solveFrom_monotone hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases t
    all_goals simp only [generate, bind, pure, RunResult.bind] at h ⊢
    all_goals repeat' (split at h <;> try contradiction)
    all_goals simp_all

theorem infer_monotone {n Γ t result} (h : infer n Γ t = .success result) :
    ∀ fuel ≥ n, infer fuel Γ t = .success result := by
  intro fuel hf
  simp only [infer, bind, pure, RunResult.bind] at h ⊢
  repeat' (split at h <;> try contradiction)
  rename_i _ generated hg _ solved hs
  simpa only [generate_monotone hg fuel hf, solveFrom_monotone hs fuel hf] using h

end ModalityInference
