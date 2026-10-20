import ModalityInference.ComparisonRankedPrepared
import ModalityInference.Proofs.ComparisonRankedTermination

/-! The guarded fixed-rank interface settles on every finite input, preserving
successful and rejected results when fuel increases. -/
namespace ModalityInference.ComparisonRankedPrepared

open ComparisonPartialPropagation.Fuel

theorem run_settles (p : SchemePreparation.Prepared) (rank : Nat)
    (modes : List (Nat × ModExpr)) : Settles (fun fuel => run fuel p rank modes) := by
  cases hscope : modeScope p modes <;> cases hsupport : supported p modes <;>
    simp only [run, hscope, hsupport, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, bind, pure, RunResult.bind]
  all_goals try exact Settles.rejected _
  apply Settles.bind (backend_settles _)
  intro report
  split
  · exact Settles.rejected _
  exact Settles.bind (ComparisonRankedDecision.run_settles _ _ _ _ _ _ _)
    (fun _ => Settles.pure _)

theorem run_terminates (p : SchemePreparation.Prepared) (rank : Nat)
    (modes : List (Nat × ModExpr)) :
    ∃ threshold result, result ≠ .exhausted ∧
      ∀ fuel ≥ threshold, run fuel p rank modes = result :=
  (run_settles p rank modes).2

theorem run_stable {small large : Nat} {p : SchemePreparation.Prepared} {rank : Nat}
    {modes : List (Nat × ModExpr)} {result : RunResult CompareSubstitution}
    (h : run small p rank modes = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large p rank modes = result :=
  (run_settles p rank modes).1 hle h hr

theorem compare_settles (ambient : Bounds) (source target : Scheme) (rank : Nat)
    (modes : List (Nat × ModExpr)) :
    Settles (fun fuel => compare fuel ambient source target rank modes) :=
  Settles.bind (run_settles _ _ _) (fun _ => Settles.pure _)

theorem compare_terminates (ambient : Bounds) (source target : Scheme) (rank : Nat)
    (modes : List (Nat × ModExpr)) :
    ∃ threshold result, result ≠ .exhausted ∧
      ∀ fuel ≥ threshold, compare fuel ambient source target rank modes = result :=
  (compare_settles ambient source target rank modes).2

theorem compare_stable {small large : Nat} {ambient : Bounds} {source target : Scheme}
    {rank : Nat} {modes : List (Nat × ModExpr)} {result : RunResult CompareSubstitution}
    (h : compare small ambient source target rank modes = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    compare large ambient source target rank modes = result :=
  (compare_settles ambient source target rank modes).1 hle h hr

end ModalityInference.ComparisonRankedPrepared
