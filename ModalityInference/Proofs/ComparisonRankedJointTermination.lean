import ModalityInference.ComparisonRankedJoint
import ModalityInference.Proofs.ComparisonRankedModesTermination
import ModalityInference.Proofs.ComparisonPreparedDriverTermination

/-! Unconditional termination and completed-result stability of each fixed-rank
joint synthesis and exact-domain reconstruction. -/
namespace ModalityInference.ComparisonRankedJoint

open ComparisonPartialPropagation.Fuel

theorem run_settles (p : SchemePreparation.Prepared) (n : Nat) :
    Settles (fun fuel => run fuel p n) :=
  Settles.bind (ComparisonPreparedScalar.run_settles _)
    (fun _ => ComparisonRankedModes.run_settles _ _ _ _ _ _ _ _ _)

theorem run_terminates (p : SchemePreparation.Prepared) (n : Nat) :
    ∃ threshold result, result ≠ .exhausted ∧ ∀ fuel ≥ threshold, run fuel p n = result :=
  (run_settles p n).2

theorem run_stable {small large : Nat} {p : SchemePreparation.Prepared} {n : Nat}
    {result : RunResult ComparisonSignedQuerySolver.Solution}
    (h : run small p n = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large p n = result :=
  (run_settles p n).1 hle h hr

theorem synthesize_settles (p : SchemePreparation.Prepared) (n : Nat) :
    Settles (fun fuel => synthesize fuel p n) :=
  Settles.bind (ComparisonPreparedScalar.run_settles _)
    (fun _ => ComparisonRankedModes.synthesize_settles _ _ _ _ _ _ _ _ _)

theorem synthesize_terminates (p : SchemePreparation.Prepared) (n : Nat) :
    ∃ threshold result, result ≠ .exhausted ∧ ∀ fuel ≥ threshold, synthesize fuel p n = result :=
  (synthesize_settles p n).2

theorem synthesize_stable {small large : Nat} {p : SchemePreparation.Prepared} {n : Nat}
    {result : RunResult CompareSubstitution}
    (h : synthesize small p n = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    synthesize large p n = result :=
  (synthesize_settles p n).1 hle h hr

theorem compare_settles (ambient : Bounds) (source target : Scheme) (n : Nat) :
    Settles (fun fuel => compare fuel ambient source target n) :=
  Settles.bind (synthesize_settles _ _) (fun _ => Settles.pure _)

theorem compare_terminates (ambient : Bounds) (source target : Scheme) (n : Nat) :
    ∃ threshold result, result ≠ .exhausted ∧
      ∀ fuel ≥ threshold, compare fuel ambient source target n = result :=
  (compare_settles ambient source target n).2

theorem compare_stable {small large : Nat} {ambient : Bounds} {source target : Scheme} {n : Nat}
    {result : RunResult CompareSubstitution}
    (h : compare small ambient source target n = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    compare large ambient source target n = result :=
  (compare_settles ambient source target n).1 hle h hr

end ModalityInference.ComparisonRankedJoint
