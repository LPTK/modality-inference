import ModalityInference.ComparisonPreparedDriver
import ModalityInference.Proofs.ComparisonPreparedQueriesTermination
import ModalityInference.Proofs.ComparisonGuardedEndpointQueries
import ModalityInference.Proofs.ComparisonPreparedScalarPreflight

/-! Prepared structural comparison eventually returns a fixed completed result
for arbitrary inputs. Every completed result is preserved when fuel increases,
including rejection by structural selection or finite image assembly. -/
namespace ModalityInference

open ComparisonPartialPropagation.Fuel

namespace ComparisonPreparedScalar

theorem run_settles (p : SchemePreparation.Prepared) :
    Settles (fun fuel => run fuel p) := by
  unfold run
  apply Settles.bind (compact_settles _ _)
  intro theory
  apply Settles.bind (compact_settles _ _)
  intro goals
  exact Settles.pure _

end ComparisonPreparedScalar

namespace ComparisonGuardedEndpointQueries

theorem run_settles (input : ComparisonSignedSynthesis.Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (shapeCondition : CNF) :
    Settles (fun fuel => run fuel input side flex sources shapeCondition) := by
  have hs : Stable (fun fuel => run fuel input side flex sources shapeCondition) :=
    fun hle h hr => run_stable hr h _ hle
  refine ⟨hs, Terminates.of_stable hs ?_⟩
  obtain ⟨threshold, hthreshold⟩ := run_terminates input side flex sources shapeCondition
  exact ⟨threshold, hthreshold threshold le_rfl⟩

end ComparisonGuardedEndpointQueries

namespace ComparisonPreparedDriver

theorem propagate_settles (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    Settles (fun fuel => propagate fuel first p solved) := by
  unfold propagate
  apply Settles.bind (ComparisonPreparedQueries.compile_settles _ _ _)
  intro program
  apply Settles.bind (ComparisonPreparedScalar.run_settles _)
  intro scalar
  apply Settles.bind (ComparisonGuardedEndpointQueries.run_settles _ _ _ _ _)
  intro result
  dsimp only
  split
  · exact Settles.rejected _
  · split
    · exact Settles.rejected _
    · exact Settles.pure _

theorem run_settles (source target : Scheme) :
    Settles (fun fuel => run fuel source target) := by
  unfold run
  split
  · exact Settles.rejected _
  · apply Settles.bind (ComparisonPreparedScalarPreflight.run_settles _)
    intro _
    apply Settles.bind ⟨shapePrepare_stable _, ComparisonShapeSolver.prepare_eventually _⟩
    intro shapes
    cases shapes with
    | infeasibleAssumptions => exact Settles.rejected _
    | solved solved =>
        apply Settles.bind (propagate_settles _ _ _)
        intro result
        exact Settles.pure _

theorem propagate_terminates (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    ∃threshold result, result ≠ .exhausted ∧
      ∀fuel ≥ threshold, propagate fuel first p solved = result :=
  (propagate_settles first p solved).2

theorem propagate_stable {small large first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {result : RunResult CompareSubstitution}
    (h : propagate small first p solved = result) (hr : result ≠ .exhausted)
    (hle : small ≤ large) : propagate large first p solved = result :=
  (propagate_settles first p solved).1 hle h hr

theorem run_terminates (source target : Scheme) :
    ∃threshold result, result ≠ .exhausted ∧
      ∀fuel ≥ threshold, run fuel source target = result :=
  (run_settles source target).2

theorem run_stable {small large : Nat} {source target : Scheme}
    {result : RunResult CompareSubstitution} (h : run small source target = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) : run large source target = result :=
  (run_settles source target).1 hle h hr

theorem run_monotone {small large : Nat} {source target : Scheme}
    {result : CompareSubstitution} (h : run small source target = .success result)
    (hle : small ≤ large) : run large source target = .success result :=
  run_stable h (by simp) hle

end ComparisonPreparedDriver

end ModalityInference
