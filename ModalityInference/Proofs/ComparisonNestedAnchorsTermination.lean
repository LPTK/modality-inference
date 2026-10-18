import ModalityInference.ComparisonNestedAnchors
import ModalityInference.Proofs.ComparisonDeclaredAnchorsTermination

/-! The nested structural candidate and its whole-obligation certificate have
one stable completed result at sufficiently large fuel. -/
namespace ModalityInference.ComparisonNestedAnchors

open ComparisonPartialPropagation ComparisonPartialPropagation.Fuel
open ComparisonDeclaredAnchors

theorem attempt_settles (p : SchemePreparation.Prepared) :
    Settles (fun fuel => attempt fuel p) := by
  simp only [attempt, bind, pure, RunResult.bind]
  split
  · exact Settles.pure _
  · apply Settles.bind ⟨shapePrepare_stable _, ComparisonShapeSolver.prepare_eventually _⟩
    intro shapes
    dsimp only
    split
    · exact Settles.pure _
    · apply Settles.bind ⟨modeEdges_fuel_stable _ _, modeEdges_fuel_terminates _ _⟩
      intro edges
      apply Settles.bind (backend_settles _)
      intro report
      split
      · exact Settles.pure _
      · apply Settles.bind (checkPairs_settles _ _ _ _ _)
        intro ok
        cases ok <;> exact Settles.pure _

theorem run_settles (source target : Scheme) :
    Settles (fun fuel => run fuel source target) := by
  unfold run
  apply Settles.bind (attempt_settles _)
  intro candidate
  cases candidate
  · exact Settles.rejected _
  · exact Settles.pure _

end ModalityInference.ComparisonNestedAnchors
