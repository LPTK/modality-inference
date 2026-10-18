import ModalityInference.ComparisonDeclaredAnchors
import ModalityInference.Proofs.ComparisonCheckerTermination

/-! The whole-type certificate phase has a fixed completed result at every
sufficiently large fuel, and preserves all earlier completed results. -/
namespace ModalityInference.ComparisonDeclaredAnchors

open ComparisonPartialPropagation ComparisonPartialPropagation.Fuel

theorem checkPair_settles (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Result)
    (edges : List (ModExpr × ModExpr)) (graph : Graph) (pair : CompareTy × CompareTy) :
    Settles (fun fuel => checkPair fuel p shapes edges graph pair) := by
  unfold checkPair
  apply Settles.bind ⟨saturate_fuel_stable _ _ _ _, saturate_fuel_terminates _ _ _ _⟩
  intro candidate
  cases candidate <;> exact Settles.pure _

theorem checkPairs_settles (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Result)
    (edges : List (ModExpr × ModExpr)) (graph : Graph) (pairs : List (CompareTy × CompareTy)) :
    Settles (fun fuel => checkPairs fuel p shapes edges graph pairs) := by
  induction pairs with
  | nil => exact Settles.pure _
  | cons pair rest ih =>
      unfold checkPairs
      apply Settles.bind (checkPair_settles _ _ _ _ _)
      intro ok
      cases ok
      · exact Settles.pure _
      · exact ih

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

end ModalityInference.ComparisonDeclaredAnchors
