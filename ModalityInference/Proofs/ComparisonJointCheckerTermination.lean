import ModalityInference.ComparisonJointChecker
import ModalityInference.Proofs.ComparisonCheckerTermination
import ModalityInference.Proofs.ComparisonJointBatch

/-! Fuel stability and eventual completion of the shared comparison driver.
The results cover arbitrary input schemes and include both successful and
rejected completed outcomes. -/
namespace ModalityInference

open ComparisonPartialPropagation.Fuel

namespace ComparisonJointGroup

theorem leaf_settles (heads : List TypeVar) (names : List Nat) (coordinate : ComparisonControls.Coordinate)
    (v : TypeVar) : Settles (fun _ => leaf heads names coordinate v) := by
  cases v <;> simp only [leaf]
  all_goals repeat' first | exact Settles.pure _ | exact Settles.rejected _ | split

theorem fixed_settles (heads : List TypeVar) (coordinate : ComparisonControls.Coordinate)
    (a : ComparisonGroups.Atom) : Settles (fun _ => fixed heads coordinate a) := by
  unfold fixed
  split
  · exact Settles.rejected _
  · exact Settles.pure _

theorem fixedBound_settles (heads : List TypeVar) (coordinate : ComparisonControls.Coordinate)
    (pair : ComparisonGroups.Inequality) : Settles (fun _ => fixedBound heads coordinate pair) := by
  unfold fixedBound
  apply Settles.bind (fixed_settles _ _ _)
  intro left
  apply Settles.bind (fixed_settles _ _ _)
  intro right
  exact Settles.pure _

theorem action_settles (heads : Nat) (coordinate : ComparisonControls.Coordinate) (m : ModExpr) :
    Settles (fun fuel => action fuel heads coordinate m) := by
  unfold action
  apply Settles.bind (compact_settles _ _)
  intro lower
  apply Settles.bind (compact_settles _ _)
  intro upper
  exact Settles.pure _

theorem bound_settles (heads : List TypeVar) (names : List Nat)
    (coordinate : ComparisonControls.Coordinate) (theory : CNF) (pair : ComparisonGroups.Inequality) :
    Settles (fun fuel => bound fuel heads names coordinate theory pair) := by
  unfold bound
  apply Settles.bind (leaf_settles _ _ _ _)
  intro left
  apply Settles.bind (leaf_settles _ _ _ _)
  intro right
  apply Settles.bind (action_settles _ _ _)
  intro leftAction
  apply Settles.bind (action_settles _ _ _)
  intro rightAction
  exact Settles.pure _

theorem coordinate_settles (assumptions required : Bounds) (g : ComparisonGroups.Group)
    (c : ComparisonControls.Coordinate) : Settles (fun fuel => coordinate fuel assumptions required g c) := by
  unfold coordinate
  apply Settles.bind (Settles.mapM _ _ (fun _ => fixedBound_settles _ _ _))
  intro declared
  apply Settles.bind (compact_settles _ _)
  intro theory
  apply Settles.bind (Settles.mapM _ _ (fun _ => bound_settles _ _ _ _ _))
  intro goals
  exact Settles.pure _

theorem prepare_settles (assumptions required : Bounds) (g : ComparisonGroups.Group) :
    Settles (fun fuel => prepare fuel assumptions required g) := by
  unfold prepare
  apply Settles.bind (coordinate_settles _ _ _ _)
  intro nominal
  apply Settles.bind (coordinate_settles _ _ _ _)
  intro locality
  apply Settles.bind (coordinate_settles _ _ _ _)
  intro affinity
  apply Settles.bind (coordinate_settles _ _ _ _)
  intro uniqueness
  apply Settles.bind (compact_settles _ _)
  intro scalar
  exact Settles.pure _

end ComparisonJointGroup

namespace ComparisonJointBatchReification

theorem prepare_settles (assumptions required : Bounds) (groups : List ComparisonGroups.Group) :
    Settles (fun fuel => prepare fuel assumptions required groups) := by
  unfold prepare
  apply Settles.mapM
  intro group
  apply Settles.bind (ComparisonJointGroup.prepare_settles _ _ _)
  intro input
  exact Settles.pure _

end ComparisonJointBatchReification

namespace ComparisonJointBatch

theorem run_settles (side : Nat → Bool) (flex : List Nat) (groups : List Entry)
    (minimumModes : Nat := 0) (scalar : CNF := []) :
    Settles (fun fuel => run fuel side flex groups minimumModes scalar) := by
  have hs : Stable (fun fuel => run fuel side flex groups minimumModes scalar) :=
    fun hle h hr => run_stable hr h _ hle
  refine ⟨hs, Terminates.of_stable hs ?_⟩
  obtain ⟨n, hn⟩ := run_terminates side flex groups minimumModes scalar
  exact ⟨n, hn n le_rfl⟩

end ComparisonJointBatch

namespace ComparisonJointElimination

theorem run_settles (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (templates : ComparisonSkeleton.Templates) (reduced : ComparisonReduction.State)
    (allowed : List ModVar) (modeIds : List Nat) (minimumModes : Nat := 0) :
    Settles (fun fuel => run fuel p shapes templates reduced allowed modeIds minimumModes) := by
  unfold run
  apply Settles.bind (ComparisonGroups.collect_settles _ _ _ _)
  intro groups
  apply Settles.bind (ComparisonJointBatchReification.prepare_settles _ _ _)
  intro compiled
  apply Settles.bind (compact_settles _ _)
  intro scalar
  apply Settles.bind (ComparisonJointBatch.run_settles _ _ _ _ _)
  intro batch
  split
  · exact Settles.pure _
  · exact Settles.rejected _

theorem run_terminates (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (templates : ComparisonSkeleton.Templates) (reduced : ComparisonReduction.State)
    (allowed : List ModVar) (modeIds : List Nat) (minimumModes : Nat := 0) :
    ∃ n result, result ≠ .exhausted ∧
      ∀ fuel ≥ n, run fuel p shapes templates reduced allowed modeIds minimumModes = result :=
  (run_settles p shapes templates reduced allowed modeIds minimumModes).2

theorem run_stable {small large minimumModes : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {allowed : List ModVar} {modeIds : List Nat}
    {result : RunResult ComparisonJointBatchReification.Output}
    (h : run small p shapes templates reduced allowed modeIds minimumModes = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large p shapes templates reduced allowed modeIds minimumModes = result :=
  (run_settles p shapes templates reduced allowed modeIds minimumModes).1 hle h hr

end ComparisonJointElimination

namespace ComparisonJointChecker

theorem propagate_settles (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved) :
    Settles (fun fuel => propagate fuel p shapes) := by
  unfold propagate
  apply Settles.bind (knownTotal_settles _ _)
  intro known
  apply Settles.bind ⟨ComparisonReduction.prepare_fuel_stable _ _ _ _ _,
    ComparisonReduction.prepare_fuel_terminates _ _ _ _ _⟩
  intro reduced
  apply Settles.bind (ComparisonJointElimination.run_settles _ _ _ _ _ _ _)
  intro result
  exact Settles.pure _

theorem run_settles (source target : Scheme) : Settles (fun fuel => run fuel source target) := by
  unfold run
  split
  · exact Settles.rejected _
  · apply Settles.bind ⟨shapePrepare_stable _, ComparisonShapeSolver.prepare_eventually _⟩
    intro shapes
    cases shapes with
    | infeasibleAssumptions => exact Settles.rejected _
    | solved shapes =>
      apply Settles.bind (propagate_settles _ _)
      intro action
      exact Settles.pure _

theorem propagate_terminates (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, propagate fuel p shapes = result :=
  (propagate_settles p shapes).2

theorem propagate_stable {small large : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {result : RunResult CompareSubstitution}
    (h : propagate small p shapes = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    propagate large p shapes = result := (propagate_settles p shapes).1 hle h hr

/-- Every input has a fixed completed outcome once enough fuel is supplied. -/
theorem run_terminates (source target : Scheme) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, run fuel source target = result :=
  (run_settles source target).2

theorem run_stable {small large : Nat} {source target : Scheme} {result : RunResult CompareSubstitution}
    (h : run small source target = result) (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large source target = result := (run_settles source target).1 hle h hr

theorem run_monotone {small large : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run small source target = .success result) (hle : small ≤ large) :
    run large source target = .success result := run_stable h (by simp) hle

end ComparisonJointChecker
end ModalityInference
