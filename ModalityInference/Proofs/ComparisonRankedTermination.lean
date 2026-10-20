import ModalityInference.ComparisonRankedDecision
import ModalityInference.Proofs.ComparisonPreparedQueriesTermination
import ModalityInference.Proofs.ComparisonSignedQuerySolver

/-! Fixed-rank preparation and solving terminate on every finite input.
Completed results, including rejection, are preserved when fuel increases. -/
namespace ModalityInference.ComparisonRankedDecision

open ComparisonPartialPropagation.Fuel

theorem prepare_settles (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    Settles (fun fuel => prepare fuel Δ input types names count modes endpoints) := by
  unfold prepare
  apply Settles.bind (compact_settles _ _)
  intro original
  apply Settles.bind (ComparisonSignedEndpoints.compileGuards_settles _)
  exact fun _ => Settles.pure _

theorem prepare_stable {small large : Nat} {Δ : Bounds}
    {input : ComparisonSignedSynthesis.Input} {types : List TypeVar} {names : List ModVar}
    {count : Nat} {modes : ModVar → ModExpr} {endpoints : List (Ty × Ty)}
    {result : RunResult ComparisonSignedQueries.Query}
    (h : prepare small Δ input types names count modes endpoints = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    prepare large Δ input types names count modes endpoints = result :=
  (prepare_settles Δ input types names count modes endpoints).1 hle h hr

theorem run_settles (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    Settles (fun fuel => run fuel Δ input types names count modes endpoints) := by
  unfold run
  apply Settles.bind (prepare_settles Δ input types names count modes endpoints)
  intro q
  have hs : Stable (fun fuel => ComparisonSignedQuerySolver.run fuel input [q] []) :=
    fun hle h hr => ComparisonSignedQuerySolver.run_stable hr h _ hle
  refine ⟨hs, Terminates.of_stable hs ?_⟩
  obtain ⟨threshold, hthreshold⟩ := ComparisonSignedQuerySolver.run_terminates input [q] []
  exact ⟨threshold, hthreshold threshold le_rfl⟩

/-- The fixed-rank solver eventually returns one completed result on every
input, without a semantic satisfiability or definedness premise. -/
theorem run_terminates (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    ∃ threshold result, result ≠ .exhausted ∧ ∀ fuel ≥ threshold,
      run fuel Δ input types names count modes endpoints = result :=
  (run_settles Δ input types names count modes endpoints).2

/-- Increasing fuel preserves both successful and rejected completed results. -/
theorem run_stable {small large : Nat} {Δ : Bounds}
    {input : ComparisonSignedSynthesis.Input} {types : List TypeVar} {names : List ModVar}
    {count : Nat} {modes : ModVar → ModExpr} {endpoints : List (Ty × Ty)}
    {result : RunResult ComparisonSignedQuerySolver.Solution}
    (h : run small Δ input types names count modes endpoints = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large Δ input types names count modes endpoints = result :=
  (run_settles Δ input types names count modes endpoints).1 hle h hr

end ModalityInference.ComparisonRankedDecision
