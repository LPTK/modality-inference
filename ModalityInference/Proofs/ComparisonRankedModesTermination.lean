import ModalityInference.ComparisonRankedModes
import ModalityInference.Proofs.ComparisonRankedTermination
import ModalityInference.Proofs.ComparisonSignedEndpointQueries

/-! Finite-rank joint synthesis settles for every finite input, without a
satisfiability premise. This is separate from stopping the search over ranks. -/
namespace ModalityInference.ComparisonRankedModes

open ComparisonPartialPropagation.Fuel

theorem prepare_settles (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty)) :
    Settles (fun fuel => prepare fuel Δ keys types names modeIds count basis endpoints) := by
  unfold prepare
  exact Settles.bind (compact_settles _ _) (fun _ =>
    Settles.bind (ComparisonSignedEndpoints.compileGuards_settles _) (fun _ => Settles.pure _))

private theorem solver_settles (input : ComparisonSignedSynthesis.Input) (flex : List Nat)
    (sources : List ComparisonSignedEndpointQueries.Source) :
    Settles (fun fuel => ComparisonSignedEndpointQueries.run fuel input
      ModalSynthesis.locality flex sources) := by
  refine ⟨fun hle h hr => ComparisonSignedEndpointQueries.run_stable hr h _ hle, ?_⟩
  apply Terminates.of_stable (fun hle h hr => ComparisonSignedEndpointQueries.run_stable hr h _ hle)
  obtain ⟨n, hn⟩ := ComparisonSignedEndpointQueries.run_terminates
    input ModalSynthesis.locality flex sources
  exact ⟨n, hn n le_rfl⟩

theorem run_settles (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalar : List ComparisonSignedEndpointQueries.Source) :
    Settles (fun fuel => run fuel Δ keys types names modeIds count basis endpoints scalar) :=
  Settles.bind (prepare_settles _ _ _ _ _ _ _ _) (fun _ => solver_settles _ _ _)

theorem prepare_stable {small large : Nat} {Δ : Bounds} {keys : List Nat}
    {types : List TypeVar} {names : List ModVar} {modeIds : List Nat} {count : Nat}
    {basis : ComparisonControls.Basis} {endpoints : List (Ty × Ty)}
    {result : RunResult ComparisonSignedEndpointQueries.Source}
    (h : prepare small Δ keys types names modeIds count basis endpoints = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    prepare large Δ keys types names modeIds count basis endpoints = result :=
  (prepare_settles Δ keys types names modeIds count basis endpoints).1 hle h hr

theorem run_terminates (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalar : List ComparisonSignedEndpointQueries.Source) :
    ∃ threshold result, result ≠ .exhausted ∧ ∀ fuel ≥ threshold,
      run fuel Δ keys types names modeIds count basis endpoints scalar = result :=
  (run_settles Δ keys types names modeIds count basis endpoints scalar).2

theorem run_stable {small large : Nat} {Δ : Bounds} {keys : List Nat}
    {types : List TypeVar} {names : List ModVar} {modeIds : List Nat} {count : Nat}
    {basis : ComparisonControls.Basis} {endpoints : List (Ty × Ty)}
    {scalar : List ComparisonSignedEndpointQueries.Source}
    {result : RunResult ComparisonSignedQuerySolver.Solution}
    (h : run small Δ keys types names modeIds count basis endpoints scalar = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    run large Δ keys types names modeIds count basis endpoints scalar = result :=
  (run_settles Δ keys types names modeIds count basis endpoints scalar).1 hle h hr

theorem synthesize_settles (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalar : List ComparisonSignedEndpointQueries.Source) :
    Settles (fun fuel => synthesize fuel Δ keys types names modeIds count basis endpoints scalar) := by
  apply Settles.bind (prepare_settles _ _ _ _ _ _ _ _)
  intro endpoint
  apply Settles.bind (solver_settles _ _ _)
  intro result
  split
  · exact Settles.rejected _
  · exact Settles.pure _

theorem synthesize_terminates (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalar : List ComparisonSignedEndpointQueries.Source) :
    ∃ threshold result, result ≠ .exhausted ∧ ∀ fuel ≥ threshold,
      synthesize fuel Δ keys types names modeIds count basis endpoints scalar = result :=
  (synthesize_settles Δ keys types names modeIds count basis endpoints scalar).2

theorem synthesize_stable {small large : Nat} {Δ : Bounds} {keys : List Nat}
    {types : List TypeVar} {names : List ModVar} {modeIds : List Nat} {count : Nat}
    {basis : ComparisonControls.Basis} {endpoints : List (Ty × Ty)}
    {scalar : List ComparisonSignedEndpointQueries.Source}
    {result : RunResult CompareSubstitution}
    (h : synthesize small Δ keys types names modeIds count basis endpoints scalar = result)
    (hr : result ≠ .exhausted) (hle : small ≤ large) :
    synthesize large Δ keys types names modeIds count basis endpoints scalar = result :=
  (synthesize_settles Δ keys types names modeIds count basis endpoints scalar).1 hle h hr

end ModalityInference.ComparisonRankedModes
