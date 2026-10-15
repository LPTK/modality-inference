import ModalityInference.ComparisonJointAssembly
import ModalityInference.Proofs.ComparisonJointProgramSupport
import ModalityInference.Proofs.ComparisonJointGroupSupport
import ModalityInference.Proofs.ComparisonJointAxisSummary
import ModalityInference.Proofs.ComparisonJointAxisStates

/-! Exact scalar obligations and shared choices of the assembled group query. -/
namespace ModalityInference.ComparisonJointAssembly

open ComparisonPropagation ComparisonJointGroup ComparisonJointGuarded

private theorem foldMax_bounds (xs : List Nat) (start : Nat) :
    start ≤ xs.foldl max start ∧ ∀ v ∈ xs, v ≤ xs.foldl max start := by
  induction xs generalizing start with
  | nil => simp
  | cons a rest ih =>
    have hr := ih (max start a)
    simpa only [List.foldl_cons, List.mem_cons, forall_eq_or_imp] using
      And.intro ((le_max_left start a).trans hr.1)
        (And.intro ((le_max_right start a).trans hr.1) hr.2)

theorem modeBound_supported (input : Input) (offset : Nat) :
    Supported (List.range (offset + modeBound input))
      (input.locality ++ input.other ++ input.scalar) := by
  intro v hv
  have h := (foldMax_bounds _ 0).2 v hv
  simp only [List.mem_range, modeBound]
  omega

theorem input_supported (input : Input) (offset : Nat) :
    Supported (List.range (offset + modeBound input)) input.locality ∧
      Supported (List.range (offset + modeBound input)) input.other ∧
      Supported (List.range (offset + modeBound input)) input.scalar := by
  simpa only [ComparisonBoundarySupport.supported_iff, List.forall_mem_append, and_assoc] using
    modeBound_supported input offset

theorem scalarClauses_correct (choice : Fin constants → Bool) (store : Store count)
    (strategy : (Nat → Bool) → Nat → Bool) (clauses : CNF) :
    Holds choice store strategy (scalarClauses (heads := heads) clauses) ↔
      ∀ world, CNFHolds (strategy world) clauses := by
  simp [Holds, scalarClauses, ConstantsHold, ComparisonJointClauses.HeadClause.Holds,
    ComparisonJointClauses.literals, ClauseHolds, CNFHolds]

theorem oppositeClauses_parameters (side : Nat → Bool) (component : Bool)
    (count heads selectors : Nat) (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (store : Store retained)
    (strategy : (Nat → Bool) → Nat → Bool) (clauses : CNF) :
    Holds choice store strategy (oppositeClauses side component count heads selectors embedding clauses) ↔
      ∀ world, CNFHolds
        (fun i => ComparisonJointSummary.parameterWorld (ComparisonJointAxisSummary.decode embedding)
          choice (strategy world) (oppositeParameter selectors i))
        (ComparisonJointAxes.otherClauses side component count heads clauses) := by
  have he := ComparisonJointSummary.separateParameters_correct
    (ComparisonJointAxisSummary.decode embedding) choice store strategy
    ((ComparisonJointAxes.otherClauses side component count heads clauses).map fun clause =>
      (⟨.check [], clause.map fun literal => (oppositeParameter selectors literal.1, literal.2)⟩ :
        ComparisonJointClauses.JointClause heads retained))
  simpa [oppositeClauses, List.map_map, ComparisonJointClauses.Holds,
    ComparisonJointClauses.HeadClause.Holds, ComparisonJointClauses.literals,
    CNFHolds, ClauseHolds] using he

theorem oppositeClauses_correct {side : Nat → Bool} {component : Bool}
    {count heads selectors : Nat} (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (store : Store retained)
    (strategy : (Nat → Bool) → Nat → Bool) {clauses : CNF}
    (hs : clauses.length ≤ selectors) :
    Holds choice store strategy (oppositeClauses side component count heads selectors embedding clauses) ↔
      ∀ world, CNFHolds
        (ComparisonJointAxes.encode
          (ComparisonJointAxisSummary.parameterWorld embedding choice (fun _ => false)) (strategy world))
        (ComparisonJointAxes.otherClauses side component count heads clauses) := by
  rw [oppositeClauses_parameters]
  apply forall_congr' fun world => CNFPropagation.holds_congr ?_
  intro v hv
  rcases ComparisonJointAxes.otherClauses_atoms hv with ⟨i, hi, rfl⟩ | ⟨w, rfl, _, _⟩
  · have his : i < selectors := lt_of_lt_of_le hi hs
    simp [oppositeParameter, ComparisonJointSummary.parameterWorld, ComparisonJointAxisSummary.decode,
      ComparisonJointAxisSummary.parameterWorld,
      ComparisonJointAxes.encode, his, show (2 * i + 1) / 2 = i by omega]
  · simp [oppositeParameter, ComparisonJointSummary.parameterWorld, ComparisonJointAxisSummary.decode,
      ComparisonJointAxes.encode, show ¬selectors + w < selectors by omega]

theorem holds_append (choice : Fin constants → Bool) (store : Store count)
    (strategy : (Nat → Bool) → Nat → Bool)
    (left right : List (GuardedClause heads count constants)) :
    Holds choice store strategy (left ++ right) ↔
      Holds choice store strategy left ∧ Holds choice store strategy right := by
  simp only [Holds, List.mem_append, or_imp, forall_and]

theorem run_solution {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {count heads : Nat} {input : Input} {result : Result input count flex}
    (h : run fuel side flex count heads input = .success result) :
    ∃ solution, ComparisonJointGuarded.run fuel side flex (compile side count heads input) = .success solution ∧
      result = reconstruct side count heads input solution := by
  unfold run at h
  cases hs : ComparisonJointGuarded.run fuel side flex (compile side count heads input) with
  | exhausted | rejected => simp [hs, bind, RunResult.bind] at h
  | success solution =>
    simp only [hs, bind, RunResult.bind, pure, RunResult.success.injEq] at h
    exact ⟨solution, rfl, h.symm⟩

theorem run_compiled {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {count heads : Nat} {input : Input} {result : Result input count flex}
    (h : run fuel side flex count heads input = .success result) :
    result.solution.types.Polynomial heads ∧
      ModalSynthesis.Uniform side flex (fun world v => (result.solution.modes.substitute v).eval world) ∧
      Holds (fun i => result.solution.constants[i]) result.solution.types
        (fun world v => (result.solution.modes.substitute v).eval world) (compile side count heads input) := by
  obtain ⟨solution, hs, rfl⟩ := run_solution h
  exact ComparisonJointGuarded.run_sound hs

def CoordinateCorrect (side : Nat → Bool) (component : Bool) (heads selectors modes : Nat)
    (embedding : Fin selectors → Fin constants) (clauses : CNF)
    (boundary : Vector (Fin count) retained) (choice : Fin constants → Bool)
    (strategy : (Nat → Bool) → Nat → Bool) (retainedStore : Store retained) (full : Store count) : Prop :=
  full.Positive ∧ full.Supported (heads + 2 * (selectors + modes)) ∧
    ComparisonJointAxisSummary.OwnAxisSupported side component heads selectors full ∧
    ∀ input, ComparisonSelectorPropagation.SliceValid heads (selectors + modes)
      (ComparisonJointAxisSummary.parameterWorld embedding choice (strategy input))
      (ComparisonJointAxisSummary.program side component count heads selectors modes clauses) full ∧
      ComparisonBoundaryPropagation.BoundaryAgreement heads (selectors + modes)
        (ComparisonJointAxisSummary.parameterWorld embedding choice (strategy input)) boundary full retainedStore

theorem run_coordinates {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {count heads : Nat} {input : Input} {result : Result input count flex}
    (hl : ComparisonJointHorn.Linear (· < 4 * count) input.locality)
    (ho : ComparisonJointHorn.Linear (· < 4 * count) input.other)
    (h : run fuel side flex count heads input = .success result) :
    let choice := fun i => result.solution.constants[i]
    let strategy := fun world v => (result.solution.modes.substitute v).eval world
    CoordinateCorrect side true heads (input.locality.length + 1) (modeBound input)
        (localityEmbedding input) input.locality (boundary count) choice strategy result.solution.types result.locality ∧
      CoordinateCorrect side false heads (input.other.length + 1) (modeBound input)
        (otherEmbedding input) input.other (boundary count) choice strategy result.solution.types result.other := by
  obtain ⟨solution, hs, rfl⟩ := run_solution h
  have hp := ComparisonJointGuarded.run_sound hs
  have hc := hp.2.2
  simp only [compile, holds_append, and_assoc] at hc
  have hlocal := ComparisonJointAxisSummary.compile_sound
    (count := 4 * count) (heads := heads) (selectors := input.locality.length + 1)
    (modes := modeBound input) (clauses := input.locality) (embedding := localityEmbedding input)
    (boundary := boundary count) (retainedStore := solution.types)
    (Nat.le_succ _) (input_supported input (4 * count + heads)).1 hl hp.2.1.2 hp.1.2.1 hc.2.1
  have hother := ComparisonJointAxisSummary.compile_sound
    (count := 4 * count) (heads := heads) (selectors := input.other.length + 1)
    (modes := modeBound input) (clauses := input.other) (embedding := otherEmbedding input)
    (boundary := boundary count) (retainedStore := solution.types)
    (Nat.le_succ _) (input_supported input (4 * count + heads)).2.1 ho hp.2.1.2 hp.1.2.1 hc.2.2.1
  exact ⟨hlocal, hother⟩

theorem run_coordinate_clauses {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {count heads : Nat} {input : Input} {result : Result input count flex}
    (hl : ComparisonJointHorn.Linear (· < 4 * count) input.locality)
    (ho : ComparisonJointHorn.Linear (· < 4 * count) input.other)
    (h : run fuel side flex count heads input = .success result) :
    let choice := fun i => result.solution.constants[i]
    let strategy := fun world v => (result.solution.modes.substitute v).eval world
    (∀ headWorld inputWorld, CNFHolds (ComparisonJointAxes.valuation heads
      (ComparisonJointAxisSummary.coordinateState heads (localityEmbedding input) choice strategy result.locality)
      strategy headWorld inputWorld) input.locality) ∧
    (∀ headWorld inputWorld, CNFHolds (ComparisonJointAxes.valuation heads
      (ComparisonJointAxisSummary.coordinateState heads (otherEmbedding input) choice strategy result.other)
      strategy headWorld inputWorld) input.other) := by
  obtain ⟨hlocal, hother⟩ := run_coordinates hl ho h
  have hc := (run_compiled h).2.2
  simp only [compile, holds_append, and_assoc] at hc
  constructor
  · exact ComparisonJointAxes.selectors_sound
      (fun headWorld inputWorld => ComparisonJointAxisSummary.coordinateState_valid
        (Nat.le_succ _) hlocal.2.1 hl (hlocal.2.2.2 inputWorld).1 headWorld)
      ((oppositeClauses_correct (localityEmbedding input) _ _ _ (Nat.le_succ _)).mp hc.2.2.2.1)
  · exact ComparisonJointAxes.selectors_sound
      (fun headWorld inputWorld => ComparisonJointAxisSummary.coordinateState_valid
        (Nat.le_succ _) hother.2.1 ho (hother.2.2.2 inputWorld).1 headWorld)
      ((oppositeClauses_correct (otherEmbedding input) _ _ _ (Nat.le_succ _)).mp hc.2.2.2.2.1)

end ModalityInference.ComparisonJointAssembly
