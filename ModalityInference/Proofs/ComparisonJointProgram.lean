import ModalityInference.ComparisonJointProgram
import ModalityInference.Proofs.ComparisonJointHorn
import ModalityInference.Proofs.ComparisonJointNominal
import ModalityInference.ComparisonJointAxes
import ModalityInference.Proofs.ComparisonJointEncoding

namespace ModalityInference.ComparisonJointProgram

open ComparisonPropagation ComparisonJointHorn ComparisonSelectorPropagation ComparisonJointClauses

theorem renameParameters_correct (parameters : Nat → Nat) (obligation : Obligation count)
    (world : Nat → Bool) (values : Fin count → Prop) :
    (renameParameters parameters obligation).Holds world values ↔
      obligation.Holds (world ∘ parameters) values := by
  cases obligation <;> simp only [renameParameters, Obligation.Holds, rename_correct]

theorem fold_valid {size : Nat} {store : Store count} (hs : store.Supported size)
    (obligations : List (Obligation count)) (program : Program count) :
    (obligations.foldl (Program.add size) program).Valid store ↔
      program.Valid store ∧ ∀ obligation ∈ obligations, ∀ world,
        obligation.Holds world (fun v => CNFHolds world store[v]) := by
  induction obligations generalizing program with
  | nil => simp
  | cons obligation rest ih =>
    simp only [List.foldl_cons, ih, Program.add_valid hs, List.forall_mem_cons, and_assoc]

noncomputable def values (store : Store count) (world : Nat → Bool) : Fin count → Bool := by
  classical
  exact fun v => decide (CNFHolds world store[v])

@[simp] theorem values_true (store : Store count) (world : Nat → Bool) (v : Fin count) :
    values store world v = true ↔ CNFHolds world store[v] := by
  classical
  simp [values]

theorem compile_valid {size : Nat} {decode : Nat → Option (Fin count)}
    {parameters : Nat → Nat} {clauses : CNF} {store : Store count}
    (hs : store.Supported size)
    (hc : Linear (fun v => (decode v).isSome = true) clauses) :
    (compile size decode parameters clauses).Valid store ↔
      ∀ world, CNFHolds (valuation decode (values store world) (world ∘ parameters)) clauses := by
  rw [compile, fold_valid hs]
  simp only [Program.empty_valid, true_and, List.forall_mem_map, renameParameters_correct]
  simp_rw [← values_true store]
  exact ⟨fun h world c hm => (compileClause_correct (hc c hm) _ _).mp (h c hm world),
    fun h c hm world => (compileClause_correct (hc c hm) _ _).mpr (h world c hm)⟩

@[simp] theorem axisState_even (i : Fin count) : axisState count (2 * i.val) = some i := by
  simp [axisState, i.isLt]

@[simp] theorem axisState_odd (count i : Nat) : axisState count (2 * i + 1) = none := by
  simp [axisState]

theorem axisState_above {count i : Nat} (hi : count ≤ i) : axisState count (2 * i) = none := by
  simp [axisState, Nat.not_lt.mpr hi]

theorem axisParameter_head (count heads selectors i : Nat) (hi : i < heads) :
    axisParameter count heads selectors (2 * (count + i)) = i := by
  simp [axisParameter, hi]

@[simp] theorem axisParameter_mode (count heads selectors i : Nat) :
    axisParameter count heads selectors (2 * (count + heads + i)) =
      heads + 2 * (selectors + i) := by
  simp [axisParameter]

@[simp] theorem axisParameter_selector (count heads selectors i : Nat) :
    axisParameter count heads selectors (2 * i + 1) = heads + 2 * i := by
  simp [axisParameter]

theorem diagonal_slice_iff {size : Nat} {store : Store count}
    (hs : store.Supported size) (heads parameters : Nat) (choice : Nat → Bool)
    (condition : CNF) (source target : Fin count) :
    (∀ world, Slice heads parameters choice (fun i => world (2 * i)) →
      Slice heads parameters choice (fun i => world (2 * i + 1)) →
      CNFHolds world (diagonal size condition) →
      CNFHolds (fun i => world (2 * i)) store[source] →
      CNFHolds (fun i => world (2 * i + 1)) store[target]) ↔
      ∀ world, Slice heads parameters choice world → CNFHolds world condition →
        CNFHolds world store[source] → CNFHolds world store[target] := by
  constructor
  · intro h world hw hc hv
    simpa using h (fun i => world (i / 2)) (by simpa using hw) (by simpa using hw)
      ((diagonal_correct _ _ _).mpr ⟨by simpa using hc, by simp⟩) (by simpa using hv)
  · intro h world hl _ hr hv
    obtain ⟨hc, he⟩ := (diagonal_correct _ _ _).mp hr
    exact (CNFPropagation.holds_congr
      (fun i hi => he i (List.mem_range.mp (hs target i hi)))).mp
        (h (fun i => world (2 * i)) hl hc hv)

theorem add_sliceValid {size : Nat} {program : Program count} {store : Store count}
    (hs : store.Supported size) (heads parameters : Nat) (choice : Nat → Bool)
    (obligation : Obligation count) :
    SliceValid heads parameters choice (program.add size obligation) store ↔
      SliceValid heads parameters choice program store ∧
        ∀ world, Slice heads parameters choice world →
          obligation.Holds world (fun v => CNFHolds world store[v]) := by
  cases obligation <;> simp only [sliceValid_iff, Program.add, lower_update, upper_update,
    List.forall_mem_cons, diagonal_slice_iff hs, meet_correct, forall_and, Obligation.Holds]
  all_goals tauto

theorem fold_sliceValid {size : Nat} {store : Store count} (hs : store.Supported size)
    (heads parameters : Nat) (choice : Nat → Bool)
    (obligations : List (Obligation count)) (program : Program count) :
    SliceValid heads parameters choice (obligations.foldl (Program.add size) program) store ↔
      SliceValid heads parameters choice program store ∧ ∀ obligation ∈ obligations,
        ∀ world, Slice heads parameters choice world →
          obligation.Holds world (fun v => CNFHolds world store[v]) := by
  induction obligations generalizing program with
  | nil => simp
  | cons obligation rest ih =>
    simp only [List.foldl_cons, ih, add_sliceValid hs, List.forall_mem_cons, and_assoc]

theorem compile_sliceValid {size : Nat} {decode : Nat → Option (Fin count)}
    {parameters : Nat → Nat} {clauses : CNF} {store : Store count}
    (hs : store.Supported size)
    (hc : Linear (fun v => (decode v).isSome = true) clauses)
    (heads scalars : Nat) (choice : Nat → Bool) :
    SliceValid heads scalars choice (compile size decode parameters clauses) store ↔
      ∀ world, Slice heads scalars choice world →
        CNFHolds (valuation decode (values store world) (world ∘ parameters)) clauses := by
  rw [compile, fold_sliceValid hs]
  simp only [empty_sliceValid, true_and, List.forall_mem_map, renameParameters_correct]
  simp_rw [← values_true store]
  exact ⟨fun h world hw c hm => (compileClause_correct (hc c hm) _ _).mp (h c hm world hw),
    fun h c hm world hw => (compileClause_correct (hc c hm) _ _).mpr (h world hw c hm)⟩

def axisInputs (heads selectors : Nat) (world : Nat → Bool) (i : Nat) : Bool :=
  if i < heads then world i else world (heads + 2 * (selectors + (i - heads)))

theorem axis_valuation_even (heads selectors : Nat) (state : Fin count → Bool)
    (world : Nat → Bool) (i : Nat) :
    valuation (axisState count) state (world ∘ axisParameter count heads selectors) (2 * i) =
      ComparisonJointEncoding.valuation state (axisInputs heads selectors world) i := by
  by_cases hi : i < count
  all_goals simp [valuation, axisState, axisParameter, ComparisonJointEncoding.valuation, axisInputs, hi]
  split <;> split <;> simp_all [Nat.sub_sub] <;> omega

theorem axis_valuation (heads selectors : Nat) (state : Fin count → Bool)
    (world : Nat → Bool) :
    valuation (axisState count) state (world ∘ axisParameter count heads selectors) =
      ComparisonJointAxes.encode (fun i => world (heads + 2 * i))
        (ComparisonJointEncoding.valuation state (axisInputs heads selectors world)) := by
  funext v
  have hv : v = 2 * (v / 2) ∨ v = 2 * (v / 2) + 1 := by omega
  rcases hv with hv | hv <;> rw [hv]
  · simp [ComparisonJointAxes.encode, axis_valuation_even]
  · simp [ComparisonJointAxes.encode, valuation]

end ModalityInference.ComparisonJointProgram
