import ModalityInference.ComparisonParametricPropagation
import ModalityInference.Proofs.ComparisonSelectorPropagation

namespace ModalityInference.ComparisonParametricPropagation

open ComparisonPropagation ComparisonSelectorPropagation

/-- A complementary parameter pair prevents the global seed from forcing the
value on any valid parameter slice. One dummy pair suffices when needed. -/
theorem extend_one_of_parameters {heads parameters : Nat} {choice : Nat → Bool}
    {store : Store count} (hparam : 0 < parameters) :
    ∀ v : Fin count, CNFHolds (fun _ => true) (extend heads parameters choice store)[v] := by
  intro v
  exact (extend_correct _ _ _ _ _ _).mpr (Or.inr
    ((outside_correct _ _ _ _).mpr ⟨0, hparam, rfl⟩))

/-- Each valid parameter slice has its own least positive head solution,
including the constant zero and one formulas. -/
theorem slice_least {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (hparam : 0 < parameters) (hp : store.Positive) (hs : store.Supported heads)
    (hc : SliceClosed heads parameters choice program store)
    {valuation : Nat → Bool} (hv : Slice heads parameters choice valuation) (v : Fin count) :
    CNFHolds valuation (closure heads parameters program)[v] → CNFHolds valuation store[v] := by
  intro h
  have hle := propagate_least_closed (extend_positive hp) (extend_supported hs)
    (extend_one_of_parameters hparam) (prepareProgram_closed_extend hc)
  exact ((extend_correct _ _ _ _ _ _).mp (hle v valuation h)).resolve_right (outside_false hv)

theorem residual_complete {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (hparam : 0 < parameters) (hp : store.Positive) (hs : store.Supported heads)
    (hc : SliceValid heads parameters choice program store)
    {valuation : Nat → Bool} (hv : Slice heads parameters choice valuation) :
    CNFHolds valuation (residualQuery heads parameters program) := by
  rw [residualQuery, residual_correct]
  refine ⟨(implies_correct _ _ _).mpr (fun _ => (hc.2 valuation hv).1), ?_⟩
  intro v h
  simp only [prepareProgram, Fin.getElem_fin, Vector.getElem_ofFn]
  exact (implies_correct _ _ _).mpr fun _ => (hc.2 valuation hv).2 v
    (slice_least hparam hp hs hc.1 hv v h)

theorem closure_positive (heads parameters : Nat) (program : Program count) :
    (closure heads parameters program).Positive := propagate_positive _ _ _

theorem closure_supported (heads parameters : Nat) (program : Program count) :
    (closure heads parameters program).Supported (heads + 2 * parameters) := propagate_supported _ _ _

theorem residual_sound {heads parameters : Nat} {choice : Nat → Bool} {program : Program count}
    (h : ∀ valuation, Slice heads parameters choice valuation →
      CNFHolds valuation (residualQuery heads parameters program)) :
    (witness heads parameters choice program).Positive ∧
      (witness heads parameters choice program).Supported heads ∧
        SliceValid heads parameters choice program (witness heads parameters choice program) := by
  have hc : SliceValid heads parameters choice program (closure heads parameters program) :=
    prepareProgram_slice_valid (propagate_closed _ _) h
  have hs := closure_supported heads parameters program
  have hp := closure_positive heads parameters program
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_positive (heads := heads) (choice := choice) (hp v)
  · intro v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_supported heads choice (closure heads parameters program)[v]
  · apply hc.congr
    intro valuation hparam v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      (specialize_of_slice (hs v) hparam).symm

theorem residual_iff {heads parameters : Nat} (hparam : 0 < parameters)
    (choice : Nat → Bool) (program : Program count) :
    (∀ valuation, Slice heads parameters choice valuation →
      CNFHolds valuation (residualQuery heads parameters program)) ↔
      ∃ store : Store count, store.Positive ∧ store.Supported heads ∧
        SliceValid heads parameters choice program store := by
  exact ⟨fun h => ⟨witness heads parameters choice program, residual_sound h⟩,
    fun ⟨_, hp, hs, h⟩ _ hv => residual_complete hparam hp hs h hv⟩

end ModalityInference.ComparisonParametricPropagation
