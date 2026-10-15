import ModalityInference.Proofs.ComparisonJointAxisSummary

namespace ModalityInference.ComparisonJointAxisSummary

open ComparisonPropagation ComparisonSelectorPropagation ComparisonBoundaryPropagation
open ComparisonJointAxes ComparisonJointProgram ComparisonJointHorn

/-- Evaluate a reconstructed store at the fixed shared selectors and the one
joint modality strategy. Head observations remain independent inputs. -/
noncomputable def coordinateState (heads : Nat) (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (store : Store count) : State count :=
  fun headWorld input => values store (select heads (parameterWorld embedding choice (strategy input)) headWorld)

theorem selected_keep_eq {side : Nat → Bool} {component : Bool} {heads selectors : Nat}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} (hm : ModeUniform side strategy)
    {left right : Nat → Bool} (he : ∀ v, side v = component → left v = right v)
    (headWorld : Nat → Bool) {v : Nat} (hv : keep side component heads selectors v = true) :
    select heads (parameterWorld embedding choice (strategy left)) headWorld v =
      select heads (parameterWorld embedding choice (strategy right)) headWorld v := by
  by_cases hh : v < heads
  · simp [select, hh]
  · simp only [select, hh, ↓reduceIte, fixedValue]
    by_cases hs : (v - heads) / 2 < selectors
    · simp [parameterWorld, decode, hs]
    · have hside : side ((v - heads) / 2 - selectors) = component := by
        simpa [keep, hh, hs] using hv
      have heq := hm left right ((v - heads) / 2 - selectors)
        (fun w hw => he w (hw.trans hside))
      simp [parameterWorld, decode, hs, heq]

theorem coordinateState_uniform {side : Nat → Bool} {component : Bool} {heads selectors : Nat}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} {store : Store count}
    (hm : ModeUniform side strategy) (hs : OwnAxisSupported side component heads selectors store) :
    StateUniform side component (coordinateState heads embedding choice strategy store) := by
  intro headWorld left right he v
  simp only [coordinateState, values]
  congr 1
  apply propext
  exact CNFPropagation.holds_congr fun i hi => selected_keep_eq hm he headWorld (hs v i hi)

theorem axisInputs_select (heads : Nat) (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (modes headWorld : Nat → Bool) :
    axisInputs heads selectors (select heads (parameterWorld embedding choice modes) headWorld) =
      (fun v => if v < heads then headWorld v else modes (v - heads)) := by
  funext v
  by_cases hv : v < heads
  · simp [axisInputs, hv, select]
  · simp [axisInputs, hv, select, fixedValue,
      show ¬heads + 2 * (selectors + (v - heads)) < heads by omega]

theorem coordinate_valuation (heads : Nat) (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (store : Store count) (headWorld input : Nat → Bool) :
    ComparisonJointEncoding.valuation
      (values store (select heads (parameterWorld embedding choice (strategy input)) headWorld))
      (axisInputs heads selectors (select heads (parameterWorld embedding choice (strategy input)) headWorld)) =
    ComparisonJointAxes.valuation heads (coordinateState heads embedding choice strategy store)
      strategy headWorld input := by
  rw [axisInputs_select]
  funext v
  by_cases hv : v < count
  · simp [ComparisonJointEncoding.valuation, ComparisonJointAxes.valuation, coordinateState, hv]
  · by_cases hh : v < count + heads
    · simp [ComparisonJointEncoding.valuation, ComparisonJointAxes.valuation, hv, hh,
        show v - count < heads by omega]
    · simp [ComparisonJointEncoding.valuation, ComparisonJointAxes.valuation, hv, hh,
        show ¬v - count < heads by omega, Nat.sub_sub]

theorem coordinateState_valid {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} {store : Store count} {input : Nat → Bool}
    (hselectors : clauses.length ≤ selectors)
    (hs : store.Supported (heads + 2 * (selectors + modes)))
    (hc : Linear (· < count) clauses)
    (hv : SliceValid heads (selectors + modes)
      (parameterWorld embedding choice (strategy input))
      (program side component count heads selectors modes clauses) store)
    (headWorld : Nat → Bool) :
    CNFHolds (ComparisonJointAxes.encode (parameterWorld embedding choice (fun _ => false))
      (ComparisonJointAxes.valuation heads (coordinateState heads embedding choice strategy store)
        strategy headWorld input)) (ownClauses side component count heads clauses) := by
  have hh := (axisProgram_sliceValid hs hc _).mp hv _
    (select_slice heads (selectors + modes) (parameterWorld embedding choice (strategy input)) headWorld)
  rw [coordinate_valuation, ownClauses_holds] at hh
  rw [ownClauses_holds]
  intro i hi
  have hs : i < selectors := by omega
  simpa [select, fixedValue, parameterWorld, decode, hs,
    show ¬heads + 2 * i < heads by omega] using hh i hi

theorem coordinateState_boundary {count heads selectors modes : Nat}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} {store : Store count}
    {boundary : Vector (Fin count) retained} {retainedStore : Store retained} {input : Nat → Bool}
    (hs : retainedStore.Supported heads)
    (ha : BoundaryAgreement heads (selectors + modes)
      (parameterWorld embedding choice (strategy input)) boundary store retainedStore)
    (headWorld : Nat → Bool) (j : Fin retained) :
    coordinateState heads embedding choice strategy store headWorld input boundary[j] =
      values retainedStore headWorld j := by
  simp only [coordinateState, values]
  congr 1
  apply propext
  exact (ha _ (select_slice heads (selectors + modes)
    (parameterWorld embedding choice (strategy input)) headWorld) j).trans
    (ComparisonJointClauses.store_select hs _ headWorld j)

end ModalityInference.ComparisonJointAxisSummary
