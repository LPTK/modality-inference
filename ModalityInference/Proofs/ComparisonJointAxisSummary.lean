import ModalityInference.ComparisonJointAxisSummary
import ModalityInference.Proofs.ComparisonJointProgramSupport

namespace ModalityInference.ComparisonJointAxisSummary

open ComparisonPropagation ComparisonSelectorPropagation ComparisonBoundaryPropagation
open ComparisonJointSummary ComparisonJointAxes ComparisonJointProgram ComparisonJointHorn

@[simp] theorem parameterWorld_selector (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (modes : Nat → Bool) (i : Fin selectors) :
    parameterWorld embedding choice modes i.val = choice (embedding i) := by
  simp [parameterWorld, decode, i.isLt]

@[simp] theorem parameterWorld_mode (embedding : Fin selectors → Fin constants)
    (choice : Fin constants → Bool) (modes : Nat → Bool) (i : Nat) :
    parameterWorld embedding choice modes (selectors + i) = modes i := by
  simp [parameterWorld, decode, show ¬selectors + i < selectors by omega]

def mixed (side : Nat → Bool) (component : Bool) (input : Nat → Bool) (v : Nat) : Bool :=
  if side v = component then input v else false

theorem strategy_mixed {side : Nat → Bool} {component : Bool}
    {strategy : (Nat → Bool) → Nat → Bool} (h : ModeUniform side strategy)
    (input : Nat → Bool) (v : Nat) :
    strategy (mixed side component input) v =
      if side v = component then strategy input v else strategy (fun _ => false) v := by
  by_cases hv : side v = component
  · simp only [hv, ↓reduceIte]
    exact h _ _ v (fun w hw => by simp [mixed, hw, hv])
  · simp only [hv, ↓reduceIte]
    exact h _ _ v (fun w hw => by simp [mixed, hw, hv])

theorem projectWorld_slice {side : Nat → Bool} {component : Bool} {heads selectors modes : Nat}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} (hm : ModeUniform side strategy)
    {input world : Nat → Bool}
    (hw : Slice heads (selectors + modes) (parameterWorld embedding choice (strategy input)) world) :
    Slice heads (selectors + modes)
      (parameterWorld embedding choice (strategy (mixed side component input)))
      (projectWorld side component heads selectors (strategy (fun _ => false)) world) := by
  intro i hi
  have h := hw i hi
  by_cases hs : i < selectors
  · simp [projectWorld, keep, parameterWorld, decode, hs,
      show (heads + 2 * i + 1 - heads) / 2 = i by omega] at h ⊢
    exact h
  · simp [projectWorld, keep, fixed, parameterWorld, decode, hs,
      show (heads + 2 * i + 1 - heads) / 2 = i by omega] at h ⊢
    rw [strategy_mixed hm]
    by_cases hc : side (i - selectors) = component <;>
      simp [hc, h.1, h.2, show ¬heads + 2 * i < heads by omega,
        show ¬heads + 2 * i + 1 < heads by omega,
        show ¬(heads + 2 * i + 1 - heads) % 2 = 0 by omega]

theorem clause_project_correct (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline world : Nat → Bool) (clause : Clause) :
    ClauseHolds (projectWorld side component heads selectors baseline world) clause ↔
      (clause.any fun literal => !keep side component heads selectors literal.1 &&
        fixed heads selectors baseline literal.1 == literal.2) = true ∨
      ClauseHolds world (clause.filter fun literal => keep side component heads selectors literal.1) := by
  constructor
  · rintro ⟨v, b, hv, he⟩
    cases hk : keep side component heads selectors v with
    | true => exact .inr ⟨v, b, List.mem_filter.mpr ⟨hv, hk⟩,
        by simpa [projectWorld, hk] using he⟩
    | false =>
      apply Or.inl
      exact List.any_eq_true.mpr ⟨(v, b), hv, by simpa [projectWorld, hk] using he⟩
  · rintro (hf | ⟨v, b, hv, he⟩)
    · obtain ⟨⟨v, b⟩, hv, he⟩ := List.any_eq_true.mp hf
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at he
      exact ⟨v, b, hv, by simpa [projectWorld, he.1] using he.2⟩
    · obtain ⟨hv, hk⟩ := List.mem_filter.mp hv
      exact ⟨v, b, hv, by simpa [projectWorld, hk] using he⟩

theorem restrict_correct (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline world : Nat → Bool) (clauses : CNF) :
    CNFHolds world (restrict side component heads selectors baseline clauses) ↔
      CNFHolds (projectWorld side component heads selectors baseline world) clauses := by
  simp only [restrict, CNFHolds, List.forall_mem_map, List.forall_mem_filter]
  apply forall_congr' fun clause => imp_congr_right fun _ => ?_
  rw [clause_project_correct]
  cases clause.any (fun literal => !keep side component heads selectors literal.1 &&
    fixed heads selectors baseline literal.1 == literal.2) <;> simp

theorem restrict_positive {side : Nat → Bool} {component : Bool} {heads selectors : Nat}
    {baseline : Nat → Bool} {clauses : CNF} (h : Positive clauses) :
    Positive (restrict side component heads selectors baseline clauses) := by
  intro clause hc literal hl
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  exact h original (List.mem_filter.mp ho).1 literal (List.mem_filter.mp hl).1

theorem restrict_atoms {side : Nat → Bool} {component : Bool} {heads selectors : Nat}
    {baseline : Nat → Bool} {clauses : CNF} {v : Nat}
    (h : v ∈ CNFPropagation.atoms (restrict side component heads selectors baseline clauses)) :
    v ∈ CNFPropagation.atoms clauses ∧ keep side component heads selectors v = true := by
  obtain ⟨clause, hc, b, hl⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hl, hk⟩ := List.mem_filter.mp hl
  exact ⟨CNFPropagation.mem_atoms.mpr ⟨original, (List.mem_filter.mp ho).1, b, hl⟩, hk⟩

def OwnAxisSupported (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (store : Store count) : Prop :=
  ∀ v : Fin count, ∀ i ∈ CNFPropagation.atoms store[v], keep side component heads selectors i = true

@[simp] theorem restrictStore_get (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline : Nat → Bool) (store : Store count) (v : Fin count) :
    (restrictStore side component heads selectors baseline store)[v] =
      restrict side component heads selectors baseline store[v] := by
  simp [restrictStore]

theorem restrictStore_properties {side : Nat → Bool} {component : Bool} {heads selectors size : Nat}
    {baseline : Nat → Bool} {store : Store count} (hp : store.Positive) (hs : store.Supported size) :
    (restrictStore side component heads selectors baseline store).Positive ∧
      (restrictStore side component heads selectors baseline store).Supported size ∧
      OwnAxisSupported side component heads selectors (restrictStore side component heads selectors baseline store) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [restrictStore_get]
    exact restrict_positive (hp v)
  · intro v i hi
    rw [restrictStore_get] at hi
    exact hs v i (restrict_atoms hi).1
  · intro v i hi
    rw [restrictStore_get] at hi
    exact (restrict_atoms hi).2

theorem restrictStore_values (side : Nat → Bool) (component : Bool) (heads selectors : Nat)
    (baseline world : Nat → Bool) (store : Store count) (v : Fin count) :
    values (restrictStore side component heads selectors baseline store) world v =
      values store (projectWorld side component heads selectors baseline world) v := by
  simp [values, restrictStore, restrict_correct]

theorem guard_keep {side : Nat → Bool} {component : Bool} {count heads selectors : Nat}
    {clauses : CNF} (hselectors : clauses.length ≤ selectors) {v : Nat}
    (hv : v ∈ CNFPropagation.atoms (ownClauses side component count heads clauses))
    (hstate : axisState count v = none) :
    keep side component heads selectors (axisParameter count heads selectors v) = true := by
  rcases ownClauses_atoms hv with ⟨i, hi, rfl⟩ | ⟨w, rfl, how, _⟩
  · rw [axisParameter_selector]
    simp [keep, show i < selectors by omega]
  · have hcount : ¬w < count := by
      intro hc
      simp [axisState, hc] at hstate
    by_cases hhead : w < count + heads
    · simp [axisParameter, hhead, keep, show w - count < heads by omega]
    · have hside : side (w - (count + heads)) = component := by
        simpa [own, hhead] using how
      simp [axisParameter, hhead, keep, hside]

theorem restrictStore_valid {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} {store : Store count}
    (hselectors : clauses.length ≤ selectors) (hc : Linear (· < count) clauses)
    (hm : ModeUniform side strategy) (hp : store.Positive)
    (hs : store.Supported (heads + 2 * (selectors + modes)))
    (hv : ∀ input, SliceValid heads (selectors + modes)
      (parameterWorld embedding choice (strategy input))
      (program side component count heads selectors modes clauses) store) :
    ∀ input, SliceValid heads (selectors + modes)
      (parameterWorld embedding choice (strategy input))
      (program side component count heads selectors modes clauses)
      (restrictStore side component heads selectors (strategy (fun _ => false)) store) := by
  intro input
  have hrestricted := (restrictStore_properties (side := side) (component := component)
    (heads := heads) (selectors := selectors) (baseline := strategy (fun _ => false)) hp hs).2.1
  apply (compile_sliceValid hrestricted (ownClauses_axisLinear hc) heads (selectors + modes) _).mpr
  intro world hw
  have hprojected := projectWorld_slice (component := component) hm hw
  have hfull := (compile_sliceValid hs (ownClauses_axisLinear hc) heads (selectors + modes) _).mp
    (hv (mixed side component input)) _ hprojected
  apply (CNFPropagation.holds_congr ?_).mp hfull
  intro v hvatom
  cases hstate : axisState count v with
  | none =>
    have hk := guard_keep hselectors hvatom hstate
    simp [ComparisonJointHorn.valuation, hstate, projectWorld, hk]
  | some i =>
    simp only [ComparisonJointHorn.valuation, hstate, Option.elim_some]
    exact (restrictStore_values side component heads selectors (strategy (fun _ => false)) world store i).symm

@[simp] theorem projectWorld_head {side : Nat → Bool} {component : Bool} {heads selectors : Nat}
    {baseline world : Nat → Bool} {v : Nat} (hv : v < heads) :
    projectWorld side component heads selectors baseline world v = world v := by
  simp [projectWorld, keep, hv]

theorem restrictStore_boundary {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} {store : Store count}
    {boundary : Vector (Fin count) retained} {retainedStore : Store retained}
    (hm : ModeUniform side strategy) (hp : retainedStore.Supported heads)
    (ha : ∀ input, BoundaryAgreement heads (selectors + modes)
      (parameterWorld embedding choice (strategy input)) boundary store retainedStore) :
    ∀ input, BoundaryAgreement heads (selectors + modes)
      (parameterWorld embedding choice (strategy input)) boundary
      (restrictStore side component heads selectors (strategy (fun _ => false)) store) retainedStore := by
  intro input world hw j
  rw [restrictStore_get, restrict_correct]
  have hprojected := projectWorld_slice (component := component) hm hw
  exact (ha (mixed side component input) _ hprojected j).trans
    (CNFPropagation.holds_congr fun i hi => projectWorld_head (List.mem_range.mp (hp j i hi)))

/-- The exact reconstruction used by the executable assembly has the permitted
axis dependency and preserves the same nominal boundary for every input. -/
theorem compile_sound {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool}
    {boundary : Vector (Fin count) retained} {retainedStore : Store retained}
    (hselectors : clauses.length ≤ selectors)
    (hsource : Supported (List.range (count + heads + modes)) clauses)
    (hc : Linear (· < count) clauses) (hm : ModeUniform side strategy)
    (hretained : retainedStore.Supported heads)
    (h : ComparisonJointGuarded.Holds choice retainedStore strategy
      (compile side component count heads selectors modes embedding clauses boundary)) :
    let full := restrictStore side component heads selectors (strategy (fun _ => false))
      (reconstruct heads (selectors + modes)
        (program side component count heads selectors modes clauses) boundary retainedStore)
    full.Positive ∧ full.Supported (heads + 2 * (selectors + modes)) ∧
      OwnAxisSupported side component heads selectors full ∧
      ∀ input, SliceValid heads (selectors + modes)
        (parameterWorld embedding choice (strategy input))
        (program side component count heads selectors modes clauses) full ∧
        BoundaryAgreement heads (selectors + modes)
          (parameterWorld embedding choice (strategy input)) boundary full retainedStore := by
  have hprogram := axisProgram_own_supported (side := side) (component := component) hselectors hsource
  have hsummary := ComparisonBoundarySupport.summarize_supported hprogram boundary
  have hcompiled := (compileGuarded_correct heads (decode embedding) choice _ retainedStore strategy).mp h
  have hb : ∀ input, BoundaryValid heads (selectors + modes)
      (parameterWorld embedding choice (strategy input))
      (program side component count heads selectors modes clauses) boundary retainedStore := by
    intro input
    exact (summarize_valid_iff _ _ _ _ _ _).mp ((hcompiled input).slice hsummary)
  have hpositive := reconstruct_positive heads (selectors + modes)
    (program side component count heads selectors modes clauses) boundary retainedStore
  have hsupported := reconstruct_supported heads (selectors + modes)
    (program side component count heads selectors modes clauses) boundary retainedStore
  have hprops := restrictStore_properties (side := side) (component := component)
    (heads := heads) (selectors := selectors) (baseline := strategy (fun _ => false))
    hpositive hsupported
  refine ⟨hprops.1, hprops.2.1, hprops.2.2, ?_⟩
  intro input
  refine ⟨restrictStore_valid hselectors hc hm hpositive hsupported
    (fun input => reconstruct_valid hprogram.edges (hb input)) input, ?_⟩
  exact restrictStore_boundary hm hretained
    (fun input world hw j => reconstruct_boundary (hb input) hw j) input

/-- A summary is equivalent to one finite positive coordinate store, shared
across all inputs and using only the component's own scalar dependencies. -/
theorem compile_iff {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    {strategy : (Nat → Bool) → Nat → Bool}
    {boundary : Vector (Fin count) retained} {retainedStore : Store retained}
    (hparameters : 0 < selectors + modes) (hselectors : clauses.length ≤ selectors)
    (hsource : Supported (List.range (count + heads + modes)) clauses)
    (hc : Linear (· < count) clauses) (hm : ModeUniform side strategy)
    (hretained : retainedStore.Supported heads) :
    ComparisonJointGuarded.Holds choice retainedStore strategy
      (compile side component count heads selectors modes embedding clauses boundary) ↔
    ∃ full : Store count, full.Positive ∧ full.Supported (heads + 2 * (selectors + modes)) ∧
      OwnAxisSupported side component heads selectors full ∧
      ∀ input, SliceValid heads (selectors + modes)
        (parameterWorld embedding choice (strategy input))
        (program side component count heads selectors modes clauses) full ∧
        BoundaryAgreement heads (selectors + modes)
          (parameterWorld embedding choice (strategy input)) boundary full retainedStore := by
  constructor
  · intro h
    exact ⟨_, compile_sound hselectors hsource hc hm hretained h⟩
  · rintro ⟨full, hp, hs, _, hv⟩
    apply (compileGuarded_correct heads (decode embedding) choice _ retainedStore strategy).mpr
    intro input
    exact selected_of_slice (summarize_complete_parametric hparameters hp hs
      (hv input).1 (hv input).2) hretained

end ModalityInference.ComparisonJointAxisSummary
