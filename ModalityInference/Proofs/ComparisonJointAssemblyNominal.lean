import ModalityInference.ComparisonJointAssembly
import ModalityInference.Proofs.ComparisonJointGroupStateSupport
import ModalityInference.Proofs.ComparisonJointAxisStates

namespace ModalityInference.ComparisonJointAssembly

open ComparisonPropagation ComparisonJointGroup ComparisonJointHorn ComparisonJointProgram
open ComparisonJointSummary ComparisonSelectorPropagation ComparisonJointAxes

@[simp] theorem nominalState_isSome (count v : Nat) :
    (nominalState count v).isSome = true ↔ v < count := by
  simp [nominalState]

theorem nominalProgram_linear {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {input : Input} (h : prepare fuel assumptions required g = .success input) :
    Linear (fun v => (nominalState g.leaves.length v).isSome = true) input.nominal := by
  intro c hc v w b hv hw hsv hsw
  exact (prepare_linear h).1 c hc hv hw
    (by have := (nominalState_isSome _ _).mp hsv; omega)
    (by have := (nominalState_isSome _ _).mp hsw; omega)

theorem nominalProgram_supported {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {input : Input} (h : prepare fuel assumptions required g = .success input) :
    GuardsSupported g.heads.length (nominalProgram g.leaves.length g.heads.length input) := by
  apply compile_supported
  intro clause hc literal hl hd
  have ha := prepare_nominal_atoms h (CNFPropagation.mem_atoms.mpr ⟨clause, hc, literal.2, hl⟩)
  have hn : ¬literal.1 < g.leaves.length := by
    intro hn
    simp [nominalState, hn] at hd
  rcases ha with ha | ha
  · exact False.elim (hn ha)
  · omega

theorem sliceValid_zero (heads : Nat) (choice : Nat → Bool) (program : Program count)
    (store : Store count) :
    SliceValid heads 0 choice program store ↔ program.Valid store := by
  rw [Program.valid_iff]
  simp only [SliceValid, SliceClosed, Slice, Nat.not_lt_zero, false_implies, forall_const,
    and_self, forall_and, Store.Le]
  exact ⟨fun ⟨⟨hl, he⟩, hc, hu⟩ => ⟨fun v world => hl world v, he, hc, hu⟩,
    fun ⟨hl, he, hc, hu⟩ => ⟨⟨fun world v => hl v world, he⟩, hc, hu⟩⟩

theorem selected_nominal_valid {heads : Nat} {program : Program count} {store : Store count}
    (hp : GuardsSupported heads program) (hs : store.Supported heads) (choice : Nat → Bool) :
    SelectedValid heads choice program store ↔ program.Valid store :=
  (selected_iff_slice (parameters := 0) (by simpa using hp) hs).trans
    (sliceValid_zero heads choice program store)

theorem nominalProgram_guarded_valid {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input}
    (h : prepare fuel assumptions required g = .success input)
    {store : Store g.leaves.length} (hs : store.Supported g.heads.length)
    (choice : Fin constants → Bool) (strategy : (Nat → Bool) → Nat → Bool) :
    ComparisonJointGuarded.Holds choice store strategy
      (ComparisonJointSummary.compileGuarded g.heads.length (fun i => .inr i)
        (nominalProgram g.leaves.length g.heads.length input)) ↔
      (nominalProgram g.leaves.length g.heads.length input).Valid store := by
  rw [compileGuarded_correct]
  constructor
  · intro hh
    exact (selected_nominal_valid (nominalProgram_supported h) hs _).mp (hh (fun _ => false))
  · intro hh world
    exact (selected_nominal_valid (nominalProgram_supported h) hs _).mpr hh

theorem nominalProgram_valuation {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input}
    (h : prepare fuel assumptions required g = .success input)
    (store : Store g.leaves.length) (full : State (4 * g.leaves.length))
    (strategy : (Nat → Bool) → Nat → Bool) (headWorld scalarInput : Nat → Bool)
    (hfull : ∀ i, full headWorld scalarInput (state .unaffected i) = values store headWorld i) :
    CNFHolds (ComparisonJointHorn.valuation (nominalState g.leaves.length)
      (values store headWorld) (headWorld ∘ (· - 4 * g.leaves.length))) input.nominal ↔
    CNFHolds (ComparisonJointAxes.valuation g.heads.length full strategy headWorld scalarInput) input.nominal := by
  apply CNFPropagation.holds_congr
  intro v hv
  rcases prepare_nominal_atoms h hv with hv | ⟨hl, hu⟩
  · have heq := hfull ⟨v, hv⟩
    simpa [ComparisonJointHorn.valuation, nominalState, ComparisonJointAxes.valuation, hv,
      state, coordinateNumber, show v < 4 * g.leaves.length by omega] using heq.symm
  · simp [ComparisonJointHorn.valuation, nominalState, ComparisonJointAxes.valuation, hu,
      show ¬v < g.leaves.length by omega, Nat.not_lt.mpr hl]

/-- The nominal program observes the shared head-only states; all other state
slots and every scalar input are irrelevant to its original clauses. -/
theorem nominalProgram_valid_iff {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input}
    (h : prepare fuel assumptions required g = .success input)
    {store : Store g.leaves.length} (hs : store.Supported g.heads.length)
    (full : State (4 * g.leaves.length)) (strategy : (Nat → Bool) → Nat → Bool)
    (hfull : ∀ headWorld scalarInput i,
      full headWorld scalarInput (state .unaffected i) = values store headWorld i) :
    (nominalProgram g.leaves.length g.heads.length input).Valid store ↔
      ∀ headWorld scalarInput,
        CNFHolds (ComparisonJointAxes.valuation g.heads.length full strategy headWorld scalarInput) input.nominal := by
  rw [nominalProgram, compile_valid hs (nominalProgram_linear h)]
  constructor
  · intro hh headWorld scalarInput
    exact (nominalProgram_valuation h store full strategy headWorld scalarInput
      (hfull headWorld scalarInput)).mp (hh headWorld)
  · intro hh headWorld
    exact (nominalProgram_valuation h store full strategy headWorld (fun _ => false)
      (hfull headWorld (fun _ => false))).mpr (hh headWorld (fun _ => false))

/-- The actual guarded nominal component has exactly the original group
clause semantics, with the same shared modality strategy as all other components. -/
theorem nominalProgram_guarded_iff {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input}
    (h : prepare fuel assumptions required g = .success input)
    {store : Store g.leaves.length} (hs : store.Supported g.heads.length)
    (choice : Fin constants → Bool) (full : State (4 * g.leaves.length))
    (strategy : (Nat → Bool) → Nat → Bool)
    (hfull : ∀ headWorld scalarInput i,
      full headWorld scalarInput (state .unaffected i) = values store headWorld i) :
    ComparisonJointGuarded.Holds choice store strategy
      (ComparisonJointSummary.compileGuarded g.heads.length (fun i => .inr i)
        (nominalProgram g.leaves.length g.heads.length input)) ↔
      ∀ headWorld scalarInput,
        CNFHolds (ComparisonJointAxes.valuation g.heads.length full strategy headWorld scalarInput) input.nominal :=
  (nominalProgram_guarded_valid h hs choice strategy).trans
    (nominalProgram_valid_iff h hs full strategy hfull)

end ModalityInference.ComparisonJointAssembly
