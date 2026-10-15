import ModalityInference.Proofs.ComparisonJointProgram
import ModalityInference.Proofs.ComparisonJointAxesSupport
import ModalityInference.Proofs.ComparisonBoundarySupport

/-! The concrete linear-clause compiler preserves the finite observation
namespace used by boundary propagation. -/
namespace ModalityInference.ComparisonJointProgram

open ComparisonPropagation ComparisonJointHorn ComparisonJointAxes
open ComparisonJointSummary ComparisonBoundarySupport

@[simp] theorem axisState_isSome_iff (count v : Nat) :
    (axisState count v).isSome = true ↔ EvenState (· < count) v := by
  by_cases hp : v % 2 = 0 <;> by_cases hv : v / 2 < count <;>
    simp [axisState, EvenState, hp, hv]

theorem ownClauses_axisLinear {side : Nat → Bool} {component : Bool} {count heads : Nat}
    {clauses : CNF} (h : Linear (· < count) clauses) :
    Linear (fun v => (axisState count v).isSome = true)
      (ownClauses side component count heads clauses) := by
  simpa only [axisState_isSome_iff] using ownClauses_linear h side component count heads

theorem axisParameter_guardBound {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF}
    (hselectors : clauses.length ≤ selectors)
    (hsource : Supported (List.range (count + heads + modes)) clauses) {v : Nat}
    (hv : v ∈ CNFPropagation.atoms (ownClauses side component count heads clauses))
    (hstate : axisState count v = none) :
    axisParameter count heads selectors v < heads + 2 * (selectors + modes) := by
  rcases ownClauses_atoms hv with ⟨i, hi, rfl⟩ | ⟨w, rfl, _, hw⟩
  · rw [axisParameter_selector]
    omega
  · have hw : w < count + heads + modes := List.mem_range.mp (hsource w hw)
    have hcount : ¬w < count := by
      intro hc
      simp [axisState, hc] at hstate
    by_cases hhead : w < count + heads
    · simp [axisParameter, hhead]
      omega
    · simp [axisParameter, hhead]
      omega

def ConditionSupported (size : Nat) : Obligation count → Prop
  | .lower _ condition | .edge _ _ condition | .upper _ condition | .check condition =>
      Supported (List.range size) condition

theorem compileClause_supported {size : Nat} {decode : Nat → Option (Fin count)}
    {parameters : Nat → Nat} {clause : Clause}
    (h : ∀ literal ∈ clause, decode literal.1 = none → parameters literal.1 < size) :
    ConditionSupported size (renameParameters parameters (compileClause decode clause)) := by
  have hg : Supported (CNFPropagation.atoms [guards decode clause]) [guards decode clause] :=
    fun _ hv => hv
  have hm : ∀ v ∈ CNFPropagation.atoms [guards decode clause], parameters v ∈ List.range size := by
    intro v hv
    obtain ⟨c, hc, b, hb⟩ := CNFPropagation.mem_atoms.mp hv
    have hc : c = guards decode clause := List.mem_singleton.mp hc
    subst c
    obtain ⟨hb, hd⟩ := List.mem_filter.mp hb
    exact List.mem_range.mpr (h (v, b) hb (by simpa using hd))
  have hp := rename_supported hg hm
  have hn := rename_supported (negate_supported hg) hm
  cases hfalse : stateIndex decode false clause <;>
    cases htrue : stateIndex decode true clause <;>
    simpa only [compileClause, hfalse, htrue, renameParameters, ConditionSupported] using
      (by first | exact hp | exact hn)

theorem diagonal_supported {size : Nat} {condition : CNF}
    (h : Supported (List.range size) condition) :
    Supported (List.range (2 * size)) (diagonal size condition) := by
  apply append_supported
  · exact rename_supported h (by
      intro i hi
      simp only [List.mem_range] at hi ⊢
      omega)
  · rw [supported_iff]
    intro clause hc literal hl
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    have hi := List.mem_range.mp hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    all_goals rcases hl with rfl | rfl <;> simp only [List.mem_range] <;> omega

theorem empty_supported (size count : Nat) : GuardsSupported size (Program.empty count) := by
  constructor <;> simp [Program.empty, ComparisonBoundaryPropagation.EdgesSupported,
    Supported, CNFPropagation.atoms]

theorem add_supported {size : Nat} {program : Program count} {obligation : Obligation count}
    (hp : GuardsSupported size program) (ho : ConditionSupported size obligation) :
    GuardsSupported size (program.add size obligation) := by
  cases obligation with
  | lower target condition =>
    refine ⟨?_, hp.edges, hp.upper, hp.checks⟩
    intro v
    simp only [Program.add, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · exact join_supported ho (hp.lower v)
    · exact hp.lower v
  | edge source target condition =>
    refine ⟨hp.lower, ?_, hp.upper, hp.checks⟩
    intro edge he
    rcases List.mem_cons.mp he with rfl | he
    · exact diagonal_supported ho
    · exact hp.edges edge he
  | upper source condition =>
    refine ⟨hp.lower, hp.edges, ?_, hp.checks⟩
    intro v
    simp only [Program.add, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · exact meet_supported ho (hp.upper v)
    · exact hp.upper v
  | check condition =>
    exact ⟨hp.lower, hp.edges, hp.upper, meet_supported ho hp.checks⟩

theorem fold_supported {size : Nat} {program : Program count}
    (obligations : List (Obligation count)) (hp : GuardsSupported size program)
    (ho : ∀ obligation ∈ obligations, ConditionSupported size obligation) :
    GuardsSupported size (obligations.foldl (Program.add size) program) := by
  induction obligations generalizing program with
  | nil => exact hp
  | cons obligation rest ih =>
    exact ih (add_supported hp (ho obligation List.mem_cons_self))
      (fun o hm => ho o (List.mem_cons_of_mem _ hm))

/-- Only guard atoms need a finite parameter address; state atoms are decoded
before the parameter renaming. -/
theorem compile_supported {size : Nat} {decode : Nat → Option (Fin count)}
    {parameters : Nat → Nat} {clauses : CNF}
    (h : ∀ clause ∈ clauses, ∀ literal ∈ clause,
      decode literal.1 = none → parameters literal.1 < size) :
    GuardsSupported size (compile size decode parameters clauses) := by
  unfold compile
  apply fold_supported _ (empty_supported size count)
  intro obligation ho
  obtain ⟨clause, hc, rfl⟩ := List.mem_map.mp ho
  exact compileClause_supported (h clause hc)

/-- The actual axis compiler supplies the boundary algorithm's finite-support
premise directly from source support and the reserved selector count. -/
theorem axisProgram_own_supported {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF}
    (hselectors : clauses.length ≤ selectors)
    (hsource : Supported (List.range (count + heads + modes)) clauses) :
    GuardsSupported (heads + 2 * (selectors + modes))
      (axisProgram count heads selectors modes (ownClauses side component count heads clauses)) := by
  apply compile_supported
  intro clause hc literal hl hstate
  exact axisParameter_guardBound hselectors hsource
    (CNFPropagation.mem_atoms.mpr ⟨clause, hc, literal.2, hl⟩) hstate

theorem axisProgram_valid {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF} {store : Store count}
    (hs : store.Supported (heads + 2 * (selectors + modes)))
    (hc : Linear (· < count) clauses) :
    (axisProgram count heads selectors modes (ownClauses side component count heads clauses)).Valid store ↔
      ∀ world, CNFHolds
        (ComparisonJointAxes.encode (fun i => world (heads + 2 * i))
          (ComparisonJointEncoding.valuation (values store world) (axisInputs heads selectors world)))
        (ownClauses side component count heads clauses) := by
  rw [axisProgram, compile_valid hs (ownClauses_axisLinear hc)]
  simp_rw [axis_valuation]

theorem axisProgram_sliceValid {side : Nat → Bool} {component : Bool}
    {count heads selectors modes : Nat} {clauses : CNF} {store : Store count}
    (hs : store.Supported (heads + 2 * (selectors + modes)))
    (hc : Linear (· < count) clauses) (choice : Nat → Bool) :
    ComparisonSelectorPropagation.SliceValid heads (selectors + modes) choice
      (axisProgram count heads selectors modes (ownClauses side component count heads clauses)) store ↔
      ∀ world, ComparisonSelectorPropagation.Slice heads (selectors + modes) choice world →
        CNFHolds
          (ComparisonJointAxes.encode (fun i => world (heads + 2 * i))
            (ComparisonJointEncoding.valuation (values store world) (axisInputs heads selectors world)))
          (ownClauses side component count heads clauses) := by
  rw [axisProgram, compile_sliceValid hs (ownClauses_axisLinear hc)]
  simp_rw [axis_valuation]

end ModalityInference.ComparisonJointProgram
