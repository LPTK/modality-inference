import ModalityInference.ComparisonJointSummary
import ModalityInference.Proofs.ComparisonJointClauses
import ModalityInference.Proofs.ComparisonJointGuarded
import ModalityInference.Proofs.ComparisonSliceCNF

namespace ModalityInference.ComparisonJointSummary

open ComparisonPropagation ComparisonJointClauses ComparisonSelectorPropagation
  ComparisonBoundaryPropagation

theorem literals_headLiterals (size : Nat) (clause : Clause) :
    literals (headLiterals size clause) = clause.filter (fun literal => literal.1 < size) := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
    rcases literal with ⟨i, polarity⟩
    by_cases hi : i < size <;> simp_all [headLiterals, literals]

theorem scalarLiteral_correct (heads : Nat) (choice : Nat → Bool) (literal : Literal) :
    choice (scalarLiteral heads literal).1 = (scalarLiteral heads literal).2 ↔
      fixedValue heads choice literal.1 = literal.2 := by
  simp only [scalarLiteral, fixedValue]
  split <;> cases literal.2 <;> cases choice ((literal.1 - heads) / 2) <;> decide

theorem clause_split (heads : Nat) (choice world : Nat → Bool) (clause : Clause) :
    ClauseHolds (select heads choice world) clause ↔
      ClauseHolds world (literals (headLiterals heads clause)) ∨
        ClauseHolds choice (modeLiterals heads clause) := by
  rw [literals_headLiterals]
  constructor
  · rintro ⟨i, polarity, hi, he⟩
    by_cases hh : i < heads
    · exact Or.inl ⟨i, polarity, List.mem_filter.mpr ⟨hi, by simpa⟩,
        by simpa only [select, if_pos hh] using he⟩
    · exact Or.inr ⟨(scalarLiteral heads (i, polarity)).1,
        (scalarLiteral heads (i, polarity)).2,
        List.mem_map.mpr ⟨(i, polarity), List.mem_filter.mpr ⟨hi, by simpa using Nat.le_of_not_gt hh⟩, rfl⟩,
        (scalarLiteral_correct heads choice (i, polarity)).mpr
          (by simpa only [select, if_neg hh] using he)⟩
  · rintro (⟨i, polarity, hi, he⟩ | ⟨i, polarity, hi, he⟩)
    · have hh : i < heads := by simpa using (List.mem_filter.mp hi).2
      exact ⟨i, polarity, (List.mem_filter.mp hi).1, by simpa only [select, if_pos hh] using he⟩
    · obtain ⟨literal, hl, eq⟩ := List.mem_map.mp hi
      have hh : ¬literal.1 < heads := by
        have h : heads ≤ literal.1 := by simpa using (List.mem_filter.mp hl).2
        omega
      have hv : choice (scalarLiteral heads literal).1 = (scalarLiteral heads literal).2 := by
        simpa only [eq] using he
      exact ⟨literal.1, literal.2, (List.mem_filter.mp hl).1,
        by simpa only [select, if_neg hh] using (scalarLiteral_correct heads choice literal).mp hv⟩

theorem selectRelation_above (heads : Nat) (choice world : Nat → Bool) {i : Nat}
    (hi : 2 * heads ≤ i) : selectRelation heads choice world i = fixedValue heads choice (i / 2) := by
  have hh : ¬i / 2 < heads := by omega
  simp only [selectRelation, pairWorld, select, if_neg hh]
  split <;> rfl

theorem edge_clause_split (heads : Nat) (choice world : Nat → Bool) (clause : Clause) :
    ClauseHolds (selectRelation heads choice world) clause ↔
      ClauseHolds world (literals (headLiterals (2 * heads) clause)) ∨
        ClauseHolds choice (edgeModeLiterals heads clause) := by
  rw [literals_headLiterals]
  constructor
  · rintro ⟨i, polarity, hi, he⟩
    by_cases hh : i < 2 * heads
    · exact Or.inl ⟨i, polarity, List.mem_filter.mpr ⟨hi, by simpa⟩,
        by rwa [selectRelation_below choice world hh] at he⟩
    · have hge : heads ≤ i / 2 := by omega
      exact Or.inr ⟨(scalarLiteral heads (i / 2, polarity)).1,
        (scalarLiteral heads (i / 2, polarity)).2,
        List.mem_map.mpr ⟨(i, polarity), List.mem_filter.mpr ⟨hi, by simpa⟩, rfl⟩,
        (scalarLiteral_correct heads choice (i / 2, polarity)).mpr
          (by rwa [selectRelation_above heads choice world (by omega)] at he)⟩
  · rintro (⟨i, polarity, hi, he⟩ | ⟨i, polarity, hi, he⟩)
    · have hh : i < 2 * heads := by simpa using (List.mem_filter.mp hi).2
      exact ⟨i, polarity, (List.mem_filter.mp hi).1,
        by rwa [selectRelation_below choice world hh]⟩
    · obtain ⟨literal, hl, eq⟩ := List.mem_map.mp hi
      have hh : heads ≤ literal.1 / 2 := by simpa using (List.mem_filter.mp hl).2
      have hv : choice (scalarLiteral heads (literal.1 / 2, literal.2)).1 =
          (scalarLiteral heads (literal.1 / 2, literal.2)).2 := by simpa only [eq] using he
      refine ⟨literal.1, literal.2, (List.mem_filter.mp hl).1, ?_⟩
      rw [selectRelation_above heads choice world (by omega)]
      exact (scalarLiteral_correct heads choice (literal.1 / 2, literal.2)).mp hv

theorem forall_clause_or (world : Nat → Bool) (clauses : CNF) (P : Prop) :
    (∀ clause ∈ clauses, ClauseHolds world clause ∨ P) ↔ CNFHolds world clauses ∨ P := by
  classical
  by_cases h : P <;> simp [CNFHolds, h]

theorem relation_selected_correct (heads parameters : Nat) (choice world : Nat → Bool)
    (clauses : CNF) :
    CNFHolds (selectRelation heads choice world) (ComparisonSliceCNF.relation heads parameters clauses) ↔
      CNFHolds (selectRelation heads choice world) clauses := by
  have he : ComparisonSliceCNF.pair = pairWorld := by
    funext a b i
    simp [ComparisonSliceCNF.pair, pairWorld]
  simp only [selectRelation, ←he]
  rw [ComparisonSliceCNF.relation_correct (select_slice heads parameters choice _),
    ComparisonSliceCNF.sync_of_slice (select_slice heads parameters choice _)
      (select_slice heads parameters choice _)]

theorem lower_correct (heads : Nat) (choice world : Nat → Bool) (store : Store count)
    (v : Fin count) (condition : CNF) :
    (∀ clause ∈ lower heads v condition,
      clause.head.Holds store world ∨ ClauseHolds choice clause.modes) ↔
      (CNFHolds (select heads choice world) condition → CNFHolds world store[v]) := by
  simp only [lower, List.forall_mem_map, HeadClause.Holds]
  have he : ∀ clause : Clause,
      (ClauseHolds world (literals (headLiterals heads clause)) ∨ CNFHolds world store[v]) ∨
          ClauseHolds choice (modeLiterals heads clause) ↔
        ClauseHolds (select heads choice world) clause ∨ CNFHolds world store[v] := by
    intro clause
    rw [clause_split]
    tauto
  simp_rw [he]
  rw [forall_clause_or, negate_correct,
    ComparisonSliceCNF.point_correct (select_slice heads _ choice world)]
  tauto

theorem edge_correct (heads : Nat) (choice world : Nat → Bool) (store : Store count)
    (transition : Edge count) :
    (∀ clause ∈ edge heads transition,
      clause.head.Holds store world ∨ ClauseHolds choice clause.modes) ↔
      (CNFHolds (selectRelation heads choice world) transition.relation →
        CNFHolds (fun i => world (2 * i)) store[transition.source] →
          CNFHolds (fun i => world (2 * i + 1)) store[transition.target]) := by
  simp only [edge, List.forall_mem_map, HeadClause.Holds]
  have he : ∀ clause : Clause,
      (CNFHolds (fun i => world (2 * i)) store[transition.source] →
        ClauseHolds world (literals (headLiterals (2 * heads) clause)) ∨
          CNFHolds (fun i => world (2 * i + 1)) store[transition.target]) ∨
          ClauseHolds choice (edgeModeLiterals heads clause) ↔
        ClauseHolds (selectRelation heads choice world) clause ∨
          (CNFHolds (fun i => world (2 * i)) store[transition.source] →
            CNFHolds (fun i => world (2 * i + 1)) store[transition.target]) := by
    intro clause
    rw [edge_clause_split]
    tauto
  simp_rw [he]
  rw [forall_clause_or, negate_correct, relation_selected_correct]
  tauto

theorem upper_correct (heads : Nat) (choice world : Nat → Bool) (store : Store count)
    (v : Fin count) (condition : CNF) :
    (∀ clause ∈ upper heads v condition,
      clause.head.Holds store world ∨ ClauseHolds choice clause.modes) ↔
      (CNFHolds world store[v] → CNFHolds (select heads choice world) condition) := by
  simp only [upper, List.forall_mem_map, HeadClause.Holds]
  have he : ∀ clause : Clause,
      (CNFHolds world store[v] → ClauseHolds world (literals (headLiterals heads clause))) ∨
          ClauseHolds choice (modeLiterals heads clause) ↔
        ClauseHolds (select heads choice world) clause ∨ ¬CNFHolds world store[v] := by
    intro clause
    rw [clause_split]
    tauto
  simp_rw [he]
  rw [forall_clause_or]
  tauto

theorem checks_correct (heads : Nat) (choice world : Nat → Bool) (store : Store count)
    (condition : CNF) :
    (∀ clause ∈ checks heads condition,
      clause.head.Holds store world ∨ ClauseHolds choice clause.modes) ↔
      CNFHolds (select heads choice world) condition := by
  simp only [checks, List.forall_mem_map, HeadClause.Holds, ← clause_split]
  rfl

/-- Program obligations after substituting one shared scalar assignment into
all source and target parameter pairs. Nominal state formulas remain head-only. -/
def SelectedValid (heads : Nat) (choice : Nat → Bool) (program : Program count)
    (store : Store count) : Prop :=
  ∀ world,
    (∀ v : Fin count, CNFHolds (select heads choice world) program.lower[v] → CNFHolds world store[v]) ∧
    (∀ transition ∈ program.edges,
      CNFHolds (selectRelation heads choice world) transition.relation →
        CNFHolds (fun i => world (2 * i)) store[transition.source] →
          CNFHolds (fun i => world (2 * i + 1)) store[transition.target]) ∧
    (∀ v : Fin count, CNFHolds world store[v] → CNFHolds (select heads choice world) program.upper[v]) ∧
      CNFHolds (select heads choice world) program.checks

/-- The actual compiler preserves every obligation for one shared nominal
store and one shared scalar strategy. No pointwise replacement is introduced. -/
theorem compile_correct (heads : Nat) (program : Program count) (store : Store count)
    (strategy : (Nat → Bool) → Nat → Bool) :
    Holds store strategy (compile heads program) ↔
      ∀ modeWorld, SelectedValid heads (strategy modeWorld) program store := by
  simp only [Holds, compile, List.forall_mem_append, List.forall_mem_flatMap,
    List.mem_finRange, forall_const]
  simp_rw [lower_correct, edge_correct, upper_correct, checks_correct]
  constructor
  · intro h modeWorld world
    have hh := h world modeWorld
    exact ⟨hh.1.1.1, hh.1.1.2, hh.1.2, hh.2⟩
  · intro h world modeWorld
    have hh := h modeWorld world
    exact ⟨⟨⟨hh.1, hh.2.1⟩, hh.2.2.1⟩, hh.2.2.2⟩

structure GuardsSupported (size : Nat) (program : Program count) : Prop where
  lower : ∀ v : Fin count, Supported (List.range size) program.lower[v]
  edges : EdgesSupported size program
  upper : ∀ v : Fin count, Supported (List.range size) program.upper[v]
  checks : Supported (List.range size) program.checks

theorem select_cnf_of_slice {heads parameters : Nat} {choice world : Nat → Bool} {cs : CNF}
    (hs : Supported (List.range (heads + 2 * parameters)) cs)
    (hw : Slice heads parameters choice world) :
    CNFHolds (select heads choice world) cs ↔ CNFHolds world cs :=
  CNFPropagation.holds_congr fun i hi => select_eq_of_slice hw (List.mem_range.mp (hs i hi))

theorem selectRelation_cnf_of_slice {heads parameters : Nat} {choice world : Nat → Bool} {cs : CNF}
    (hs : Supported (List.range (2 * (heads + 2 * parameters))) cs)
    (hl : Slice heads parameters choice (fun i => world (2 * i)))
    (hr : Slice heads parameters choice (fun i => world (2 * i + 1))) :
    CNFHolds (selectRelation heads choice world) cs ↔ CNFHolds world cs := by
  apply CNFPropagation.holds_congr
  intro i hi
  have hi := List.mem_range.mp (hs i hi)
  have hj : i / 2 < heads + 2 * parameters := by omega
  simp only [selectRelation, pairWorld]
  split
  · rename_i hp
    have hp : i % 2 = 0 := by simpa using hp
    rw [select_eq_of_slice hl hj]
    congr 1
    omega
  · rename_i hp
    have hp : i % 2 ≠ 0 := by simpa using hp
    rw [select_eq_of_slice hr hj]
    congr 1
    omega

theorem SelectedValid.slice {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (h : SelectedValid heads choice program store)
    (hp : GuardsSupported (heads + 2 * parameters) program) :
    SliceValid heads parameters choice program store := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro world hw v hv
    exact (h world).1 v ((select_cnf_of_slice (hp.lower v) hw).mpr hv)
  · intro e he world hl hr hedge hsource
    exact (h world).2.1 e he ((selectRelation_cnf_of_slice (hp.edges e he) hl hr).mpr hedge) hsource
  · intro world hw
    exact ⟨(select_cnf_of_slice hp.checks hw).mp (h world).2.2.2,
      fun v hv => (select_cnf_of_slice (hp.upper v) hw).mp ((h world).2.2.1 v hv)⟩

theorem selected_of_slice {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (h : SliceValid heads parameters choice program store) (hs : store.Supported heads) :
    SelectedValid heads choice program store := by
  intro world
  have hw := select_slice heads parameters choice world
  refine ⟨?_, ?_, ?_, (h.2 _ hw).1⟩
  · intro v hv
    exact (store_select hs choice world v).mp (h.1.1 _ hw v hv)
  · intro e he hedge hsource
    have hl : Slice heads parameters choice (fun i => selectRelation heads choice world (2 * i)) := by
      simpa only [selectRelation, pairWorld_even] using
        select_slice heads parameters choice (fun i => world (2 * i))
    have hr : Slice heads parameters choice (fun i => selectRelation heads choice world (2 * i + 1)) := by
      simpa only [selectRelation, pairWorld_odd] using
        select_slice heads parameters choice (fun i => world (2 * i + 1))
    have hc : CNFHolds (fun i => selectRelation heads choice world (2 * i)) store[e.source] := by
      simpa only [selectRelation, pairWorld_even] using
        (store_select hs choice (fun i => world (2 * i)) e.source).mpr hsource
    have ht := h.1.2 e he _ hl hr hedge hc
    simp only [selectRelation, pairWorld_odd] at ht
    exact (store_select hs choice (fun i => world (2 * i + 1)) e.target).mp ht
  · intro v hv
    exact (h.2 _ hw).2 v ((store_select hs choice world v).mpr hv)

theorem selected_iff_slice {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (hp : GuardsSupported (heads + 2 * parameters) program) (hs : store.Supported heads) :
    SelectedValid heads choice program store ↔ SliceValid heads parameters choice program store :=
  ⟨fun h => h.slice hp, fun h => selected_of_slice h hs⟩

theorem compile_slice_correct {heads parameters : Nat} {program : Program count} {store : Store count}
    (hp : GuardsSupported (heads + 2 * parameters) program) (hs : store.Supported heads)
    (strategy : (Nat → Bool) → Nat → Bool) :
    Holds store strategy (compile heads program) ↔
      ∀ modeWorld, SliceValid heads parameters (strategy modeWorld) program store :=
  (compile_correct heads program store strategy).trans
    (forall_congr' fun _ => selected_iff_slice hp hs)

/-- Boundary elimination reconstructs the same finite coordinate formulas for
every interpretation of the scalar strategy, not separate pointwise witnesses. -/
theorem strategy_summary_iff {heads parameters : Nat} (hparameters : 0 < parameters)
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained)
    (hs : EdgesSupported (heads + 2 * parameters) program)
    (strategy : (Nat → Bool) → Nat → Bool) :
    (∀ modeWorld, SliceValid heads parameters (strategy modeWorld)
      (summarize heads parameters program boundary) store) ↔
      ∃ full : Store count, full.Positive ∧ full.Supported (heads + 2 * parameters) ∧
        ∀ modeWorld, SliceValid heads parameters (strategy modeWorld) program full ∧
          BoundaryAgreement heads parameters (strategy modeWorld) boundary full store := by
  let allowed := fun choice => ∃ modeWorld, strategy modeWorld = choice
  have he := summarize_uniform_iff hparameters allowed program boundary store hs
  constructor
  · intro h
    obtain ⟨full, hp, hf, hv⟩ := he.mp (by rintro choice ⟨world, rfl⟩; exact h world)
    exact ⟨full, hp, hf, fun world => hv _ ⟨world, rfl⟩⟩
  · rintro ⟨full, hp, hf, hv⟩ world
    exact he.mpr ⟨full, hp, hf, by rintro choice ⟨w, rfl⟩; exact hv w⟩ _ ⟨world, rfl⟩

/-- The concrete summary compiler exactly preserves existence of one shared
coordinate reconstruction under the chosen scalar strategy. -/
theorem compile_summary_correct {heads parameters : Nat} (hparameters : 0 < parameters)
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained)
    (hs : EdgesSupported (heads + 2 * parameters) program)
    (hp : GuardsSupported (heads + 2 * parameters) (summarize heads parameters program boundary))
    (hstore : store.Supported heads) (strategy : (Nat → Bool) → Nat → Bool) :
    Holds store strategy (compile heads (summarize heads parameters program boundary)) ↔
      ∃ full : Store count, full.Positive ∧ full.Supported (heads + 2 * parameters) ∧
        ∀ modeWorld, SliceValid heads parameters (strategy modeWorld) program full ∧
          BoundaryAgreement heads parameters (strategy modeWorld) boundary full store :=
  (compile_slice_correct hp hstore strategy).trans
    (strategy_summary_iff hparameters program boundary store hs strategy)

def parameterWorld (decode : Nat → Sum (Fin constants) Nat) (choice : Fin constants → Bool)
    (world : Nat → Bool) (i : Nat) : Bool := (decode i).elim choice world

theorem constantsHold_cons (choice : Fin constants → Bool) (literal : Fin constants × Bool)
    (rest : List (Fin constants × Bool)) :
    ComparisonJointGuarded.ConstantsHold choice (literal :: rest) ↔
      choice literal.1 = literal.2 ∨ ComparisonJointGuarded.ConstantsHold choice rest := by
  simp [ComparisonJointGuarded.ConstantsHold]

theorem parameters_correct (decode : Nat → Sum (Fin constants) Nat) (choice : Fin constants → Bool)
    (world : Nat → Bool) (clause : Clause) :
    ClauseHolds (parameterWorld decode choice world) clause ↔
      ComparisonJointGuarded.ConstantsHold choice (constantParameters decode clause) ∨
        ClauseHolds world (modeParameters decode clause) := by
  induction clause with
  | nil => simp [ClauseHolds, constantParameters, modeParameters, ComparisonJointGuarded.ConstantsHold]
  | cons literal rest ih =>
    rcases literal with ⟨i, polarity⟩
    rw [clauseHolds_cons, ih]
    cases hi : decode i with
    | inl index =>
      have hc : constantParameters decode ((i, polarity) :: rest) =
          (index, polarity) :: constantParameters decode rest := by simp [constantParameters, hi]
      have hm : modeParameters decode ((i, polarity) :: rest) = modeParameters decode rest := by
        simp [modeParameters, hi]
      rw [hc, hm, constantsHold_cons]
      simp only [parameterWorld, hi, Sum.elim_inl]
      tauto
    | inr index =>
      have hc : constantParameters decode ((i, polarity) :: rest) = constantParameters decode rest := by
        simp [constantParameters, hi]
      have hm : modeParameters decode ((i, polarity) :: rest) =
          (index, polarity) :: modeParameters decode rest := by simp [modeParameters, hi]
      rw [hc, hm, clauseHolds_cons]
      simp only [parameterWorld, hi, Sum.elim_inr]
      tauto

theorem separateParameters_correct (decode : Nat → Sum (Fin constants) Nat)
    (choice : Fin constants → Bool) (store : Store count)
    (strategy : (Nat → Bool) → Nat → Bool) (clauses : List (JointClause heads count)) :
    ComparisonJointGuarded.Holds choice store strategy (clauses.map (separateParameters decode)) ↔
      Holds store (fun world => parameterWorld decode choice (strategy world)) clauses := by
  simp only [ComparisonJointGuarded.Holds, Holds, List.forall_mem_map, separateParameters]
  apply forall_congr' fun headWorld => forall_congr' fun modeWorld =>
    forall_congr' fun clause => imp_congr_right fun _ => ?_
  rw [parameters_correct]
  tauto

/-- The constants selected by dependency separation remain fixed while all
ordinary modality inputs vary. The actual compiled summary keeps both kinds. -/
theorem compileGuarded_correct (heads : Nat) (decode : Nat → Sum (Fin constants) Nat)
    (choice : Fin constants → Bool) (program : Program count) (store : Store count)
    (strategy : (Nat → Bool) → Nat → Bool) :
    ComparisonJointGuarded.Holds choice store strategy (compileGuarded heads decode program) ↔
      ∀ world, SelectedValid heads (parameterWorld decode choice (strategy world)) program store :=
  (separateParameters_correct decode choice store strategy (compile heads program)).trans
    (compile_correct heads program store (fun world => parameterWorld decode choice (strategy world)))

end ModalityInference.ComparisonJointSummary
