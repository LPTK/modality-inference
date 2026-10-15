import ModalityInference.Proofs.ComparisonJointClauses

/-! Exact nominal-program meaning on a shared constant-selector slice. -/
namespace ModalityInference.ComparisonJointClauses

open ComparisonPropagation ComparisonSelectorPropagation

private theorem sliceValid_iff (heads parameters : Nat) (choice : Nat → Bool)
    (program : Program count) (store : Store count) :
    SliceValid heads parameters choice program store ↔
      (∀ world, Slice heads parameters choice world → ∀ v : Fin count,
        CNFHolds world program.lower[v] → CNFHolds world store[v]) ∧
      (∀ e ∈ program.edges, ∀ world,
        Slice heads parameters choice (fun i => world (2 * i)) →
        Slice heads parameters choice (fun i => world (2 * i + 1)) →
        CNFHolds world e.relation → CNFHolds (fun i => world (2 * i)) store[e.source] →
        CNFHolds (fun i => world (2 * i + 1)) store[e.target]) ∧
      (∀ world, Slice heads parameters choice world → CNFHolds world program.checks) ∧
      ∀ world, Slice heads parameters choice world → ∀ v : Fin count,
        CNFHolds world store[v] → CNFHolds world program.upper[v] := by
  simp only [SliceValid, SliceClosed, forall_and, and_assoc]

private theorem lower_update (heads parameters : Nat) (choice : Nat → Bool)
    (condition : CNF) (lower store : Store count) (target : Fin count) :
    (∀ world, Slice heads parameters choice world → ∀ v : Fin count,
      CNFHolds world (Vector.ofFn fun w : Fin count =>
        if w == target then join condition lower[w] else lower[w])[v] →
      CNFHolds world store[v]) ↔
    (∀ world, Slice heads parameters choice world → ∀ v : Fin count,
      CNFHolds world lower[v] → CNFHolds world store[v]) ∧
    ∀ world, Slice heads parameters choice world →
      CNFHolds world condition → CNFHolds world store[target] := by
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq]
  constructor
  · intro h
    constructor
    · intro world hs v hv
      apply h world hs v
      by_cases he : v = target
      · subst v; simp [join_correct, hv]
      · simp [he, hv]
    · intro world hs hc
      apply h world hs target
      simp [join_correct, hc]
  · rintro ⟨hl, hv⟩ world hs v hw
    by_cases he : v = target
    · subst v
      simp only [↓reduceIte, join_correct] at hw
      exact hw.elim (hv world hs) (hl world hs target)
    · simp only [he, ↓reduceIte] at hw
      exact hl world hs v hw

private theorem upper_update (heads parameters : Nat) (choice : Nat → Bool)
    (condition : CNF) (upper store : Store count) (source : Fin count) :
    (∀ world, Slice heads parameters choice world → ∀ v : Fin count,
      CNFHolds world store[v] →
      CNFHolds world (Vector.ofFn fun w : Fin count =>
        if w == source then meet condition upper[w] else upper[w])[v]) ↔
    (∀ world, Slice heads parameters choice world → ∀ v : Fin count,
      CNFHolds world store[v] → CNFHolds world upper[v]) ∧
    ∀ world, Slice heads parameters choice world →
      CNFHolds world store[source] → CNFHolds world condition := by
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq]
  constructor
  · intro h
    constructor
    · intro world hs v hv
      have hh := h world hs v hv
      by_cases he : v = source
      · subst v
        simp only [↓reduceIte, meet_correct] at hh
        exact hh.2
      · simpa only [he, ↓reduceIte] using hh
    · intro world hs hv
      have hh := h world hs source hv
      exact ((meet_correct _ _ _).mp (by simpa using hh)).1
  · rintro ⟨hu, hv⟩ world hs v hw
    by_cases he : v = source
    · subst v
      simp only [↓reduceIte, meet_correct]
      exact ⟨hv world hs hw, hu world hs source hw⟩
    · simp only [he, ↓reduceIte]
      exact hu world hs v hw

private theorem singleton_holds (world : Nat → Bool) (guard : Clause) :
    CNFHolds world [guard] ↔ ClauseHolds world guard := by simp [CNFHolds]

private theorem guard_lower (A B : Prop) : (¬A → B) ↔ A ∨ B := by tauto

private theorem guard_edge (A B C : Prop) : (¬A → B → C) ↔ (B → A ∨ C) := by tauto

/-- Each compiled clause adds exactly its guarded nominal obligation. -/
theorem addHead_sliceValid (heads parameters index : Nat) (choice : Nat → Bool)
    (program : Program count) (store : Store count) (clause : HeadClause heads count) :
    SliceValid heads parameters choice (addHead heads index program clause) store ↔
      SliceValid heads parameters choice program store ∧
        clause.SliceHolds heads parameters index choice store := by
  cases clause with
  | lower target guard =>
    simp only [sliceValid_iff, addHead, Program.add, lower_update, negate_correct,
      singleton_holds, guard_lower, HeadClause.SliceHolds]
    tauto
  | edge source target guard =>
    simp only [sliceValid_iff, addHead, List.forall_mem_cons, negate_correct,
      singleton_holds, guard_edge, HeadClause.SliceHolds]
    tauto
  | upper source guard =>
    simp only [sliceValid_iff, addHead, Program.add, upper_update, singleton_holds,
      HeadClause.SliceHolds]
    tauto
  | check guard =>
    simp only [sliceValid_iff, addHead, Program.add, meet_correct, singleton_holds,
      forall_and, HeadClause.SliceHolds]
    tauto

private theorem empty_sliceValid (heads parameters : Nat) (choice : Nat → Bool)
    (store : Store count) : SliceValid heads parameters choice (Program.empty count) store := by
  simp [sliceValid_iff, Program.empty, CNFHolds, ClauseHolds]

/-- Folding preserves every nominal obligation at its original selector index. -/
theorem nominalProgram_sliceHolds (parameters : Nat) (choice : Nat → Bool)
    (clauses : List (JointClause heads count)) (store : Store count) :
    SliceValid heads parameters choice (nominalProgram clauses) store ↔
      ∀ i (hi : i < clauses.length),
        clauses[i].head.SliceHolds heads parameters i choice store := by
  have fold : ∀ entries : List (JointClause heads count × Nat), ∀ program : Program count,
      SliceValid heads parameters choice
        (entries.foldl (fun p entry => addHead heads entry.2 p entry.1.head) program) store ↔
        SliceValid heads parameters choice program store ∧
          ∀ entry ∈ entries, entry.1.head.SliceHolds heads parameters entry.2 choice store := by
    intro entries
    induction entries with
    | nil => simp
    | cons entry entries ih =>
      intro program
      simp only [List.foldl_cons, ih, addHead_sliceValid, List.forall_mem_cons]
      tauto
  rw [nominalProgram, fold]
  simp only [empty_sliceValid, true_and, List.forall_mem_zipIdx']

/-- A supported head store satisfies the compiled nominal program precisely
when each selector assigned to the nominal side proves its original head clause. -/
theorem nominalProgram_valid_iff {clauses : List (JointClause heads count)}
    {store : Store count} (hs : store.Supported heads) (choice : Nat → Bool) :
    SliceValid heads (2 * clauses.length) choice (nominalProgram clauses) store ↔
      ∀ i (hi : i < clauses.length), choice (2 * i) = true →
        ∀ world, clauses[i].head.Holds store world := by
  rw [nominalProgram_sliceHolds]
  exact forall_congr' fun i => forall_congr' fun hi =>
    HeadClause.sliceHolds_iff hs clauses[i].head (by omega)

end ModalityInference.ComparisonJointClauses
