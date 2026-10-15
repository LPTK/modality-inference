import ModalityInference.Proofs.ComparisonJointBatch

/-! Constructive composition of local polynomial witnesses under one shared
modality strategy. The construction concatenates finite stores and choices. -/
namespace ModalityInference.ComparisonJointBatch

open ComparisonPropagation ComparisonJointGuarded ComparisonJointClauses

def assemble {α : Type} (size : Entry → Nat) :
    (entries : List Entry) → ((i : Fin entries.length) → Fin (size entries[i]) → α) →
      Fin (total size entries) → α
  | [], _, v => Fin.elim0 v
  | entry :: entries, values, v =>
    if h : v.val < size entry then values ⟨0, by simp⟩ ⟨v.val, h⟩
    else assemble size entries (fun i => values i.succ)
      ⟨v.val - size entry, by have hv : v.val < size entry + total size entries := v.isLt; omega⟩

theorem assemble_embed {α : Type} (size : Entry → Nat) (entries : List Entry)
    (values : (i : Fin entries.length) → Fin (size entries[i]) → α)
    (i : Fin entries.length) (j : Fin (size entries[i])) :
    assemble size entries values (embed size entries i j) = values i j := by
  induction entries with
  | nil => exact Fin.elim0 i
  | cons entry entries ih =>
    cases i using Fin.cases with
    | zero => simp [assemble, embed, offset, total]
    | succ i =>
      have hh : ¬offset size (entry :: entries) i.succ.val + j.val < size entry := by
        simp only [Fin.val_succ, offset, List.take_succ_cons, total, List.map_cons, List.sum_cons]
        omega
      simp only [assemble, embed, hh, ↓reduceDIte]
      convert ih (fun i => values i.succ) i j using 1
      apply congrArg (assemble size entries (fun i => values i.succ))
      apply Fin.ext
      simp [embed, offset, total, Nat.add_assoc]

theorem assemble_property {α : Type} (size : Entry → Nat) (entries : List Entry)
    (values : (i : Fin entries.length) → Fin (size entries[i]) → α) {P : α → Prop}
    (h : ∀ i j, P (values i j)) (v : Fin (total size entries)) :
    P (assemble size entries values v) := by
  induction entries with
  | nil => exact Fin.elim0 v
  | cons entry entries ih =>
    simp only [assemble]
    split
    · exact h _ _
    · exact ih (fun i => values i.succ) (fun i => h i.succ) _

def forward (size : Entry → Nat) (entries : List Entry) (i : Fin entries.length) (v : Nat) : Nat :=
  offset size entries i.val + v

def assembleStore (entries : List Entry)
    (stores : (i : Fin entries.length) → Store entries[i].count) : Store (total Entry.count entries) :=
  Vector.ofFn (assemble Entry.count entries
    (fun i j => rename (forward Entry.heads entries i) (stores i)[j]))

def assembleChoice (entries : List Entry)
    (choices : (i : Fin entries.length) → Fin (constants entries[i]) → Bool) :
    Fin (total constants entries) → Bool := assemble constants entries choices

@[simp] theorem assembleStore_get (entries : List Entry)
    (stores : (i : Fin entries.length) → Store entries[i].count)
    (i : Fin entries.length) (j : Fin entries[i].count) :
    (assembleStore entries stores)[embed Entry.count entries i j] =
      rename (forward Entry.heads entries i) (stores i)[j] := by
  change (Vector.ofFn _)[embed Entry.count entries i j] = _
  rw [Fin.getElem_fin, Vector.getElem_ofFn]
  exact assemble_embed Entry.count entries _ i j

@[simp] theorem assembleChoice_get (entries : List Entry)
    (choices : (i : Fin entries.length) → Fin (constants entries[i]) → Bool)
    (i : Fin entries.length) (j : Fin (constants entries[i])) :
    assembleChoice entries choices (embed constants entries i j) = choices i j :=
  assemble_embed constants entries choices i j

theorem assembleStore_polynomial {entries : List Entry}
    {stores : (i : Fin entries.length) → Store entries[i].count}
    (h : ∀ i, (stores i).Polynomial entries[i].heads) :
    (assembleStore entries stores).Polynomial (total Entry.heads entries) := by
  have hp : ∀ v : Fin (total Entry.count entries), let clauses := (assembleStore entries stores)[v]
      Positive clauses ∧ Supported (List.range (total Entry.heads entries)) clauses ∧
        CNFHolds (fun _ => true) clauses ∧ ¬CNFHolds (fun _ => false) clauses := by
    intro v
    change (fun clauses => Positive clauses ∧ Supported (List.range (total Entry.heads entries)) clauses ∧
      CNFHolds (fun _ => true) clauses ∧ ¬CNFHolds (fun _ => false) clauses)
      ((Vector.ofFn (assemble Entry.count entries _))[v])
    rw [Fin.getElem_fin, Vector.getElem_ofFn]
    apply assemble_property Entry.count entries _
      (P := fun clauses => Positive clauses ∧ Supported (List.range (total Entry.heads entries)) clauses ∧
        CNFHolds (fun _ => true) clauses ∧ ¬CNFHolds (fun _ => false) clauses) (v := v)
    intro i j
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro clause hc literal hl
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
      obtain ⟨value, hv, rfl⟩ := List.mem_map.mp hl
      exact (h i).1 j original ho value hv
    · exact ComparisonBoundarySupport.rename_supported ((h i).2.1 j) fun w hw =>
        List.mem_range.mpr (lt_of_lt_of_le (Nat.add_lt_add_left (List.mem_range.mp hw) _)
          (offset_bound Entry.heads entries i.val i.isLt))
    · exact (rename_correct _ _ _).mpr ((h i).2.2.1 j)
    · intro hf
      exact (h i).2.2.2 j ((rename_correct _ _ _).mp hf)
  exact ⟨fun v => (hp v).1, fun v => (hp v).2.1, fun v => (hp v).2.2.1,
    fun v => (hp v).2.2.2⟩

theorem literals_forward {heads totalHeads : Nat} {f : Nat → Nat}
    {embedding : Fin heads → Fin totalHeads}
    (hf : ∀ i, f i.val = (embedding i).val) (guard : List (HeadLiteral heads))
    (valuation : Nat → Bool) :
    ClauseHolds valuation (literals (guard.map fun l => (embedding l.1, l.2))) ↔
      ClauseHolds (valuation ∘ f) (literals guard) := by
  rw [ComparisonJointReindex.literals_map]
  simp [ClauseHolds, literals, List.mem_map, Prod.exists, hf]

theorem paired_literals_forward {heads totalHeads : Nat} {f : Nat → Nat}
    {embedding : Fin heads → Fin totalHeads}
    (hf : ∀ i, f i.val = (embedding i).val) (guard : List (HeadLiteral (2 * heads)))
    (valuation : Nat → Bool) :
    ClauseHolds valuation (literals (guard.map fun l => (ComparisonJointReindex.paired embedding l.1, l.2))) ↔
      ClauseHolds (fun i => valuation (2 * f (i / 2) + i % 2)) (literals guard) := by
  have hpair (i : Fin (2 * heads)) :
      (ComparisonJointReindex.paired embedding i).val = 2 * f (i.val / 2) + i.val % 2 := by
    rw [hf ⟨i.val / 2, by omega⟩]
    rfl
  rw [ComparisonJointReindex.literals_map]
  simp [ClauseHolds, literals, List.mem_map, Prod.exists, hpair]

theorem headClause_forward {heads totalHeads count totalCount : Nat}
    {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (hf : ∀ i, f i.val = (embedding i).val)
    (states : Fin count → Fin totalCount) (part : Store count) (full : Store totalCount)
    (hs : ∀ i, full[states i] = rename f part[i])
    (c : HeadClause heads count) (valuation : Nat → Bool) :
    (ComparisonJointReindex.headClause embedding states c).Holds full valuation ↔
      c.Holds part (ComparisonJointReindex.world f valuation c) := by
  cases c <;> simp only [ComparisonJointReindex.headClause, HeadClause.Holds,
    ComparisonJointReindex.world, hs, rename_correct, literals_forward hf,
    paired_literals_forward hf, Function.comp_def]
  simp

theorem holds_forward {heads totalHeads count totalCount constants totalConstants : Nat}
    {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (hf : ∀ i, f i.val = (embedding i).val)
    (states : Fin count → Fin totalCount) (constantsMap : Fin constants → Fin totalConstants)
    (part : Store count) (full : Store totalCount)
    (hs : ∀ i, full[states i] = rename f part[i])
    (choice : Fin constants → Bool) (allChoices : Fin totalConstants → Bool)
    (hc : ∀ i, allChoices (constantsMap i) = choice i)
    (strategy : (Nat → Bool) → Nat → Bool) (clauses : List (GuardedClause heads count constants))
    (h : Holds choice part strategy clauses) :
    Holds allChoices full strategy (ComparisonJointReindex.clauses embedding states constantsMap clauses) := by
  intro headWorld modeWorld clause hclause
  obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hclause
  rcases h (ComparisonJointReindex.world f headWorld c.head) modeWorld c hmem with hk | hh | hm
  · apply Or.inl
    apply (ComparisonJointReindex.constants_map constantsMap c.constants allChoices).mpr
    simpa only [Function.comp_def, hc] using hk
  · exact Or.inr (Or.inl ((headClause_forward hf states part full hs c.head headWorld).mpr hh))
  · exact Or.inr (Or.inr hm)

theorem compile_holds {side : Nat → Bool} {entries : List Entry} {minimumModes : Nat}
    {scalar : CNF} (choices : (i : Fin entries.length) → Fin (constants entries[i]) → Bool)
    (stores : (i : Fin entries.length) → Store entries[i].count)
    (strategy : (Nat → Bool) → Nat → Bool)
    (hc : ∀ i, Holds (choices i) (stores i) strategy
      (ComparisonJointAssembly.compile side entries[i].count entries[i].heads entries[i].input minimumModes))
    (hs : ∀ world, CNFHolds (strategy world) scalar) :
    Holds (assembleChoice entries choices) (assembleStore entries stores) strategy
      (compile side entries minimumModes scalar) := by
  intro headWorld modeWorld clause hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · obtain ⟨i, _, hmem⟩ := List.mem_flatMap.mp hmem
    exact holds_forward (f := forward Entry.heads entries i)
      (embedding := embed Entry.heads entries i) (fun _ => rfl)
      (embed Entry.count entries i) (embed constants entries i)
      (stores i) (assembleStore entries stores) (assembleStore_get entries stores i)
      (choices i) (assembleChoice entries choices) (assembleChoice_get entries choices i)
      strategy _ (hc i) headWorld modeWorld clause hmem
  · exact ((ComparisonJointAssembly.scalarClauses_correct _ _ _ _).mpr hs)
      headWorld modeWorld clause hmem

/-- Independent nominal groups compose whenever their scalar action is shared. -/
theorem run_complete_local {side : Nat → Bool} {flex : List Nat} {entries : List Entry}
    {minimumModes : Nat} {scalar : CNF}
    (choices : (i : Fin entries.length) → Fin (constants entries[i]) → Bool)
    (stores : (i : Fin entries.length) → Store entries[i].count)
    (strategy : (Nat → Bool) → Nat → Bool)
    (hp : ∀ i, (stores i).Polynomial entries[i].heads)
    (hu : ModalSynthesis.Uniform side flex strategy)
    (hc : ∀ i, Holds (choices i) (stores i) strategy
      (ComparisonJointAssembly.compile side entries[i].count entries[i].heads entries[i].input minimumModes))
    (hs : ∀ world, CNFHolds (strategy world) scalar) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel side flex entries minimumModes scalar = .success result :=
  run_complete ⟨assembleChoice entries choices, assembleStore entries stores,
    assembleStore_polynomial hp, strategy, hu, compile_holds choices stores strategy hc hs⟩

theorem run_complete_families {side : Nat → Bool} {flex : List Nat} {entries : List Entry}
    {minimumModes : Nat} {scalar : CNF}
    (strategy : (Nat → Bool) → Nat → Bool)
    (hu : ModalSynthesis.Uniform side flex strategy)
    (hc : ∀ i : Fin entries.length, ∃ choice store,
      store.Polynomial entries[i].heads ∧ Holds choice store strategy
        (ComparisonJointAssembly.compile side entries[i].count entries[i].heads entries[i].input minimumModes))
    (hs : ∀ world, CNFHolds (strategy world) scalar) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel side flex entries minimumModes scalar = .success result := by
  classical
  choose choices stores hlocal using hc
  exact run_complete_local choices stores strategy (fun i => (hlocal i).1) hu
    (fun i => (hlocal i).2) hs

end ModalityInference.ComparisonJointBatch
