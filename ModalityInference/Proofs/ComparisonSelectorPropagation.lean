import ModalityInference.ComparisonSelectorPropagation
import ModalityInference.Proofs.ComparisonPropagation
import ModalityInference.Proofs.SymbolicCNF

namespace ModalityInference.ComparisonSelectorPropagation

open ComparisonPropagation

/-- Selector choices are represented by complementary positive coordinates. -/
def Slice (heads selectors : Nat) (choice parameters : Nat → Bool) : Prop :=
  ∀ i < selectors,
    parameters (heads + 2 * i) = choice i ∧
    parameters (heads + 2 * i + 1) = !choice i

def outside (heads selectors : Nat) (choice : Nat → Bool) : CNF :=
  [(List.range selectors).map fun i =>
    (heads + 2 * i + if choice i then 1 else 0, true)]

def extend (heads selectors : Nat) (choice : Nat → Bool) (store : Store count) : Store count :=
  Vector.ofFn fun i => join store[i] (outside heads selectors choice)

theorem theory_correct (heads selectors : Nat) (parameters : Nat → Bool) :
    CNFHolds parameters (theory heads selectors) ↔
      ∀ i < selectors, parameters (heads + 2 * i + 1) = !parameters (heads + 2 * i) := by
  simp only [theory, CNFHolds, List.forall_mem_flatMap, List.mem_range]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [clauseHolds_cons]
  simp only [ClauseHolds, List.not_mem_nil, false_and, exists_false, or_false]
  apply forall_congr' fun i => imp_congr_right fun hi => ?_
  cases parameters (heads + 2 * i) <;> cases parameters (heads + 2 * i + 1) <;> decide


theorem outside_correct (heads selectors : Nat) (choice parameters : Nat → Bool) :
    CNFHolds parameters (outside heads selectors choice) ↔
      ∃ i < selectors, parameters (heads + 2 * i + if choice i then 1 else 0) = true := by
  simp [outside, CNFHolds, ClauseHolds, List.mem_map]

theorem outside_false {heads selectors : Nat} {choice parameters : Nat → Bool}
    (h : Slice heads selectors choice parameters) :
    ¬CNFHolds parameters (outside heads selectors choice) := by
  rw [outside_correct]
  rintro ⟨i, hi, he⟩
  have hh := h i hi
  cases hc : choice i <;> simp_all

theorem slice_of_not_outside {heads selectors : Nat} {choice parameters : Nat → Bool}
    (ht : CNFHolds parameters (theory heads selectors))
    (ho : ¬CNFHolds parameters (outside heads selectors choice)) :
    Slice heads selectors choice parameters := by
  intro i hi
  have ht := (theory_correct heads selectors parameters).mp ht i hi
  have ho : parameters (heads + 2 * i + if choice i then 1 else 0) ≠ true :=
    fun he => ho ((outside_correct _ _ _ _).mpr ⟨i, hi, he⟩)
  cases hc : choice i <;> simp_all

theorem outside_positive (heads selectors : Nat) (choice : Nat → Bool) :
    Positive (outside heads selectors choice) := by
  intro c hc literal hl
  have hc : c = (List.range selectors).map (fun i =>
      (heads + 2 * i + if choice i then 1 else 0, true)) := by simpa [outside] using hc
  subst c
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  rfl

theorem outside_supported (heads selectors : Nat) (choice : Nat → Bool) :
    Supported (List.range (heads + 2 * selectors)) (outside heads selectors choice) := by
  intro v hv
  obtain ⟨c, hc, p, hl⟩ := CNFPropagation.mem_atoms.mp hv
  have hc : c = (List.range selectors).map (fun i =>
      (heads + 2 * i + if choice i then 1 else 0, true)) := by simpa [outside] using hc
  subst c
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hl
  have hv := congrArg Prod.fst he
  have hi := List.mem_range.mp hi
  simp only [List.mem_range]
  split at hv <;> omega

theorem extend_correct (heads selectors : Nat) (choice : Nat → Bool) (store : Store count)
    (v : Fin count) (parameters : Nat → Bool) :
    CNFHolds parameters (extend heads selectors choice store)[v] ↔
      CNFHolds parameters store[v] ∨ CNFHolds parameters (outside heads selectors choice) := by
  simp only [extend, Fin.getElem_fin, Vector.getElem_ofFn, join_correct]


theorem extend_positive {heads selectors : Nat} {choice : Nat → Bool} {store : Store count}
    (h : store.Positive) : (extend heads selectors choice store).Positive := by
  intro v
  simpa only [extend, Fin.getElem_fin, Vector.getElem_ofFn] using
    join_positive (h v) (outside_positive heads selectors choice)

theorem extend_supported {heads selectors : Nat} {choice : Nat → Bool} {store : Store count}
    (h : store.Supported heads) : (extend heads selectors choice store).Supported (heads + 2 * selectors) := by
  intro v
  simp only [extend, Fin.getElem_fin, Vector.getElem_ofFn]
  apply join_supported
  · intro i hi
    have hi := List.mem_range.mp (h v i hi)
    exact List.mem_range.mpr (by omega)
  · exact outside_supported heads selectors choice

theorem extend_one {heads selectors : Nat} {choice : Nat → Bool} {store : Store count}
    (h : ∀ v : Fin count, CNFHolds (fun _ => true) store[v]) :
    ∀ v : Fin count, CNFHolds (fun _ => true) (extend heads selectors choice store)[v] :=
  fun v => (extend_correct _ _ _ _ _ _).mpr (Or.inl (h v))

/-- Parameters are equal on the input and output of each relational edge. -/
def SliceClosed (heads selectors : Nat) (choice : Nat → Bool)
    (program : Program count) (store : Store count) : Prop :=
  (∀ parameters, Slice heads selectors choice parameters →
    ∀ v : Fin count, CNFHolds parameters program.lower[v] → CNFHolds parameters store[v]) ∧
  ∀ e ∈ program.edges, ∀ parameters,
    Slice heads selectors choice (fun i => parameters (2 * i)) →
    Slice heads selectors choice (fun i => parameters (2 * i + 1)) →
    CNFHolds parameters e.relation →
    CNFHolds (fun i => parameters (2 * i)) store[e.source] →
    CNFHolds (fun i => parameters (2 * i + 1)) store[e.target]

def SliceValid (heads selectors : Nat) (choice : Nat → Bool)
    (program : Program count) (store : Store count) : Prop :=
  SliceClosed heads selectors choice program store ∧
  ∀ parameters, Slice heads selectors choice parameters →
    CNFHolds parameters program.checks ∧
      ∀ v : Fin count, CNFHolds parameters store[v] → CNFHolds parameters program.upper[v]

theorem agreement_correct (heads selectors : Nat) (parameters : Nat → Bool) :
    CNFHolds parameters (agreement heads selectors) ↔
      ∀ i < 2 * selectors, parameters (2 * (heads + i)) = parameters (2 * (heads + i) + 1) := by
  simp only [agreement, CNFHolds, List.forall_mem_flatMap, List.mem_range]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [clauseHolds_cons]
  simp only [ClauseHolds, List.not_mem_nil, false_and, exists_false, or_false]
  apply forall_congr' fun i => imp_congr_right fun hi => ?_
  cases parameters (2 * (heads + i)) <;> cases parameters (2 * (heads + i) + 1) <;> decide

theorem guardRelation_correct (heads selectors : Nat) (relation : CNF) (parameters : Nat → Bool) :
    CNFHolds parameters (guardRelation heads selectors relation) ↔
      CNFHolds parameters relation ∧
      CNFHolds (fun i => parameters (2 * i)) (theory heads selectors) ∧
      CNFHolds (fun i => parameters (2 * i + 1)) (theory heads selectors) ∧
      ∀ i < 2 * selectors, parameters (2 * (heads + i)) = parameters (2 * (heads + i) + 1) := by
  simp only [guardRelation, cnfHolds_append, rename_correct, agreement_correct]
  tauto

theorem slice_left_of_right {heads selectors : Nat} {choice parameters : Nat → Bool}
    (h : Slice heads selectors choice (fun i => parameters (2 * i + 1)))
    (ha : ∀ i < 2 * selectors,
      parameters (2 * (heads + i)) = parameters (2 * (heads + i) + 1)) :
    Slice heads selectors choice (fun i => parameters (2 * i)) := by
  intro i hi
  obtain ⟨h₁, h₂⟩ := h i hi
  refine ⟨(ha (2 * i) (by omega)).trans h₁, ?_⟩
  have he := ha (2 * i + 1) (by omega)
  simpa only [Nat.add_assoc] using he.trans h₂

theorem prepareProgram_closed_extend {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (h : SliceClosed heads selectors choice program store) :
    (prepareProgram heads selectors program).Closed (extend heads selectors choice store) := by
  refine ⟨?_, ?_⟩
  · intro v parameters hv
    have hv : CNFHolds parameters (meet (theory heads selectors) program.lower[v]) := by
      simpa only [prepareProgram, Fin.getElem_fin, Vector.getElem_ofFn] using hv
    obtain ⟨ht, hv⟩ := (meet_correct _ _ _).mp hv
    rw [extend_correct]
    by_cases ho : CNFHolds parameters (outside heads selectors choice)
    · exact Or.inr ho
    · exact Or.inl (h.1 parameters (slice_of_not_outside ht ho) v hv)
  · intro e he parameters hr hv
    obtain ⟨e, heOriginal, rfl⟩ := List.mem_map.mp he
    obtain ⟨hr, hl, ht, ha⟩ := (guardRelation_correct _ _ _ _).mp hr
    rw [extend_correct] at hv ⊢
    by_cases ho : CNFHolds (fun i => parameters (2 * i + 1)) (outside heads selectors choice)
    · exact Or.inr ho
    · have hs := slice_of_not_outside ht ho
      have hs' := slice_left_of_right hs ha
      exact Or.inl (h.2 e heOriginal parameters hs' hs hr (hv.resolve_right (outside_false hs')))

theorem program_slice_least {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (hp : store.Positive) (hs : store.Supported heads)
    (ht : ∀ v : Fin count, CNFHolds (fun _ => true) store[v])
    (hc : SliceClosed heads selectors choice program store)
    {parameters : Nat → Bool} (hparam : Slice heads selectors choice parameters) (v : Fin count) :
    let p := prepareProgram heads selectors program
    CNFHolds parameters (propagate (heads + 2 * selectors) p.edges p.lower)[v] →
      CNFHolds parameters store[v] := by
  dsimp only
  intro hv
  have hle := propagate_least_closed (extend_positive hp) (extend_supported hs) (extend_one ht)
    (prepareProgram_closed_extend hc)
  exact ((extend_correct _ _ _ _ _ _).mp (hle v parameters hv)).resolve_right (outside_false hparam)

theorem program_residual_complete {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (hp : store.Positive) (hs : store.Supported heads)
    (ht : ∀ v : Fin count, CNFHolds (fun _ => true) store[v])
    (hc : SliceValid heads selectors choice program store)
    {parameters : Nat → Bool} (hparam : Slice heads selectors choice parameters) :
    let p := prepareProgram heads selectors program
    CNFHolds parameters (residual p (propagate (heads + 2 * selectors) p.edges p.lower)) := by
  dsimp only
  rw [residual_correct]
  refine ⟨(implies_correct _ _ _).mpr (fun _ => (hc.2 parameters hparam).1), ?_⟩
  intro v hv
  simp only [prepareProgram, Fin.getElem_fin, Vector.getElem_ofFn]
  exact (implies_correct _ _ _).mpr fun _ => (hc.2 parameters hparam).2 v
    (program_slice_least hp hs ht hc.1 hparam v hv)


theorem clause_select_correct (heads : Nat) (choice parameters : Nat → Bool) (c : Clause) :
    ClauseHolds (select heads choice parameters) c ↔
      fixedClause heads choice c = true ∨
        ClauseHolds parameters (c.filter fun literal => literal.1 < heads) := by
  constructor
  · rintro ⟨v, b, hv, he⟩
    by_cases hh : v < heads
    · exact Or.inr ⟨v, b, List.mem_filter.mpr ⟨hv, by simpa using hh⟩,
        by simpa [select, hh] using he⟩
    · apply Or.inl
      apply List.any_eq_true.mpr
      exact ⟨(v, b), hv, by simpa [select, hh, show heads ≤ v by omega] using he⟩
  · rintro (hf | ⟨v, b, hv, he⟩)
    · obtain ⟨⟨v, b⟩, hv, he⟩ := List.any_eq_true.mp hf
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
      exact ⟨v, b, hv, by simpa [select, show ¬v < heads by omega] using he.2⟩
    · obtain ⟨hv, hh⟩ := List.mem_filter.mp hv
      have hh : v < heads := by simpa using hh
      exact ⟨v, b, hv, by simpa [select, hh] using he⟩

theorem specialize_correct (heads : Nat) (choice parameters : Nat → Bool) (cs : CNF) :
    CNFHolds parameters (specialize heads choice cs) ↔
      CNFHolds (select heads choice parameters) cs := by
  simp only [specialize, CNFHolds, List.forall_mem_map, List.forall_mem_filter]
  apply forall_congr' fun c => imp_congr_right fun hc => ?_
  rw [clause_select_correct]
  cases fixedClause heads choice c <;> simp

theorem specialize_positive {heads : Nat} {choice : Nat → Bool} {cs : CNF}
    (h : Positive cs) : Positive (specialize heads choice cs) := by
  intro c hc literal hl
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
  exact h original (List.mem_filter.mp ho).1 literal (List.mem_filter.mp hl).1

theorem specialize_supported (heads : Nat) (choice : Nat → Bool) (cs : CNF) :
    Supported (List.range heads) (specialize heads choice cs) := by
  intro v hv
  obtain ⟨c, hc, b, hl⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hc
  exact List.mem_range.mpr (by simpa using (List.mem_filter.mp hl).2)


theorem select_slice (heads selectors : Nat) (choice parameters : Nat → Bool) :
    Slice heads selectors choice (select heads choice parameters) := by
  intro i hi
  constructor
  · simp [select, fixedValue, show ¬heads + 2 * i < heads by omega]
  · simp [select, fixedValue, show ¬heads + 2 * i + 1 < heads by omega,
      show heads + 2 * i + 1 - heads = 2 * i + 1 by omega,
      show (2 * i + 1) / 2 = i by omega]

theorem select_eq_of_slice {heads selectors : Nat} {choice parameters : Nat → Bool}
    (hs : Slice heads selectors choice parameters) {v : Nat} (hv : v < heads + 2 * selectors) :
    select heads choice parameters v = parameters v := by
  by_cases hh : v < heads
  · simp [select, hh]
  · have hi : (v - heads) / 2 < selectors := by omega
    obtain ⟨he, ho⟩ := hs ((v - heads) / 2) hi
    have heq : v = heads + 2 * ((v - heads) / 2) + (v - heads) % 2 := by omega
    by_cases hp : (v - heads) % 2 = 0
    · have heq : v = heads + 2 * ((v - heads) / 2) := by omega
      simpa [select, hh, fixedValue, hp, ← heq] using he.symm
    · have hp : (v - heads) % 2 = 1 := by omega
      have heq : v = heads + 2 * ((v - heads) / 2) + 1 := by omega
      simpa [select, hh, fixedValue, hp, ← heq] using ho.symm

theorem specialize_of_slice {heads selectors : Nat} {choice parameters : Nat → Bool} {cs : CNF}
    (hs : Supported (List.range (heads + 2 * selectors)) cs)
    (hp : Slice heads selectors choice parameters) :
    CNFHolds parameters (specialize heads choice cs) ↔ CNFHolds parameters cs := by
  rw [specialize_correct]
  exact CNFPropagation.holds_congr fun v hv =>
    select_eq_of_slice hp (List.mem_range.mp (hs v hv))

theorem Slice.theory {heads selectors : Nat} {choice parameters : Nat → Bool}
    (hs : Slice heads selectors choice parameters) : CNFHolds parameters (theory heads selectors) := by
  apply (theory_correct _ _ _).mpr
  intro i hi
  rw [(hs i hi).1, (hs i hi).2]

theorem slices_agreement {heads selectors : Nat} {choice parameters : Nat → Bool}
    (hl : Slice heads selectors choice (fun i => parameters (2 * i)))
    (hr : Slice heads selectors choice (fun i => parameters (2 * i + 1))) :
    ∀ i < 2 * selectors, parameters (2 * (heads + i)) = parameters (2 * (heads + i) + 1) := by
  intro i hi
  have hj : i / 2 < selectors := by omega
  by_cases hp : i % 2 = 0
  · have he : i = 2 * (i / 2) := by omega
    simpa only [← he] using (hl (i / 2) hj).1.trans (hr (i / 2) hj).1.symm
  · have he : i = 2 * (i / 2) + 1 := by omega
    have hh := (hl (i / 2) hj).2.trans (hr (i / 2) hj).2.symm
    simpa only [Nat.add_assoc, ← he] using hh


theorem prepareProgram_slice_valid {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (hc : (prepareProgram heads selectors program).Closed store)
    (hr : ∀ parameters, Slice heads selectors choice parameters →
      CNFHolds parameters (residual (prepareProgram heads selectors program) store)) :
    SliceValid heads selectors choice program store := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro parameters hs v hv
    apply hc.1 v parameters
    simpa only [prepareProgram, Fin.getElem_fin, Vector.getElem_ofFn, meet_correct] using
      And.intro hs.theory hv
  · intro e he parameters hl ht hr hv
    apply hc.2 { e with relation := guardRelation heads selectors e.relation }
      (List.mem_map.mpr ⟨e, he, rfl⟩) parameters _ hv
    exact (guardRelation_correct _ _ _ _).mpr
      ⟨hr, hl.theory, ht.theory, slices_agreement hl ht⟩
  · intro parameters hs
    obtain ⟨hcheck, hu⟩ := (residual_correct _ _ _).mp (hr parameters hs)
    refine ⟨(implies_correct _ _ _).mp hcheck hs.theory, ?_⟩
    intro v hv
    have hh := hu v hv
    have hh : CNFHolds parameters (implies (theory heads selectors) program.upper[v]) := by
      simpa only [prepareProgram, Fin.getElem_fin, Vector.getElem_ofFn] using hh
    exact (implies_correct _ _ _).mp hh hs.theory

theorem SliceValid.congr {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {a b : Store count}
    (h : SliceValid heads selectors choice program a)
    (hab : ∀ parameters, Slice heads selectors choice parameters →
      ∀ v : Fin count, CNFHolds parameters a[v] ↔ CNFHolds parameters b[v]) :
    SliceValid heads selectors choice program b := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro parameters hs v hv
    exact (hab parameters hs v).mp (h.1.1 parameters hs v hv)
  · intro e he parameters hl ht hr hv
    exact (hab _ ht e.target).mp (h.1.2 e he parameters hl ht hr
      ((hab _ hl e.source).mpr hv))
  · intro parameters hs
    exact ⟨(h.2 parameters hs).1, fun v hv => (h.2 parameters hs).2 v
      ((hab parameters hs v).mpr hv)⟩

theorem cap_correct (heads : Nat) (parameters : Nat → Bool) :
    CNFHolds parameters (cap heads) ↔ ∃ i < heads, parameters i = true := by
  simp [cap, CNFHolds, ClauseHolds, List.mem_map]

theorem polynomial_seed {heads : Nat} {store : Store count} (h : store.Polynomial heads)
    {parameters : Nat → Bool} (hs : CNFHolds parameters (seed heads)) (v : Fin count) :
    CNFHolds parameters store[v] := by
  apply (CNFPropagation.holds_congr (fun i hi =>
    ((seed_correct _ _).mp hs i (List.mem_range.mp (h.2.1 v i hi))).symm)).mp
  exact h.2.2.1 v

theorem polynomial_cap {heads : Nat} {store : Store count} (h : store.Polynomial heads)
    {parameters : Nat → Bool} {v : Fin count} (hv : CNFHolds parameters store[v]) :
    CNFHolds parameters (cap heads) := by
  apply (cap_correct _ _).mpr
  by_contra hh
  have hz : ∀ i < heads, parameters i = false := by
    intro i hi
    cases he : parameters i
    · rfl
    · exact False.elim (hh ⟨i, hi, he⟩)
  exact h.2.2.2 v ((CNFPropagation.holds_congr fun i hi => hz i
    (List.mem_range.mp (h.2.1 v i hi))).mp hv)

theorem normalize_valid {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count} (hp : store.Polynomial heads)
    (h : SliceValid heads selectors choice program store) :
    SliceValid heads selectors choice (normalize heads program) store := by
  refine ⟨⟨?_, h.1.2⟩, ?_⟩
  · intro parameters hs v hv
    have hv : CNFHolds parameters (join (seed heads) program.lower[v]) := by
      simpa only [normalize, Fin.getElem_fin, Vector.getElem_ofFn] using hv
    exact ((join_correct _ _ _).mp hv).elim (fun hh => polynomial_seed hp hh v)
      (h.1.1 parameters hs v)
  · intro parameters hs
    refine ⟨(h.2 parameters hs).1, ?_⟩
    intro v hv
    simpa only [normalize, Fin.getElem_fin, Vector.getElem_ofFn, meet_correct] using
      And.intro (polynomial_cap hp hv) ((h.2 parameters hs).2 v hv)

theorem normalize_forget {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count}
    (h : SliceValid heads selectors choice (normalize heads program) store) :
    SliceValid heads selectors choice program store := by
  refine ⟨⟨?_, h.1.2⟩, ?_⟩
  · intro parameters hs v hv
    apply h.1.1 parameters hs v
    simpa only [normalize, Fin.getElem_fin, Vector.getElem_ofFn, join_correct] using
      (Or.inr hv : CNFHolds parameters (seed heads) ∨ CNFHolds parameters program.lower[v])
  · intro parameters hs
    refine ⟨(h.2 parameters hs).1, ?_⟩
    intro v hv
    have hh := (h.2 parameters hs).2 v hv
    have hh : CNFHolds parameters (meet (cap heads) program.upper[v]) := by
      simpa only [normalize, Fin.getElem_fin, Vector.getElem_ofFn] using hh
    exact (meet_correct _ _ _).mp hh |>.2


theorem closure_positive (heads selectors : Nat) (program : Program count) :
    (closure heads selectors program).Positive := propagate_positive _ _ _

theorem closure_supported (heads selectors : Nat) (program : Program count) :
    (closure heads selectors program).Supported (heads + 2 * selectors) := propagate_supported _ _ _

theorem residualQuery_sound {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count}
    (h : ∀ parameters, Slice heads selectors choice parameters →
      CNFHolds parameters (residualQuery heads selectors program)) :
    (witness heads selectors choice program).Polynomial heads ∧
      SliceValid heads selectors choice program (witness heads selectors choice program) := by
  have hc : SliceValid heads selectors choice (normalize heads program)
      (closure heads selectors program) :=
    prepareProgram_slice_valid (propagate_closed _ _) h
  have hs := closure_supported heads selectors program
  have hp := closure_positive heads selectors program
  have hw : SliceValid heads selectors choice (normalize heads program)
      (witness heads selectors choice program) := by
    apply hc.congr
    intro parameters hparam v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      (specialize_of_slice (hs v) hparam).symm
  refine ⟨⟨?_, ?_, ?_, ?_⟩, normalize_forget hw⟩
  · intro v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_positive (heads := heads) (choice := choice) (hp v)
  · intro v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_supported heads choice (closure heads selectors program)[v]
  · intro v
    simp only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn]
    apply (specialize_correct _ _ _ _).mpr
    apply hc.1.1 _ (select_slice _ _ _ _) v
    simp only [normalize, Fin.getElem_fin, Vector.getElem_ofFn, join_correct]
    apply Or.inl
    exact (seed_correct _ _).mpr fun i hi => by simp [select, hi]
  · intro v hv
    have hv : CNFHolds (fun _ => false)
        (specialize heads choice (closure heads selectors program)[v]) := by
      simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using hv
    have hu := (hc.2 _ (select_slice heads selectors choice (fun _ => false))).2 v
      ((specialize_correct _ _ _ _).mp hv)
    have hu : CNFHolds (select heads choice (fun _ => false)) (cap heads) :=
      (meet_correct _ _ _).mp (by
        simpa only [normalize, Fin.getElem_fin, Vector.getElem_ofFn] using hu) |>.1
    obtain ⟨i, hi, he⟩ := (cap_correct _ _).mp hu
    simp [select, hi] at he

theorem residualQuery_complete {heads selectors : Nat} {choice : Nat → Bool}
    {program : Program count} {store : Store count} (hp : store.Polynomial heads)
    (h : SliceValid heads selectors choice program store) :
    ∀ parameters, Slice heads selectors choice parameters →
      CNFHolds parameters (residualQuery heads selectors program) := by
  intro parameters hparam
  exact program_residual_complete hp.1 hp.2.1 hp.2.2.1 (normalize_valid hp h) hparam

/-- Exact symbolic feasibility for one shared positive head polynomial per state
and one constant selector assignment, including arbitrary relational edges. -/
theorem residualQuery_iff (heads selectors : Nat) (choice : Nat → Bool) (program : Program count) :
    (∀ parameters, Slice heads selectors choice parameters →
      CNFHolds parameters (residualQuery heads selectors program)) ↔
      ∃ store : Store count, store.Polynomial heads ∧
        SliceValid heads selectors choice program store := by
  exact ⟨fun h => ⟨witness heads selectors choice program, residualQuery_sound h⟩,
    fun ⟨_, hp, h⟩ => residualQuery_complete hp h⟩


theorem choice_slice {heads selectors : Nat} {parameters : Nat → Bool}
    (ht : CNFHolds parameters (theory heads selectors)) :
    Slice heads selectors (selectorChoice heads parameters) parameters := by
  intro i hi
  exact ⟨rfl, (theory_correct _ _ _).mp ht i hi⟩

theorem Slice.agree {heads selectors : Nat} {choice left right : Nat → Bool}
    (hl : Slice heads selectors choice left) (hr : Slice heads selectors choice right)
    {v : Nat} (hv : keepSelectors heads selectors v = true) : left v = right v := by
  have hv : heads ≤ v ∧ v < heads + 2 * selectors := by simpa [keepSelectors] using hv
  rw [← select_eq_of_slice hl hv.2, ← select_eq_of_slice hr hv.2]
  simp [select, show ¬v < heads by omega]

theorem Slice.of_agree {heads selectors : Nat} {choice left right : Nat → Bool}
    (hr : Slice heads selectors choice right)
    (h : ∀ v, keepSelectors heads selectors v = true → left v = right v) :
    Slice heads selectors choice left := by
  intro i hi
  rw [h (heads + 2 * i) (by simp [keepSelectors]; omega),
    h (heads + 2 * i + 1) (by simp [keepSelectors]; omega)]
  exact hr i hi

theorem query_correct (heads selectors : Nat) (program : Program count) (parameters : Nat → Bool) :
    CNFHolds parameters (query heads selectors program) ↔
      CNFHolds parameters (theory heads selectors) ∧
        ∀ τ, Slice heads selectors (selectorChoice heads parameters) τ →
          CNFHolds τ (residualQuery heads selectors program) := by
  rw [query, cnfHolds_append, SymbolicCNF.abstract_correct]
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun τ hs => h τ (fun _ hv => hs.agree (choice_slice ht) hv)⟩
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun τ he => h τ ((choice_slice ht).of_agree he)⟩

theorem selectorChoice_select (heads : Nat) (choice parameters : Nat → Bool) :
    selectorChoice heads (select heads choice parameters) = choice := by
  funext i
  exact (select_slice heads (i + 1) choice parameters i (by omega)).1

theorem query_satisfiable_iff (heads selectors : Nat) (program : Program count) :
    (∃ parameters, CNFHolds parameters (query heads selectors program)) ↔
      ∃ choice, ∃ store : Store count, store.Polynomial heads ∧
        SliceValid heads selectors choice program store := by
  constructor
  · rintro ⟨parameters, h⟩
    have h := (query_correct _ _ _ _).mp h
    exact ⟨selectorChoice heads parameters, (residualQuery_iff _ _ _ _).mp h.2⟩
  · rintro ⟨choice, store, hp, hv⟩
    refine ⟨select heads choice (fun _ => false), (query_correct _ _ _ _).mpr ?_⟩
    refine ⟨(select_slice _ _ _ _).theory, ?_⟩
    rw [selectorChoice_select]
    exact residualQuery_complete hp hv

theorem run_sound {fuel heads selectors : Nat} {program : Program count} {result : Result count}
    (h : run fuel heads selectors program = .success result) :
    result.store.Polynomial heads ∧
      SliceValid heads selectors (selectorChoice heads (CNFPropagation.valuation result.assignment))
        program result.store := by
  unfold run at h
  cases hr : CNFPropagation.solve fuel (query heads selectors program) with
  | exhausted | rejected => simp [hr, bind, RunResult.bind] at h
  | success assignment =>
    simp only [hr, bind, RunResult.bind, pure, RunResult.success.injEq] at h
    cases h
    exact residualQuery_sound ((query_correct _ _ _ _).mp (CNFPropagation.solve_sound hr)).2

theorem run_complete {heads selectors : Nat} {program : Program count}
    (h : ∃ choice, ∃ store : Store count, store.Polynomial heads ∧
      SliceValid heads selectors choice program store) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel heads selectors program = .success result := by
  obtain ⟨parameters, hp⟩ := (query_satisfiable_iff heads selectors program).mpr h
  obtain ⟨n, hn⟩ := CNFPropagation.solve_complete hp
  refine ⟨n, ?_⟩
  intro fuel hf
  obtain ⟨assignment, ha⟩ := hn fuel hf
  exact ⟨⟨assignment, witness heads selectors
    (selectorChoice heads (CNFPropagation.valuation assignment)) program⟩,
    by simp [run, ha, bind, RunResult.bind, pure]⟩


theorem run_reifies {fuel selectors : Nat} {basis : List CompareTy}
    {program : Program count} {result : Result count}
    (h : run fuel basis.length selectors program = .success result) :
    ∃ images, reconstruct basis result.store = some images := by
  have hp := (run_sound h).1
  exact reconstruct_complete fun v => reify_complete (hp.1 v) (hp.2.1 v) (hp.2.2.1 v) (hp.2.2.2 v)

theorem run_stable {n heads selectors : Nat} {program : Program count} {result : RunResult (Result count)}
    (hne : result ≠ .exhausted) (h : run n heads selectors program = result) :
    ∀ fuel ≥ n, run fuel heads selectors program = result := by
  intro fuel hf
  cases hr : CNFPropagation.solve n (query heads selectors program) with
  | exhausted => exact False.elim (hne (by simpa [run, hr, bind, RunResult.bind] using h.symm))
  | rejected message =>
    have hs := CNFPropagation.solve_stable (by simp) hr fuel hf
    simpa [run, hs, hr, bind, RunResult.bind] using h
  | success assignment =>
    have hs := CNFPropagation.solve_stable (by simp) hr fuel hf
    simpa [run, hs, hr, bind, RunResult.bind] using h

theorem run_terminates (heads selectors : Nat) (program : Program count) :
    ∃ n, ∀ fuel ≥ n, run fuel heads selectors program ≠ .exhausted := by
  obtain ⟨n, hn⟩ := CNFPropagation.solve_terminates (query heads selectors program)
  refine ⟨n, ?_⟩
  intro fuel hf
  cases hr : CNFPropagation.solve fuel (query heads selectors program) with
  | exhausted => exact False.elim (hn fuel hf hr)
  | rejected | success => simp [run, hr, bind, RunResult.bind, pure]


end ModalityInference.ComparisonSelectorPropagation
