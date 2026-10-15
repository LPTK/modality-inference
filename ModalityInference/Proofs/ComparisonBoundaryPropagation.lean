import ModalityInference.ComparisonBoundaryPropagation
import ModalityInference.Proofs.ComparisonParametricPropagation

namespace ModalityInference.ComparisonBoundaryPropagation

open ComparisonPropagation ComparisonSelectorPropagation

theorem decodeLiteral_correct (heads parameters : Nat) (world : Nat → Bool) (literal : Literal) :
    world (decodeLiteral heads parameters literal).1 = (decodeLiteral heads parameters literal).2 ↔
      pathWorld heads parameters world literal.1 = literal.2 := by
  dsimp only [decodeLiteral, pathWorld]
  split
  · rfl
  · split
    · rfl
    · cases literal.2 <;> cases world (2 * ((literal.1 - (heads + 2 * parameters)) / 2)) <;> simp

theorem decodeRelation_correct (heads parameters : Nat) (world : Nat → Bool) (clauses : CNF) :
    CNFHolds world (decodeRelation heads parameters clauses) ↔
      CNFHolds (pathWorld heads parameters world) clauses := by
  simp only [decodeRelation, CNFHolds, List.forall_mem_map]
  apply forall_congr' fun c => imp_congr_right fun hc => ?_
  constructor
  · rintro ⟨v, b, hv, he⟩
    obtain ⟨literal, hl, heq⟩ := List.mem_map.mp hv
    have he' : world (decodeLiteral heads parameters literal).1 =
        (decodeLiteral heads parameters literal).2 := by simpa only [heq] using he
    exact ⟨literal.1, literal.2, hl, (decodeLiteral_correct _ _ _ _).mp he'⟩
  · rintro ⟨v, b, hv, he⟩
    exact ⟨(decodeLiteral heads parameters (v, b)).1, (decodeLiteral heads parameters (v, b)).2,
      List.mem_map.mpr ⟨(v, b), hv, rfl⟩, (decodeLiteral_correct _ _ _ _).mpr he⟩

theorem sourceEquality_correct (heads parameters : Nat) (world : Nat → Bool) :
    CNFHolds world (sourceEquality heads parameters) ↔
      ∀ i < heads, world i = world (heads + 2 * parameters + 2 * i) := by
  simp only [sourceEquality, CNFHolds, List.forall_mem_flatMap, List.mem_range]
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [clauseHolds_cons]
  simp only [ClauseHolds, List.not_mem_nil, false_and, exists_false, or_false]
  apply forall_congr' fun i => imp_congr_right fun _ => ?_
  cases world i <;> cases world (heads + 2 * parameters + 2 * i) <;> decide

theorem pathWorld_old {heads parameters : Nat} (world : Nat → Bool) {i : Nat}
    (hi : i < heads + 2 * parameters) :
    pathWorld heads parameters world i = world (2 * i + 1) := by
  simp only [pathWorld, hi, ↓reduceIte]

theorem pathWorld_source (heads parameters : Nat) (world : Nat → Bool) (i : Nat) :
    pathWorld heads parameters world (heads + 2 * parameters + 2 * i) = world (2 * i) := by
  simp [pathWorld]

theorem pathWorld_source_neg (heads parameters : Nat) (world : Nat → Bool) (i : Nat) :
    pathWorld heads parameters world (heads + 2 * parameters + 2 * i + 1) = !world (2 * i) := by
  have hn : ¬ heads + 2 * parameters + 2 * i + 1 < heads + 2 * parameters := by omega
  have he : heads + 2 * parameters + 2 * i + 1 - (heads + 2 * parameters) = 2 * i + 1 := by omega
  simp only [pathWorld, if_neg hn, he]
  simp

theorem pathWorld_slice {heads parameters : Nat} {world choice : Nat → Bool}
    (h : Slice heads parameters choice (fun i => world (2 * i + 1))) :
    Slice heads (parameters + heads) (pathChoice parameters choice (fun i => world (2 * i)))
      (pathWorld heads parameters world) := by
  intro i hi
  by_cases hp : i < parameters
  · rw [pathChoice, if_pos hp]
    rw [pathWorld_old world (by omega), pathWorld_old world (by omega)]
    exact h i hp
  · have he : i = parameters + (i - parameters) := by omega
    have hpos : heads + 2 * i = heads + 2 * parameters + 2 * (i - parameters) := by omega
    rw [pathChoice, if_neg hp, hpos]
    exact ⟨pathWorld_source _ _ _ _, pathWorld_source_neg _ _ _ _⟩

theorem Slice.path_prefix {heads parameters : Nat} {world choice source : Nat → Bool}
    (h : Slice heads (parameters + heads) (pathChoice parameters choice source) world) :
    Slice heads parameters choice world := by
  intro i hi
  simpa only [pathChoice, hi, ↓reduceIte] using h i (by omega)

theorem closure_sliceClosed (heads parameters : Nat) (choice : Nat → Bool) (program : Program count) :
    SliceClosed heads parameters choice program
      (ComparisonParametricPropagation.closure heads parameters program) := by
  have hc := propagate_closed (heads + 2 * parameters) (prepareProgram heads parameters program)
  refine ⟨?_, ?_⟩
  · intro world hs v hv
    apply hc.1 v world
    simpa only [prepareProgram, Fin.getElem_fin, Vector.getElem_ofFn, meet_correct] using
      And.intro hs.theory hv
  · intro e he world hl ht hr hv
    apply hc.2 { e with relation := guardRelation heads parameters e.relation }
      (List.mem_map.mpr ⟨e, he, rfl⟩) world _ hv
    exact (guardRelation_correct _ _ _ _).mpr
      ⟨hr, hl.theory, ht.theory, slices_agreement hl ht⟩

theorem sourceProgram_closed {heads parameters : Nat} {choice sourceValues : Nat → Bool}
    {program : Program count} {store : Store count} {source : Fin count}
    (hs : store.Supported heads) (hc : SliceClosed heads parameters choice program store)
    (hsource : CNFHolds sourceValues store[source]) :
    SliceClosed heads (parameters + heads) (pathChoice parameters choice sourceValues)
      (sourceProgram heads parameters program source) store := by
  refine ⟨?_, ?_⟩
  · intro world hslice v hv
    by_cases he : v = source
    · subst v
      simp only [sourceProgram, Fin.getElem_fin, Vector.getElem_ofFn, BEq.rfl, ↓reduceIte] at hv
      have heq := (sourceEquality_correct _ _ _).mp hv
      apply (CNFPropagation.holds_congr (σ := sourceValues) (τ := world) ?_).mp hsource
      intro i hi
      have hih := List.mem_range.mp (hs source i hi)
      have hp := (hslice (parameters + i) (by omega)).1
      have hid : heads + 2 * (parameters + i) = heads + 2 * parameters + 2 * i := by omega
      simp only [pathChoice, show ¬ parameters + i < parameters by omega, ↓reduceIte,
        Nat.add_sub_cancel_left, hid] at hp
      exact (heq i hih).trans hp |>.symm
    · simp only [sourceProgram, Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq, he,
        ↓reduceIte] at hv
      rcases hv [] (by simp) with ⟨i, b, hi, _⟩
      simp at hi
  · intro e he world hl ht hr hv
    exact hc.2 e he world (Slice.path_prefix hl) (Slice.path_prefix ht) hr hv

theorem pathRelation_least {heads parameters : Nat} {choice world : Nat → Bool}
    {program : Program count} {store : Store count} {source target : Fin count}
    (hparameters : 0 < parameters) (hp : store.Positive) (hs : store.Supported heads)
    (hc : SliceClosed heads parameters choice program store)
    (ht : Slice heads parameters choice (fun i => world (2 * i + 1)))
    (hsource : CNFHolds (fun i => world (2 * i)) store[source])
    (hpath : CNFHolds world (pathRelation heads parameters program source target)) :
    CNFHolds (fun i => world (2 * i + 1)) store[target] := by
  have hpath := (decodeRelation_correct _ _ _ _).mp hpath
  have hm := ComparisonParametricPropagation.slice_least (by omega) hp hs
    (sourceProgram_closed hs hc hsource) (pathWorld_slice ht) target hpath
  apply (CNFPropagation.holds_congr ?_).mp hm
  intro i hi
  exact pathWorld_old _ (by have := List.mem_range.mp (hs target i hi); omega)

theorem pathRelation_refl {heads parameters : Nat} {choice world : Nat → Bool}
    {program : Program count} (source : Fin count)
    (ht : Slice heads parameters choice (fun i => world (2 * i + 1)))
    (he : ∀ i < heads, world (2 * i) = world (2 * i + 1)) :
    CNFHolds world (pathRelation heads parameters program source source) := by
  apply (decodeRelation_correct _ _ _ _).mpr
  apply (closure_sliceClosed heads (parameters + heads)
    (pathChoice parameters choice (fun i => world (2 * i)))
    (sourceProgram heads parameters program source)).1 _ (pathWorld_slice ht) source
  simp only [sourceProgram, Fin.getElem_fin, Vector.getElem_ofFn, BEq.rfl, ↓reduceIte]
  apply (sourceEquality_correct _ _ _).mpr
  intro i hi
  rw [pathWorld_old _ (by omega), pathWorld_source]
  exact (he i hi).symm

@[simp] theorem pairWorld_even (left right : Nat → Bool) (v : Nat) :
    pairWorld left right (2 * v) = left v := by simp [pairWorld]

@[simp] theorem pairWorld_odd (left right : Nat → Bool) (v : Nat) :
    pairWorld left right (2 * v + 1) = right v := by simp [pairWorld]

theorem pathWorld_pair_slice {heads parameters : Nat} {choice source target : Nat → Bool}
    (h : Slice heads parameters choice target) :
    Slice heads (parameters + heads) (pathChoice parameters choice source)
      (pathWorld heads parameters (pairWorld source target)) := by
  have h' : Slice heads parameters choice (fun i => pairWorld source target (2 * i + 1)) := by
    simpa only [pairWorld_odd] using h
  simpa only [pairWorld_even] using pathWorld_slice h'


def EdgesSupported (size : Nat) (program : Program count) : Prop :=
  ∀ e ∈ program.edges, Supported (List.range (2 * size)) e.relation

theorem pathRelation_step {heads parameters : Nat} {choice source left right : Nat → Bool}
    {program : Program count} {start : Fin count} {edge : Edge count}
    (hs : EdgesSupported (heads + 2 * parameters) program) (he : edge ∈ program.edges)
    (hl : Slice heads parameters choice left) (hr : Slice heads parameters choice right)
    (hedge : CNFHolds (pairWorld left right) edge.relation)
    (hpath : CNFHolds (pairWorld source left)
      (pathRelation heads parameters program start edge.source)) :
    CNFHolds (pairWorld source right) (pathRelation heads parameters program start edge.target) := by
  apply (decodeRelation_correct _ _ _ _).mpr
  have hc := (closure_sliceClosed heads (parameters + heads)
    (pathChoice parameters choice source) (sourceProgram heads parameters program start)).2 edge he
    (pairWorld (pathWorld heads parameters (pairWorld source left))
      (pathWorld heads parameters (pairWorld source right)))
  simp only [pairWorld_even, pairWorld_odd] at hc
  apply hc (pathWorld_pair_slice hl) (pathWorld_pair_slice hr)
  · apply (CNFPropagation.holds_congr ?_).mp hedge
    intro i hi
    have hi := List.mem_range.mp (hs edge he i hi)
    by_cases hp : i % 2 = 0
    · have heq : i = 2 * (i / 2) := by omega
      rw [heq, pairWorld_even, pairWorld_even, pathWorld_old _ (by omega), pairWorld_odd]
    · have heq : i = 2 * (i / 2) + 1 := by omega
      rw [heq, pairWorld_odd, pairWorld_odd, pathWorld_old _ (by omega), pairWorld_odd]
  · simpa only [pairWorld_even] using (decodeRelation_correct _ _ _ _).mp hpath

theorem pairWorld_split (world : Nat → Bool) :
    pairWorld (fun i => world (2 * i)) (fun i => world (2 * i + 1)) = world := by
  funext i
  unfold pairWorld
  split
  · simp only [beq_iff_eq] at *
    exact congrArg world (by omega)
  · simp only [beq_iff_eq] at *
    exact congrArg world (by omega)

theorem pathRelation_mono {heads parameters : Nat} {source left right : Nat → Bool}
    {program : Program count} {start target : Fin count}
    (hle : ∀ i < heads + 2 * parameters, left i = true → right i = true)
    (h : CNFHolds (pairWorld source left) (pathRelation heads parameters program start target)) :
    CNFHolds (pairWorld source right) (pathRelation heads parameters program start target) := by
  apply (decodeRelation_correct _ _ _ _).mpr
  apply (ComparisonParametricPropagation.closure_positive heads (parameters + heads)
    (sourceProgram heads parameters program start) target).monotone ?_
    ((decodeRelation_correct _ _ _ _).mp h)
  intro i hi
  dsimp only [pathWorld] at hi ⊢
  by_cases hlt : i < heads + 2 * parameters
  · simp only [if_pos hlt, pairWorld_odd] at hi ⊢
    exact hle i hlt hi
  · simpa only [if_neg hlt, pairWorld_even] using hi

theorem slice_of_theory_le {heads parameters : Nat} {choice lower upper : Nat → Bool}
    (hu : Slice heads parameters choice upper)
    (hl : CNFHolds lower (theory heads parameters))
    (hle : ∀ i < heads + 2 * parameters, lower i = true → upper i = true) :
    Slice heads parameters choice lower := by
  intro i hi
  have hpair := (theory_correct _ _ _).mp hl i hi
  have hpos := hle (heads + 2 * i) (by omega)
  have hneg := hle (heads + 2 * i + 1) (by omega)
  obtain ⟨hu₁, hu₂⟩ := hu i hi
  rw [hu₁] at hpos
  rw [hu₂] at hneg
  cases hc : choice i <;> cases hp : lower (heads + 2 * i) <;>
    cases hn : lower (heads + 2 * i + 1) <;> simp_all

theorem pathImage_correct {heads parameters : Nat} {choice target : Nat → Bool}
    {program : Program count} {start finish : Fin count} (demand : CNF)
    (ht : Slice heads parameters choice target) :
    CNFHolds target (image (heads + 2 * parameters)
      (guardRelation heads parameters (pathRelation heads parameters program start finish)) demand) ↔
      ∃ source, Slice heads parameters choice source ∧ CNFHolds source demand ∧
        CNFHolds (pairWorld source target) (pathRelation heads parameters program start finish) := by
  rw [image_correct]
  constructor
  · rintro ⟨world, hr, hd, hle⟩
    obtain ⟨hr, hsource, htarget, hagree⟩ := (guardRelation_correct _ _ _ _).mp hr
    have hs := slice_of_theory_le ht htarget hle
    refine ⟨(fun i => world (2 * i)), slice_left_of_right hs hagree, hd, ?_⟩
    apply pathRelation_mono hle
    simpa only [pairWorld_split] using hr
  · rintro ⟨source, hs, hd, hp⟩
    refine ⟨pairWorld source target, ?_, ?_, ?_⟩
    · apply (guardRelation_correct _ _ _ _).mpr
      refine ⟨hp, ?_, ?_, ?_⟩
      · simpa only [pairWorld_even] using hs.theory
      · simpa only [pairWorld_odd] using ht.theory
      · apply slices_agreement
        · simpa only [pairWorld_even] using hs
        · simpa only [pairWorld_odd] using ht
    · simpa only [pairWorld_even] using hd
    · intro i hi h
      simpa only [pairWorld_odd] using h

theorem allTargets_correct (clauses : CNF) (source : Nat → Bool) :
    CNFHolds source (allTargets clauses) ↔ ∀ target, CNFHolds (pairWorld source target) clauses := by
  rw [allTargets, rename_correct, SymbolicCNF.abstract_correct]
  constructor
  · intro h target
    apply h (pairWorld source target)
    intro v hv
    have hv : v % 2 = 0 := by simpa using hv
    simp only [pairWorld, hv, BEq.rfl, ↓reduceIte, Function.comp_apply]
  · intro h world hw
    have he : (fun i => world (2 * i)) = source := by
      funext i
      simpa using hw (2 * i) (by simp)
    simpa only [← he, pairWorld_split] using h (fun i => world (2 * i + 1))

theorem allClauses_correct (clauses : List CNF) (world : Nat → Bool) :
    CNFHolds world (allClauses clauses) ↔ ∀ c ∈ clauses, CNFHolds world c := by
  induction clauses with
  | nil => simp [allClauses, CNFHolds]
  | cons c cs ih =>
    change CNFHolds world (meet c (allClauses cs)) ↔ _
    rw [meet_correct, ih]
    simp only [List.forall_mem_cons]

theorem anyClauses_correct (clauses : List CNF) (world : Nat → Bool) :
    CNFHolds world (anyClauses clauses) ↔ ∃ c ∈ clauses, CNFHolds world c := by
  induction clauses with
  | nil => simp [anyClauses, CNFHolds, ClauseHolds]
  | cons c cs ih =>
    change CNFHolds world (join c (anyClauses cs)) ↔ _
    rw [join_correct, ih]
    simp only [List.exists_mem_cons_iff]

theorem reconstruct_correct {heads parameters : Nat} {choice world : Nat → Bool}
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained)
    (hw : Slice heads parameters choice world) (v : Fin count) :
    CNFHolds world (reconstruct heads parameters program boundary store)[v] ↔
      CNFHolds world (ComparisonParametricPropagation.closure heads parameters program)[v] ∨
        ∃ j : Fin retained, ∃ source, Slice heads parameters choice source ∧
          CNFHolds source store[j] ∧
            CNFHolds (pairWorld source world) (pathRelation heads parameters program boundary[j] v) := by
  simp [reconstruct, join_correct, anyClauses_correct, guardedPath, pathImage_correct _ hw]

theorem guardedPath_of_path {heads parameters : Nat} {choice source target : Nat → Bool}
    {program : Program count} {start finish : Fin count}
    (hs : Slice heads parameters choice source) (ht : Slice heads parameters choice target)
    (hp : CNFHolds (pairWorld source target) (pathRelation heads parameters program start finish)) :
    CNFHolds (pairWorld source target) (guardedPath heads parameters program start finish) := by
  apply (guardRelation_correct _ _ _ _).mpr
  refine ⟨hp, ?_, ?_, ?_⟩
  · simpa only [pairWorld_even] using hs.theory
  · simpa only [pairWorld_odd] using ht.theory
  · apply slices_agreement
    · simpa only [pairWorld_even] using hs
    · simpa only [pairWorld_odd] using ht

theorem guardedPath_target {heads parameters : Nat} {choice source target : Nat → Bool}
    {program : Program count} {start finish : Fin count}
    (hs : Slice heads parameters choice source)
    (hp : CNFHolds (pairWorld source target) (guardedPath heads parameters program start finish)) :
    Slice heads parameters choice target ∧
      CNFHolds (pairWorld source target) (pathRelation heads parameters program start finish) := by
  obtain ⟨hp, _, _, ha⟩ := (guardRelation_correct _ _ _ _).mp hp
  refine ⟨?_, hp⟩
  intro i hi
  have hpos := ha (2 * i) (by omega)
  have hneg := ha (2 * i + 1) (by omega)
  simp only [pairWorld_even, pairWorld_odd] at hpos hneg
  refine ⟨hpos.symm.trans (hs i hi).1, ?_⟩
  simpa only [Nat.add_assoc] using hneg.symm.trans (hs i hi).2

structure BoundaryValid (heads parameters : Nat) (choice : Nat → Bool)
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained) : Prop where
  lower : ∀ world, Slice heads parameters choice world → ∀ j : Fin retained,
    CNFHolds world (ComparisonParametricPropagation.closure heads parameters program)[boundary[j]] →
      CNFHolds world store[j]
  edges : ∀ (j k : Fin retained) source target,
    Slice heads parameters choice source → Slice heads parameters choice target →
    CNFHolds (pairWorld source target) (pathRelation heads parameters program boundary[j] boundary[k]) →
    CNFHolds source store[j] → CNFHolds target store[k]
  checks : ∀ world, Slice heads parameters choice world → CNFHolds world program.checks ∧
    ∀ v : Fin count, CNFHolds world (ComparisonParametricPropagation.closure heads parameters program)[v] →
      CNFHolds world program.upper[v]
  upper : ∀ (j : Fin retained) (v : Fin count) source target,
    Slice heads parameters choice source → Slice heads parameters choice target →
    CNFHolds source store[j] →
    CNFHolds (pairWorld source target) (pathRelation heads parameters program boundary[j] v) →
      CNFHolds target program.upper[v]

theorem summarize_valid_iff (heads parameters : Nat) (choice : Nat → Bool)
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained) :
    SliceValid heads parameters choice (summarize heads parameters program boundary) store ↔
      BoundaryValid heads parameters choice program boundary store := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [summarize, Fin.getElem_fin, Vector.getElem_ofFn] using h.1.1
    · intro j k source target hs ht hp hv
      have hedge : (⟨j, k, guardedPath heads parameters program boundary[j] boundary[k]⟩ : Edge retained) ∈
          (summarize heads parameters program boundary).edges := by
        simp [summarize]
      have hh := h.1.2 _ hedge (pairWorld source target)
        (by simpa only [pairWorld_even] using hs) (by simpa only [pairWorld_odd] using ht)
        (guardedPath_of_path hs ht hp) (by simpa only [pairWorld_even] using hv)
      simpa only [pairWorld_odd] using hh
    · intro world hw
      have hc := (h.2 world hw).1
      simp only [summarize, meet_correct, allClauses_correct, List.forall_mem_map,
        List.mem_finRange, forall_const, implies_correct] at hc
      exact hc
    · intro j v source target hs ht hv hp
      have hu := (h.2 source hs).2 j hv
      simp only [summarize, Fin.getElem_fin, Vector.getElem_ofFn, allClauses_correct,
        List.forall_mem_map, List.mem_finRange, forall_const, allTargets_correct,
        implies_correct, rename_correct] at hu
      have hh := hu v target (guardedPath_of_path hs ht hp)
      simpa only [Function.comp_def, pairWorld_odd] using hh
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [summarize, Fin.getElem_fin, Vector.getElem_ofFn] using h.lower
    · intro edge he world hl ht hr hv
      simp only [summarize, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at he
      obtain ⟨j, k, rfl⟩ := he
      have hp := (guardRelation_correct _ _ _ _).mp hr |>.1
      simpa only [pairWorld_split] using h.edges j k (fun i => world (2 * i))
        (fun i => world (2 * i + 1)) hl ht (by simpa only [pairWorld_split] using hp) hv
    · intro world hw
      refine ⟨?_, ?_⟩
      · simpa only [summarize, meet_correct, allClauses_correct, List.forall_mem_map,
          List.mem_finRange, forall_const, implies_correct] using h.checks world hw
      · intro j hv
        simp only [summarize, Fin.getElem_fin, Vector.getElem_ofFn, allClauses_correct,
          List.forall_mem_map, List.mem_finRange, forall_const, allTargets_correct,
          implies_correct, rename_correct]
        intro v target hp
        obtain ⟨ht, hp⟩ := guardedPath_target hw hp
        simpa only [Function.comp_def, pairWorld_odd] using h.upper j v world target hw ht hv hp

theorem anyClauses_positive {clauses : List CNF}
    (h : ∀ c ∈ clauses, Positive c) : Positive (anyClauses clauses) := by
  induction clauses with
  | nil => simp [anyClauses, Positive]
  | cons c cs ih =>
    exact join_positive (h c (by simp)) (ih (fun d hd => h d (by simp [hd])))

theorem anyClauses_supported {domain : List Nat} {clauses : List CNF}
    (h : ∀ c ∈ clauses, Supported domain c) : Supported domain (anyClauses clauses) := by
  induction clauses with
  | nil => simp [anyClauses, Supported, CNFPropagation.atoms]
  | cons c cs ih =>
    exact join_supported (h c (by simp)) (ih (fun d hd => h d (by simp [hd])))

theorem reconstruct_positive (heads parameters : Nat) (program : Program count)
    (boundary : Vector (Fin count) retained) (store : Store retained) :
    (reconstruct heads parameters program boundary store).Positive := by
  intro v
  simp only [reconstruct, Fin.getElem_fin, Vector.getElem_ofFn]
  apply join_positive (ComparisonParametricPropagation.closure_positive _ _ _ v)
  apply anyClauses_positive
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  exact image_positive _ _ _

theorem reconstruct_supported (heads parameters : Nat) (program : Program count)
    (boundary : Vector (Fin count) retained) (store : Store retained) :
    (reconstruct heads parameters program boundary store).Supported (heads + 2 * parameters) := by
  intro v
  simp only [reconstruct, Fin.getElem_fin, Vector.getElem_ofFn]
  apply join_supported (ComparisonParametricPropagation.closure_supported _ _ _ v)
  apply anyClauses_supported
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  exact image_supported _ _ _

theorem reconstruct_closed {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} (boundary : Vector (Fin count) retained) (store : Store retained)
    (hs : EdgesSupported (heads + 2 * parameters) program) :
    SliceClosed heads parameters choice program (reconstruct heads parameters program boundary store) := by
  have hc := closure_sliceClosed heads parameters choice program
  refine ⟨?_, ?_⟩
  · intro world hw v hv
    exact (reconstruct_correct _ _ _ hw v).mpr (Or.inl (hc.1 world hw v hv))
  · intro edge he world hl ht hedge hv
    rw [reconstruct_correct _ _ _ hl edge.source] at hv
    apply (reconstruct_correct _ _ _ ht edge.target).mpr
    rcases hv with hb | ⟨j, source, hsource, hv, hp⟩
    · exact Or.inl (hc.2 edge he world hl ht hedge hb)
    · refine Or.inr ⟨j, source, hsource, hv, ?_⟩
      apply pathRelation_step hs he hl ht ?_ hp
      simpa only [pairWorld_split] using hedge

theorem reconstruct_boundary {heads parameters : Nat} {choice world : Nat → Bool}
    {program : Program count} {boundary : Vector (Fin count) retained} {store : Store retained}
    (h : BoundaryValid heads parameters choice program boundary store)
    (hw : Slice heads parameters choice world) (j : Fin retained) :
    CNFHolds world (reconstruct heads parameters program boundary store)[boundary[j]] ↔
      CNFHolds world store[j] := by
  rw [reconstruct_correct _ _ _ hw]
  constructor
  · rintro (hb | ⟨k, source, hs, hv, hp⟩)
    · exact h.lower world hw j hb
    · exact h.edges k j source world hs hw hp hv
  · intro hv
    refine Or.inr ⟨j, world, hw, hv, ?_⟩
    apply pathRelation_refl boundary[j]
    · simpa only [pairWorld_odd] using hw
    · simp only [pairWorld_even, pairWorld_odd, implies_true]

theorem reconstruct_valid {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {boundary : Vector (Fin count) retained} {store : Store retained}
    (hs : EdgesSupported (heads + 2 * parameters) program)
    (h : BoundaryValid heads parameters choice program boundary store) :
    SliceValid heads parameters choice program (reconstruct heads parameters program boundary store) := by
  refine ⟨reconstruct_closed boundary store hs, ?_⟩
  intro world hw
  refine ⟨(h.checks world hw).1, ?_⟩
  intro v hv
  rcases (reconstruct_correct _ _ _ hw v).mp hv with hb | ⟨j, source, hs, hv, hp⟩
  · exact (h.checks world hw).2 v hb
  · exact h.upper j v source world hs hw hv hp

def BoundaryAgreement (heads parameters : Nat) (choice : Nat → Bool)
    (boundary : Vector (Fin count) retained) (full : Store count) (retainedStore : Store retained) : Prop :=
  ∀ world, Slice heads parameters choice world → ∀ j : Fin retained,
    CNFHolds world full[boundary[j]] ↔ CNFHolds world retainedStore[j]

theorem pathRelation_pair_least {heads parameters : Nat} {choice sourceValues targetValues : Nat → Bool}
    {program : Program count} {store : Store count} {source target : Fin count}
    (hparameters : 0 < parameters) (hp : store.Positive) (hs : store.Supported heads)
    (hc : SliceClosed heads parameters choice program store)
    (ht : Slice heads parameters choice targetValues)
    (hsource : CNFHolds sourceValues store[source])
    (hpath : CNFHolds (pairWorld sourceValues targetValues)
      (pathRelation heads parameters program source target)) :
    CNFHolds targetValues store[target] := by
  have hh := pathRelation_least hparameters hp hs hc
    (world := pairWorld sourceValues targetValues) (by simpa only [pairWorld_odd] using ht)
    (by simpa only [pairWorld_even] using hsource) hpath
  simpa only [pairWorld_odd] using hh

theorem summarize_complete {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {boundary : Vector (Fin count) retained}
    {full : Store count} {store : Store retained}
    (hparameters : 0 < parameters) (hp : full.Positive) (hs : full.Supported heads)
    (hc : SliceValid heads parameters choice program full)
    (ha : BoundaryAgreement heads parameters choice boundary full store) :
    SliceValid heads parameters choice (summarize heads parameters program boundary) store := by
  apply (summarize_valid_iff _ _ _ _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro world hw j hb
    exact (ha world hw j).mp
      (ComparisonParametricPropagation.slice_least hparameters hp hs hc.1 hw boundary[j] hb)
  · intro j k source target hl ht hpath hv
    exact (ha target ht k).mp (pathRelation_pair_least hparameters hp hs hc.1 ht
      ((ha source hl j).mpr hv) hpath)
  · intro world hw
    refine ⟨(hc.2 world hw).1, ?_⟩
    intro v hv
    exact (hc.2 world hw).2 v
      (ComparisonParametricPropagation.slice_least hparameters hp hs hc.1 hw v hv)
  · intro j v source target hl ht hv hpath
    exact (hc.2 target ht).2 v (pathRelation_pair_least hparameters hp hs hc.1 ht
      ((ha source hl j).mpr hv) hpath)

theorem witness_correct {heads parameters : Nat} {choice world : Nat → Bool}
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained)
    (hw : Slice heads parameters choice world) (v : Fin count) :
    CNFHolds world (witness heads parameters choice program boundary store)[v] ↔
      CNFHolds world (reconstruct heads parameters program boundary store)[v] := by
  simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
    specialize_of_slice (reconstruct_supported heads parameters program boundary store v) hw

theorem summarize_sound {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {boundary : Vector (Fin count) retained} {store : Store retained}
    (hs : EdgesSupported (heads + 2 * parameters) program)
    (h : SliceValid heads parameters choice (summarize heads parameters program boundary) store) :
    let full := witness heads parameters choice program boundary store
    full.Positive ∧ full.Supported heads ∧ SliceValid heads parameters choice program full ∧
      BoundaryAgreement heads parameters choice boundary full store := by
  have hb := (summarize_valid_iff _ _ _ _ _ _).mp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_positive (heads := heads) (choice := choice)
        (reconstruct_positive heads parameters program boundary store v)
  · intro v
    simpa only [witness, specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_supported heads choice (reconstruct heads parameters program boundary store)[v]
  · apply (reconstruct_valid hs hb).congr
    intro world hw v
    exact (witness_correct _ _ _ hw v).symm
  · intro world hw j
    exact (witness_correct _ _ _ hw boundary[j]).trans (reconstruct_boundary hb hw j)

/-- Exact elimination of internal positive-coordinate states. All retained states
share one head-polynomial interpretation, and relational guards preserve every
parameter value. The constructed full solution contains no new truth-table atoms. -/
theorem summarize_iff {heads parameters : Nat} (hparameters : 0 < parameters)
    (choice : Nat → Bool) (program : Program count) (boundary : Vector (Fin count) retained)
    (store : Store retained) (hs : EdgesSupported (heads + 2 * parameters) program) :
    SliceValid heads parameters choice (summarize heads parameters program boundary) store ↔
      ∃ full : Store count, full.Positive ∧ full.Supported heads ∧
        SliceValid heads parameters choice program full ∧
          BoundaryAgreement heads parameters choice boundary full store := by
  exact ⟨fun h => ⟨witness heads parameters choice program boundary store, summarize_sound hs h⟩,
    fun ⟨_, hp, hs, hc, ha⟩ => summarize_complete hparameters hp hs hc ha⟩

/-- A parameter-dependent positive solution can be specialized on any one slice
without changing its obligations or its retained nominal states. -/
theorem summarize_complete_parametric {heads parameters : Nat} {choice : Nat → Bool}
    {program : Program count} {boundary : Vector (Fin count) retained}
    {full : Store count} {store : Store retained}
    (hparameters : 0 < parameters) (hp : full.Positive)
    (hs : full.Supported (heads + 2 * parameters))
    (hc : SliceValid heads parameters choice program full)
    (ha : BoundaryAgreement heads parameters choice boundary full store) :
    SliceValid heads parameters choice (summarize heads parameters program boundary) store := by
  have heq : ∀ world, Slice heads parameters choice world → ∀ v : Fin count,
      CNFHolds world (specializeStore heads choice full)[v] ↔ CNFHolds world full[v] := by
    intro world hw v
    simpa only [specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_of_slice (hs v) hw
  apply summarize_complete hparameters (full := specializeStore heads choice full)
  · intro v
    simpa only [specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_positive (heads := heads) (choice := choice) (hp v)
  · intro v
    simpa only [specializeStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      specialize_supported heads choice full[v]
  · exact hc.congr (fun world hw v => (heq world hw v).symm)
  · intro world hw j
    exact (heq world hw boundary[j]).trans (ha world hw j)

/-- The same finite reconstructed formulas solve every admissible parameter
slice. `allowed` may describe residual source strategies and target assumptions;
no satisfiability or unrestricted global-definedness premise is imposed. -/
theorem summarize_uniform_iff {heads parameters : Nat} (hparameters : 0 < parameters)
    (allowed : (Nat → Bool) → Prop) (program : Program count)
    (boundary : Vector (Fin count) retained) (store : Store retained)
    (hs : EdgesSupported (heads + 2 * parameters) program) :
    (∀ choice, allowed choice →
      SliceValid heads parameters choice (summarize heads parameters program boundary) store) ↔
      ∃ full : Store count, full.Positive ∧ full.Supported (heads + 2 * parameters) ∧
        ∀ choice, allowed choice → SliceValid heads parameters choice program full ∧
          BoundaryAgreement heads parameters choice boundary full store := by
  constructor
  · intro h
    refine ⟨reconstruct heads parameters program boundary store,
      reconstruct_positive _ _ _ _ _, reconstruct_supported _ _ _ _ _, ?_⟩
    intro choice hchoice
    have hb := (summarize_valid_iff _ _ _ _ _ _).mp (h choice hchoice)
    refine ⟨reconstruct_valid hs hb, ?_⟩
    intro world hw j
    exact reconstruct_boundary hb hw j
  · rintro ⟨full, hp, hf, h⟩ choice hchoice
    obtain ⟨hc, ha⟩ := h choice hchoice
    exact summarize_complete_parametric hparameters hp hf hc ha

end ModalityInference.ComparisonBoundaryPropagation
