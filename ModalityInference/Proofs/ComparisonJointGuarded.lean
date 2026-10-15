import ModalityInference.ComparisonJointGuarded
import ModalityInference.Proofs.ComparisonJointSolver

namespace ModalityInference.ComparisonJointGuarded

open ComparisonPropagation ComparisonJointClauses ComparisonSelectorPropagation

def ConstantsHold (values : Fin constants → Bool) (guard : List (Fin constants × Bool)) : Prop :=
  ∃ literal ∈ guard, values literal.1 = literal.2

def Holds (constantsValue : Fin constants → Bool) (store : Store count)
    (strategy : (Nat → Bool) → Nat → Bool) (clauses : List (GuardedClause heads count constants)) : Prop :=
  ∀ headWorld modeWorld, ∀ clause ∈ clauses,
    ConstantsHold constantsValue clause.constants ∨ clause.head.Holds store headWorld ∨
      ClauseHolds (strategy modeWorld) clause.modes

def SelectorsValid (side : Nat → Bool) (clauses : List (GuardedClause heads count constants))
    (store : Store count) (strategy : (Nat → Bool) → Nat → Bool) (selectors : Nat → Bool) : Prop :=
  (∀ i (hi : i < clauses.length), selectors (4 * i + 1) = true →
    ∀ world, clauses[i].head.Holds store world) ∧
  ∀ world, CNFHolds (ModalSynthesis.encode selectors (strategy world)) (modeClauses side true clauses) ∧
    CNFHolds (ModalSynthesis.encode selectors (strategy world)) (modeClauses side false clauses)

theorem constant_guards_correct (selectors values : Nat → Bool) (length : Nat)
    (guard : List (Fin constants × Bool)) :
    ClauseHolds (ModalSynthesis.encode selectors values)
      (guard.map fun literal => (constantAtom length literal.1, literal.2)) ↔
        ConstantsHold (fun i => selectors (constantAtom length i)) guard := by
  simp only [ClauseHolds, List.mem_map, ConstantsHold]
  constructor
  · rintro ⟨v, p, ⟨⟨i, b⟩, hi, he⟩, hv⟩
    cases he
    refine ⟨(i, b), hi, ?_⟩
    have he : constantAtom length i = 2 * (2 * length + i.val) + 1 := by
      simp only [constantAtom]; omega
    simpa only [he, ModalSynthesis.encode_odd] using hv
  · rintro ⟨⟨i, b⟩, hi, hv⟩
    refine ⟨constantAtom length i, b, ⟨(i, b), hi, rfl⟩, ?_⟩
    have he : constantAtom length i = 2 * (2 * length + i.val) + 1 := by
      simp only [constantAtom]; omega
    simpa only [he, ModalSynthesis.encode_odd] using hv

theorem even_clause_correct (selectors values : Nat → Bool) (guard : Clause) :
    ClauseHolds (ModalSynthesis.encode selectors values)
      (guard.map fun literal => (2 * literal.1, literal.2)) ↔ ClauseHolds values guard := by
  have h := rename_correct (2 * ·) [guard] (ModalSynthesis.encode selectors values)
  simpa only [rename, List.map_cons, List.map_nil, CNFHolds, List.mem_singleton,
    forall_eq, Function.comp_def, ModalSynthesis.encode_even] using h

theorem modeClauses_correct (side : Nat → Bool) (component : Bool)
    (clauses : List (GuardedClause heads count constants)) (selectors values : Nat → Bool) :
    CNFHolds (ModalSynthesis.encode selectors values) (modeClauses side component clauses) ↔
      ∀ i (hi : i < clauses.length),
        ConstantsHold (fun j => selectors (constantAtom clauses.length j)) clauses[i].constants ∨
        selectors (4 * i + 1) = true ∨ selectors (4 * i + 3) = !component ∨
          ClauseHolds values (clauses[i].modes.filter fun literal => side literal.1 == component) := by
  simp only [modeClauses, CNFHolds, List.forall_mem_map, List.forall_mem_zipIdx']
  apply forall_congr' fun i => forall_congr' fun hi => ?_
  have h₁ : 4 * i + 1 = 2 * (2 * i) + 1 := by omega
  have h₂ : 4 * i + 3 = 2 * (2 * i + 1) + 1 := by omega
  rw [clauseHolds_append, clauseHolds_append, constant_guards_correct]
  simp only [h₁, h₂, clauseHolds_cons, ModalSynthesis.encode_odd,
    even_clause_correct, show ¬ClauseHolds (ModalSynthesis.encode selectors values) [] by
      simp [ClauseHolds], false_or, or_assoc]

theorem selectors_complete {side : Nat → Bool} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {store : Store count}
    {strategy : (Nat → Bool) → Nat → Bool} {constantsValue : Fin constants → Bool}
    (hu : ModalSynthesis.Uniform side flex strategy)
    (h : Holds constantsValue store strategy clauses) :
    ∃ selectors, (∀ i, selectors (constantAtom clauses.length i) = constantsValue i) ∧
      SelectorsValid side clauses store strategy selectors := by
  classical
  let headChoice : Nat → Bool := fun i => if hi : i < clauses.length then
    decide (∀ world, clauses[i].head.Holds store world) else false
  let axisChoice : Nat → Bool := fun i => if hi : i < clauses.length then
    decide (∀ world, ClauseHolds (strategy world)
      (clauses[i].modes.filter fun literal => side literal.1 == true)) else false
  let selectors : Nat → Bool := fun v =>
    if 4 * clauses.length ≤ v then
      if hi : (v - 4 * clauses.length) / 2 < constants then
        constantsValue ⟨(v - 4 * clauses.length) / 2, hi⟩ else false
    else if v % 4 == 1 then headChoice (v / 4) else axisChoice (v / 4)
  have hc (i : Fin constants) : selectors (constantAtom clauses.length i) = constantsValue i := by
    have hd : (constantAtom clauses.length i - 4 * clauses.length) / 2 = i.val := by
      simp only [constantAtom]; omega
    simp only [selectors, show 4 * clauses.length ≤ constantAtom clauses.length i by
      simp only [constantAtom]; omega, ↓reduceIte, hd, i.isLt, ↓reduceDIte]
  have hhead (i : Nat) (hi : i < clauses.length) : selectors (4 * i + 1) =
      decide (∀ world, clauses[i].head.Holds store world) := by
    simp [selectors, headChoice, show ¬4 * clauses.length ≤ 4 * i + 1 by omega,
      show (4 * i + 1) / 4 = i by omega, hi]
  have haxis (i : Nat) (hi : i < clauses.length) : selectors (4 * i + 3) =
      decide (∀ world, ClauseHolds (strategy world)
        (clauses[i].modes.filter fun literal => side literal.1 == true)) := by
    simp [selectors, axisChoice, show ¬4 * clauses.length ≤ 4 * i + 3 by omega,
      show (4 * i + 3) / 4 = i by omega, hi]
  refine ⟨selectors, hc, ?_, ?_⟩
  · intro i hi hs
    exact of_decide_eq_true ((hhead i hi).symm.trans hs)
  · have hcomponent (b : Bool) (world : Nat → Bool) :
        CNFHolds (ModalSynthesis.encode selectors (strategy world)) (modeClauses side b clauses) := by
      rw [modeClauses_correct]
      intro i hi
      by_cases hk : ConstantsHold constantsValue clauses[i].constants
      · exact Or.inl (by simpa only [hc] using hk)
      · apply Or.inr
        by_cases hn : ∀ headWorld, clauses[i].head.Holds store headWorld
        · exact Or.inl ((hhead i hi).trans (decide_eq_true hn))
        · have hm : ∀ modeWorld, ClauseHolds (strategy modeWorld) clauses[i].modes := by
            obtain ⟨headWorld, hn⟩ := not_forall.mp hn
            intro modeWorld
            exact ((h headWorld modeWorld clauses[i] (List.getElem_mem hi)).resolve_left hk).resolve_left hn
          have hf := ModalSynthesis.clause_factor hu hm
          by_cases hl : ∀ modeWorld, ClauseHolds (strategy modeWorld)
              (clauses[i].modes.filter fun literal => side literal.1 == true)
          · cases b
            · exact Or.inr (Or.inl ((haxis i hi).trans (decide_eq_true hl)))
            · exact Or.inr (Or.inr (hl world))
          · cases b
            · exact Or.inr (Or.inr ((hf.resolve_left hl) world))
            · exact Or.inr (Or.inl ((haxis i hi).trans (decide_eq_false hl)))
    intro world
    exact ⟨hcomponent true world, hcomponent false world⟩

theorem selectors_sound {side : Nat → Bool} {clauses : List (GuardedClause heads count constants)}
    {store : Store count} {strategy : (Nat → Bool) → Nat → Bool} {selectors : Nat → Bool}
    (h : SelectorsValid side clauses store strategy selectors) :
    Holds (fun i => selectors (constantAtom clauses.length i)) store strategy clauses := by
  intro headWorld modeWorld clause hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  cases hs : selectors (4 * i + 1) with
  | true => exact Or.inr (Or.inl (h.1 i hi hs headWorld))
  | false =>
    have hm (b : Bool) := (modeClauses_correct side b clauses selectors (strategy modeWorld)).mp
      (by cases b; exact (h.2 modeWorld).2; exact (h.2 modeWorld).1) i hi
    have hh := hm (selectors (4 * i + 3))
    have hne : selectors (4 * i + 3) ≠ !selectors (4 * i + 3) := by
      cases selectors (4 * i + 3) <;> decide
    simp only [hs, Bool.false_eq_true, false_or, hne] at hh
    rcases hh with hk | ⟨v, b, hv, he⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inr ⟨v, b, (List.mem_filter.mp hv).1, he⟩)

theorem modeClauses_supported (side : Nat → Bool) (component : Bool)
    (clauses : List (GuardedClause heads count constants)) :
    ComparisonJointModes.ComponentSupported side component (modeClauses side component clauses) := by
  intro v hv
  simp only [CNFPropagation.atoms, List.mem_flatMap, List.mem_map, modeClauses] at hv
  obtain ⟨c, ⟨⟨entry, i⟩, hi, rfl⟩, literal, hl, rfl⟩ := hv
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with (⟨literal, _, rfl⟩ | rfl | rfl) | ⟨literal, hl, rfl⟩
  · left
    simp only [constantAtom, ModalSynthesis.selector, beq_iff_eq]
    omega
  · left
    simp only [ModalSynthesis.selector, beq_iff_eq]
    omega
  · left
    simp only [ModalSynthesis.selector, beq_iff_eq]
    omega
  · right
    exact ⟨literal.1, rfl, by simpa using (List.mem_filter.mp hl).2⟩

theorem query_sound {side : Nat → Bool} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {selectors : Nat → Bool}
    (h : CNFHolds selectors (query side flex clauses)) :
    (witness side flex clauses selectors).types.Polynomial heads ∧
      ModalSynthesis.Uniform side flex (fun world v =>
        ((witness side flex clauses selectors).modes.substitute v).eval world) ∧
      Holds (fun i => (witness side flex clauses selectors).constants[i])
        (witness side flex clauses selectors).types
        (fun world v => ((witness side flex clauses selectors).modes.substitute v).eval world) clauses := by
  obtain ⟨ht, hm⟩ := (cnfHolds_append _ _ _).mp h
  have hplain : CNFHolds selectors (ComparisonJointSolver.decodeCNF heads
      (ComparisonSelectorPropagation.query heads (2 * (plain clauses).length)
        (nominalProgram (plain clauses)))) := by simpa only [plain, List.length_map] using ht
  obtain ⟨hp, hv⟩ := ComparisonJointSolver.nominalQuery_sound hplain
  refine ⟨by simpa only [plain, List.length_map] using hp,
    ComparisonJointModes.witness_uniform (modeClauses_supported side true clauses)
      (modeClauses_supported side false clauses) selectors, ?_⟩
  have hc : (fun i => (witness side flex clauses selectors).constants[i]) =
      (fun i => selectors (constantAtom clauses.length i)) := by
    funext i
    simp only [witness, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [hc]
  apply selectors_sound (selectors := selectors)
  refine ⟨?_, ?_⟩
  · intro i hi hs world
    have hv := (nominalProgram_valid_iff hp.2.1 (ComparisonJointSolver.choices selectors)).mp hv i
      (by simpa only [plain, List.length_map] using hi)
    have hh := hv (by simpa only [ComparisonJointSolver.choices,
      show 2 * (2 * i) + 1 = 4 * i + 1 by omega] using hs) world
    simpa only [plain, List.getElem_map, List.length_map] using hh
  · exact ComparisonJointModes.witness_sound (modeClauses_supported side true clauses)
      (modeClauses_supported side false clauses) hm

theorem query_complete {side : Nat → Bool} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {store : Store count}
    {strategy : (Nat → Bool) → Nat → Bool} {constantsValue : Fin constants → Bool}
    (hp : store.Polynomial heads) (hu : ModalSynthesis.Uniform side flex strategy)
    (h : Holds constantsValue store strategy clauses) :
    ∃ selectors, (∀ i, selectors (constantAtom clauses.length i) = constantsValue i) ∧
      CNFHolds selectors (query side flex clauses) := by
  obtain ⟨selectors, hc, hs⟩ := selectors_complete hu h
  refine ⟨selectors, hc, (cnfHolds_append _ _ _).mpr ⟨?_, ?_⟩⟩
  · have hh : CNFHolds selectors (ComparisonJointSolver.decodeCNF heads
        (ComparisonSelectorPropagation.query heads (2 * (plain clauses).length)
          (nominalProgram (plain clauses)))) := by
      apply (ComparisonJointSolver.nominalQuery_correct (plain clauses) selectors).mpr
      refine ⟨store, hp, (nominalProgram_valid_iff hp.2.1 (ComparisonJointSolver.choices selectors)).mpr ?_⟩
      intro i hi hchoice world
      have hs := hs.1 i (by simpa only [plain, List.length_map] using hi)
        (by simpa only [ComparisonJointSolver.choices,
          show 2 * (2 * i) + 1 = 4 * i + 1 by omega] using hchoice) world
      simpa only [plain, List.getElem_map] using hs
    simpa only [plain, List.length_map] using hh
  · exact ComparisonJointModes.query_complete (modeClauses_supported side true clauses)
      (modeClauses_supported side false clauses) hu hs.2

/-- Existing constant guards, nominal polynomials, and axis-respecting mode
strategies are synthesized jointly, with every original clause retained. -/
theorem query_iff (side : Nat → Bool) (flex : List Nat)
    (clauses : List (GuardedClause heads count constants)) :
    (∃ selectors, CNFHolds selectors (query side flex clauses)) ↔
      ∃ constantsValue store, store.Polynomial heads ∧ ∃ strategy,
        ModalSynthesis.Uniform side flex strategy ∧ Holds constantsValue store strategy clauses := by
  constructor
  · rintro ⟨selectors, h⟩
    obtain ⟨hp, hu, hh⟩ := query_sound h
    exact ⟨_, _, hp, _, hu, hh⟩
  · rintro ⟨constantsValue, store, hp, strategy, hu, hh⟩
    obtain ⟨selectors, _, hs⟩ := query_complete hp hu hh
    exact ⟨selectors, hs⟩

theorem run_sound {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {result : Result count constants flex}
    (h : run fuel side flex clauses = .success result) :
    result.types.Polynomial heads ∧
      ModalSynthesis.Uniform side flex (fun world v => (result.modes.substitute v).eval world) ∧
      Holds (fun i => result.constants[i]) result.types
        (fun world v => (result.modes.substitute v).eval world) clauses := by
  unfold run at h
  cases hr : CNFPropagation.solve fuel (query side flex clauses) with
  | exhausted | rejected => simp [hr, bind, RunResult.bind] at h
  | success selectors =>
    simp only [hr, bind, RunResult.bind, pure, RunResult.success.injEq] at h
    cases h
    exact query_sound (CNFPropagation.solve_sound hr)

theorem run_complete {side : Nat → Bool} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)}
    (h : ∃ constantsValue store, store.Polynomial heads ∧ ∃ strategy,
      ModalSynthesis.Uniform side flex strategy ∧ Holds constantsValue store strategy clauses) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel side flex clauses = .success result := by
  obtain ⟨selectors, hs⟩ := (query_iff side flex clauses).mpr h
  obtain ⟨n, hn⟩ := CNFPropagation.solve_complete hs
  refine ⟨n, ?_⟩
  intro fuel hf
  obtain ⟨assignment, ha⟩ := hn fuel hf
  exact ⟨witness side flex clauses (CNFPropagation.valuation assignment),
    by simp [run, ha, bind, RunResult.bind, pure]⟩

theorem run_stable {n : Nat} {side : Nat → Bool} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {result : RunResult (Result count constants flex)}
    (hne : result ≠ .exhausted) (h : run n side flex clauses = result) :
    ∀ fuel ≥ n, run fuel side flex clauses = result := by
  intro fuel hf
  cases hr : CNFPropagation.solve n (query side flex clauses) with
  | exhausted => exact False.elim (hne (by simpa [run, hr, bind, RunResult.bind] using h.symm))
  | rejected message =>
    have hs := CNFPropagation.solve_stable (by simp) hr fuel hf
    simpa [run, hs, hr, bind, RunResult.bind] using h
  | success assignment =>
    have hs := CNFPropagation.solve_stable (by simp) hr fuel hf
    simpa [run, hs, hr, bind, RunResult.bind] using h

theorem run_terminates (side : Nat → Bool) (flex : List Nat)
    (clauses : List (GuardedClause heads count constants)) :
    ∃ n, ∀ fuel ≥ n, run fuel side flex clauses ≠ .exhausted := by
  obtain ⟨n, hn⟩ := CNFPropagation.solve_terminates (query side flex clauses)
  refine ⟨n, ?_⟩
  intro fuel hf
  cases hr : CNFPropagation.solve fuel (query side flex clauses) with
  | exhausted => exact False.elim (hn fuel hf hr)
  | rejected | success => simp [run, hr, bind, RunResult.bind, pure]

theorem run_reifies {fuel : Nat} {side : Nat → Bool} {flex : List Nat} {basis : List CompareTy}
    {clauses : List (GuardedClause basis.length count constants)} {result : Result count constants flex}
    (h : run fuel side flex clauses = .success result) :
    ∃ images, ComparisonPropagation.reconstruct basis result.types = some images := by
  have hp := (run_sound h).1
  exact reconstruct_complete fun v => reify_complete (hp.1 v) (hp.2.1 v)
    (hp.2.2.1 v) (hp.2.2.2 v)

theorem run_modes_reify {fuel : Nat} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {result : Result count constants flex}
    (h : run fuel ModalSynthesis.locality flex clauses = .success result) (v : ModVar) :
    ∃ m, result.modes.mode v = some m := by
  unfold run at h
  cases hr : CNFPropagation.solve fuel (query ModalSynthesis.locality flex clauses) with
  | exhausted | rejected => simp [hr, bind, RunResult.bind] at h
  | success selectors =>
    simp only [hr, bind, RunResult.bind, pure, RunResult.success.injEq] at h
    cases h
    exact ComparisonJointModes.witness_reifies (modeClauses_supported _ true clauses)
      (modeClauses_supported _ false clauses) _ v

theorem run_modes_assemble {fuel : Nat} {flex : List Nat}
    {clauses : List (GuardedClause heads count constants)} {result : Result count constants flex}
    (h : run fuel ModalSynthesis.locality flex clauses = .success result)
    (parameters : List (Nat × ModVar)) :
    ∃ action, SymbolicSchemeModes.assemble result.modes parameters = some action := by
  apply (SymbolicSchemeModes.assemble_iff _ _).mpr
  intro parameter _
  obtain ⟨m, hm⟩ := run_modes_reify h parameter.2
  exact Option.isSome_iff_exists.mpr ⟨m, hm⟩

theorem run_actual {fuel : Nat} {modeIds : List Nat}
    {clauses : List (GuardedClause heads count constants)}
    {result : Result count constants (SchemeModeSynthesis.atoms modeIds)} {action : Substitution}
    (h : run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds) clauses = .success result)
    (ha : SymbolicSchemeModes.assemble result.modes (SchemeModeSynthesis.parameters modeIds) = some action)
    (η : ModVar → Mode) :
    ∃ τ : ModVar → Mode, (∀ v, (action.mode v).eval (some ∘ η) = some (τ v)) ∧
      ∀ headWorld, ∀ clause ∈ clauses,
        ConstantsHold (fun i => result.constants[i]) clause.constants ∨
          clause.head.Holds result.types headWorld ∨ ClauseHolds (encodeModes τ) clause.modes := by
  refine ⟨projectedModes (fun i => (result.modes.substitute i).eval (encodeModes η)),
    SchemeModeSynthesis.assemble_eval ha η, ?_⟩
  rw [SchemeModeSynthesis.encodeModes_projectedModes]
  intro headWorld clause hc
  exact (run_sound h).2.2 headWorld (encodeModes η) clause hc

end ModalityInference.ComparisonJointGuarded
