import ModalityInference.ComparisonJointSolver
import ModalityInference.Proofs.ComparisonJointNominal
import ModalityInference.Proofs.ComparisonJointModeWitness

namespace ModalityInference.ComparisonJointSolver

open ComparisonPropagation ComparisonJointClauses ComparisonSelectorPropagation

theorem decodeLiteral_correct (heads : Nat) (selectors : Nat → Bool) (literal : Literal) :
    selectors (decodeLiteral heads literal).1 = (decodeLiteral heads literal).2 ↔
      fixedValue heads (choices selectors) literal.1 = literal.2 := by
  dsimp only [decodeLiteral, fixedValue, choices]
  split
  · rfl
  · cases literal.2 <;> cases selectors (2 * ((literal.1 - heads) / 2) + 1) <;> simp

theorem decodeCNF_correct (heads : Nat) (selectors : Nat → Bool) (clauses : CNF) :
    CNFHolds selectors (decodeCNF heads clauses) ↔
      CNFHolds (fixedValue heads (choices selectors)) clauses := by
  simp only [decodeCNF, CNFHolds, List.forall_mem_map]
  apply forall_congr' fun c => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨v, b, hv, he⟩
    obtain ⟨literal, hl, heq⟩ := List.mem_map.mp hv
    have he' : selectors (decodeLiteral heads literal).1 = (decodeLiteral heads literal).2 := by
      simpa only [heq] using he
    exact ⟨literal.1, literal.2, hl, (decodeLiteral_correct _ _ _).mp he'⟩
  · rintro ⟨v, b, hv, he⟩
    exact ⟨(decodeLiteral heads (v, b)).1, (decodeLiteral heads (v, b)).2,
      List.mem_map.mpr ⟨(v, b), hv, rfl⟩, (decodeLiteral_correct _ _ _).mpr he⟩

theorem fixedValue_slice (heads parameters : Nat) (choice : Nat → Bool) :
    Slice heads parameters choice (fixedValue heads choice) := by
  intro i hi
  simp [fixedValue, Nat.add_assoc]

theorem selectorChoice_fixedValue (heads : Nat) (choice : Nat → Bool) :
    ComparisonSelectorPropagation.selectorChoice heads (fixedValue heads choice) = choice := by
  funext i
  exact (fixedValue_slice heads (i + 1) choice i (by omega)).1

theorem nominalQuery_correct (clauses : List (JointClause heads count)) (selectors : Nat → Bool) :
    CNFHolds selectors (decodeCNF heads
      (ComparisonSelectorPropagation.query heads (2 * clauses.length) (nominalProgram clauses))) ↔
      ∃ store : Store count, store.Polynomial heads ∧
        SliceValid heads (2 * clauses.length) (choices selectors) (nominalProgram clauses) store := by
  rw [decodeCNF_correct, ComparisonSelectorPropagation.query_correct, selectorChoice_fixedValue]
  have ht := (fixedValue_slice heads (2 * clauses.length) (choices selectors)).theory
  simp only [ht, true_and]
  exact residualQuery_iff _ _ _ _

theorem modeClauses_correct (side : Nat → Bool) (component : Bool)
    (clauses : List (JointClause heads count)) (selectors values : Nat → Bool) :
    CNFHolds (ModalSynthesis.encode selectors values) (modeClauses side component clauses) ↔
      ∀ i (hi : i < clauses.length), selectors (4 * i + 1) = true ∨
        selectors (4 * i + 3) = !component ∨
          ClauseHolds values (clauses[i].modes.filter fun literal => side literal.1 == component) := by
  simp only [modeClauses, CNFHolds, List.forall_mem_map, List.forall_mem_zipIdx']
  apply forall_congr' fun i => forall_congr' fun hi => ?_
  have h₁ : 4 * i + 1 = 2 * (2 * i) + 1 := by omega
  have h₂ : 4 * i + 3 = 2 * (2 * i + 1) + 1 := by omega
  rw [h₁, h₂, clauseHolds_cons, ModalSynthesis.clause_component]
  simp only [ModalSynthesis.encode_odd, ModalSynthesis.encode_even]

theorem modeClauses_supported (side : Nat → Bool) (component : Bool)
    (clauses : List (JointClause heads count)) :
    ComparisonJointModes.ComponentSupported side component (modeClauses side component clauses) := by
  apply ComparisonJointModes.guarded_components_supported side component clauses JointClause.modes
    (fun i => [(4 * i + 1, true), (4 * i + 3, !component)])
  intro i hi literal hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp only [ModalSynthesis.selector, beq_iff_eq] <;> omega

def SelectorsValid (side : Nat → Bool) (clauses : List (JointClause heads count))
    (store : Store count) (strategy : (Nat → Bool) → Nat → Bool) (selectors : Nat → Bool) : Prop :=
  (∀ i (hi : i < clauses.length), selectors (4 * i + 1) = true →
    ∀ world, clauses[i].head.Holds store world) ∧
  ∀ world, CNFHolds (ModalSynthesis.encode selectors (strategy world)) (modeClauses side true clauses) ∧
    CNFHolds (ModalSynthesis.encode selectors (strategy world)) (modeClauses side false clauses)

theorem selectors_complete {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)} {store : Store count}
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy)
    (h : Holds store strategy clauses) :
    ∃ selectors, SelectorsValid side clauses store strategy selectors := by
  classical
  let headChoice : Nat → Bool := fun i => if hi : i < clauses.length then
    decide (∀ world, clauses[i].head.Holds store world) else false
  let axisChoice : Nat → Bool := fun i => if hi : i < clauses.length then
    decide (∀ world, ClauseHolds (strategy world)
      (clauses[i].modes.filter fun literal => side literal.1 == true)) else false
  let selectors : Nat → Bool := fun v =>
    if v % 4 == 1 then headChoice (v / 4) else axisChoice (v / 4)
  have hhead (i : Nat) (hi : i < clauses.length) : selectors (4 * i + 1) =
      decide (∀ world, clauses[i].head.Holds store world) := by
    simp [selectors, headChoice, show (4 * i + 1) / 4 = i by omega, hi]
  have haxis (i : Nat) (hi : i < clauses.length) : selectors (4 * i + 3) =
      decide (∀ world, ClauseHolds (strategy world)
        (clauses[i].modes.filter fun literal => side literal.1 == true)) := by
    simp [selectors, axisChoice, show (4 * i + 3) / 4 = i by omega, hi]
  refine ⟨selectors, ?_, ?_⟩
  · intro i hi hs
    exact of_decide_eq_true ((hhead i hi).symm.trans hs)
  · have hcomponent (b : Bool) (world : Nat → Bool) :
        CNFHolds (ModalSynthesis.encode selectors (strategy world)) (modeClauses side b clauses) := by
      rw [modeClauses_correct]
      intro i hi
      by_cases hn : ∀ headWorld, clauses[i].head.Holds store headWorld
      · exact Or.inl ((hhead i hi).trans (decide_eq_true hn))
      · have hm : ∀ modeWorld, ClauseHolds (strategy modeWorld) clauses[i].modes := by
          obtain ⟨headWorld, hn⟩ := not_forall.mp hn
          intro modeWorld
          exact (h headWorld modeWorld clauses[i] (List.getElem_mem hi)).resolve_left hn
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

theorem selectors_sound {side : Nat → Bool} {clauses : List (JointClause heads count)}
    {store : Store count} {strategy : (Nat → Bool) → Nat → Bool} {selectors : Nat → Bool}
    (h : SelectorsValid side clauses store strategy selectors) : Holds store strategy clauses := by
  intro headWorld modeWorld clause hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  cases hs : selectors (4 * i + 1) with
  | true => exact Or.inl (h.1 i hi hs headWorld)
  | false =>
    have hm (b : Bool) := (modeClauses_correct side b clauses selectors (strategy modeWorld)).mp
      (by cases b; exact (h.2 modeWorld).2; exact (h.2 modeWorld).1) i hi
    have hh := hm (selectors (4 * i + 3))
    have hne : selectors (4 * i + 3) ≠ !selectors (4 * i + 3) := by
      cases selectors (4 * i + 3) <;> decide
    simp only [hs, Bool.false_eq_true, false_or, hne] at hh
    obtain ⟨v, b, hv, he⟩ := hh
    exact Or.inr ⟨v, b, (List.mem_filter.mp hv).1, he⟩

theorem selectors_iff {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)} {store : Store count}
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy) :
    Holds store strategy clauses ↔ ∃ selectors, SelectorsValid side clauses store strategy selectors :=
  ⟨selectors_complete hu, fun ⟨_, h⟩ => selectors_sound h⟩

theorem nominalQuery_sound {clauses : List (JointClause heads count)} {selectors : Nat → Bool}
    (h : CNFHolds selectors (decodeCNF heads
      (ComparisonSelectorPropagation.query heads (2 * clauses.length) (nominalProgram clauses)))) :
    (ComparisonSelectorPropagation.witness heads (2 * clauses.length) (choices selectors)
      (nominalProgram clauses)).Polynomial heads ∧
      SliceValid heads (2 * clauses.length) (choices selectors) (nominalProgram clauses)
        (ComparisonSelectorPropagation.witness heads (2 * clauses.length) (choices selectors)
          (nominalProgram clauses)) := by
  rw [decodeCNF_correct, ComparisonSelectorPropagation.query_correct, selectorChoice_fixedValue] at h
  exact residualQuery_sound h.2

theorem query_sound {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)} {selectors : Nat → Bool}
    (h : CNFHolds selectors (query side flex clauses)) :
    (witness side flex clauses selectors).types.Polynomial heads ∧
      ModalSynthesis.Uniform side flex (fun world v =>
        ((witness side flex clauses selectors).modes.substitute v).eval world) ∧
      Holds (witness side flex clauses selectors).types
        (fun world v => ((witness side flex clauses selectors).modes.substitute v).eval world) clauses := by
  obtain ⟨ht, hm⟩ := (cnfHolds_append _ _ _).mp h
  obtain ⟨hp, hv⟩ := nominalQuery_sound ht
  refine ⟨hp, ComparisonJointModes.witness_uniform (modeClauses_supported side true clauses)
    (modeClauses_supported side false clauses) selectors, ?_⟩
  apply selectors_sound (selectors := selectors)
  refine ⟨?_, ?_⟩
  · intro i hi hs world
    have hv := (nominalProgram_valid_iff hp.2.1 (choices selectors)).mp hv i hi
    apply hv _ world
    simpa only [choices, show 2 * (2 * i) + 1 = 4 * i + 1 by omega] using hs
  · exact ComparisonJointModes.witness_sound (modeClauses_supported side true clauses)
      (modeClauses_supported side false clauses) hm

theorem query_complete {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)} {store : Store count}
    {strategy : (Nat → Bool) → Nat → Bool} (hp : store.Polynomial heads)
    (hu : ModalSynthesis.Uniform side flex strategy) (h : Holds store strategy clauses) :
    ∃ selectors, CNFHolds selectors (query side flex clauses) := by
  obtain ⟨selectors, hs⟩ := selectors_complete hu h
  refine ⟨selectors, (cnfHolds_append _ _ _).mpr ⟨?_, ?_⟩⟩
  · apply (nominalQuery_correct clauses selectors).mpr
    refine ⟨store, hp, (nominalProgram_valid_iff hp.2.1 (choices selectors)).mpr ?_⟩
    intro i hi hchoice
    apply hs.1 i hi
    simpa only [choices, show 2 * (2 * i) + 1 = 4 * i + 1 by omega] using hchoice
  · exact ComparisonJointModes.query_complete (modeClauses_supported side true clauses)
      (modeClauses_supported side false clauses) hu hs.2

/-- Exact joint feasibility for a common nominal polynomial and one legal
uniform scalar strategy. The original guards remain in the clause formula. -/
theorem query_iff (side : Nat → Bool) (flex : List Nat) (clauses : List (JointClause heads count)) :
    (∃ selectors, CNFHolds selectors (query side flex clauses)) ↔
      ∃ store : Store count, store.Polynomial heads ∧ ∃ strategy,
        ModalSynthesis.Uniform side flex strategy ∧ Holds store strategy clauses := by
  constructor
  · rintro ⟨selectors, h⟩
    obtain ⟨hp, hu, hh⟩ := query_sound h
    exact ⟨_, hp, _, hu, hh⟩
  · rintro ⟨store, hp, strategy, hu, hh⟩
    exact query_complete hp hu hh

theorem run_sound {fuel : Nat} {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)} {result : Result count flex}
    (h : run fuel side flex clauses = .success result) :
    result.types.Polynomial heads ∧
      ModalSynthesis.Uniform side flex (fun world v => (result.modes.substitute v).eval world) ∧
      Holds result.types (fun world v => (result.modes.substitute v).eval world) clauses := by
  unfold run at h
  cases hr : CNFPropagation.solve fuel (query side flex clauses) with
  | exhausted | rejected => simp [hr, bind, RunResult.bind] at h
  | success selectors =>
    simp only [hr, bind, RunResult.bind, pure, RunResult.success.injEq] at h
    cases h
    exact query_sound (CNFPropagation.solve_sound hr)

theorem run_complete {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)}
    (h : ∃ store : Store count, store.Polynomial heads ∧ ∃ strategy,
      ModalSynthesis.Uniform side flex strategy ∧ Holds store strategy clauses) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel side flex clauses = .success result := by
  obtain ⟨selectors, hs⟩ := (query_iff side flex clauses).mpr h
  obtain ⟨n, hn⟩ := CNFPropagation.solve_complete hs
  refine ⟨n, ?_⟩
  intro fuel hf
  obtain ⟨assignment, ha⟩ := hn fuel hf
  exact ⟨witness side flex clauses (CNFPropagation.valuation assignment),
    by simp [run, ha, bind, RunResult.bind, pure]⟩

theorem run_stable {n : Nat} {side : Nat → Bool} {flex : List Nat}
    {clauses : List (JointClause heads count)} {result : RunResult (Result count flex)}
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

theorem run_terminates (side : Nat → Bool) (flex : List Nat) (clauses : List (JointClause heads count)) :
    ∃ n, ∀ fuel ≥ n, run fuel side flex clauses ≠ .exhausted := by
  obtain ⟨n, hn⟩ := CNFPropagation.solve_terminates (query side flex clauses)
  refine ⟨n, ?_⟩
  intro fuel hf
  cases hr : CNFPropagation.solve fuel (query side flex clauses) with
  | exhausted => exact False.elim (hn fuel hf hr)
  | rejected | success => simp [run, hr, bind, RunResult.bind, pure]

theorem run_reifies {fuel : Nat} {side : Nat → Bool} {flex : List Nat} {basis : List CompareTy}
    {clauses : List (JointClause basis.length count)} {result : Result count flex}
    (h : run fuel side flex clauses = .success result) :
    ∃ images, ComparisonPropagation.reconstruct basis result.types = some images := by
  have hp := (run_sound h).1
  exact reconstruct_complete fun v => reify_complete (hp.1 v) (hp.2.1 v)
    (hp.2.2.1 v) (hp.2.2.2 v)

theorem run_modes_reify {fuel : Nat} {flex : List Nat}
    {clauses : List (JointClause heads count)} {result : Result count flex}
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
    {clauses : List (JointClause heads count)} {result : Result count flex}
    (h : run fuel ModalSynthesis.locality flex clauses = .success result)
    (parameters : List (Nat × ModVar)) :
    ∃ action, SymbolicSchemeModes.assemble result.modes parameters = some action := by
  apply (SymbolicSchemeModes.assemble_iff _ _).mpr
  intro parameter _
  obtain ⟨m, hm⟩ := run_modes_reify h parameter.2
  exact Option.isSome_iff_exists.mpr ⟨m, hm⟩

theorem run_actual {fuel : Nat} {modeIds : List Nat}
    {clauses : List (JointClause heads count)} {result : Result count (SchemeModeSynthesis.atoms modeIds)}
    {action : Substitution}
    (h : run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds) clauses = .success result)
    (ha : SymbolicSchemeModes.assemble result.modes (SchemeModeSynthesis.parameters modeIds) = some action)
    (η : ModVar → Mode) :
    ∃ τ : ModVar → Mode, (∀ v, (action.mode v).eval (some ∘ η) = some (τ v)) ∧
      ∀ headWorld, ∀ clause ∈ clauses,
        clause.head.Holds result.types headWorld ∨ ClauseHolds (encodeModes τ) clause.modes := by
  refine ⟨projectedModes (fun i => (result.modes.substitute i).eval (encodeModes η)),
    SchemeModeSynthesis.assemble_eval ha η, ?_⟩
  rw [SchemeModeSynthesis.encodeModes_projectedModes]
  intro headWorld clause hc
  exact (run_sound h).2.2 headWorld (encodeModes η) clause hc

end ModalityInference.ComparisonJointSolver
