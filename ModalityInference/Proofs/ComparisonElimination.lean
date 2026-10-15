import ModalityInference.Proofs.ComparisonWitnessProperties
import ModalityInference.Proofs.Projection
import ModalityInference.Proofs.ComparisonPropagationPointwise

/-! Query obligations preserved by the executable opaque-leaf eliminator. -/
namespace ModalityInference.ComparisonElimination

private theorem all_eval_true (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = true ↔ ∀ e ∈ es, e.eval σ = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr h ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hr⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

private theorem loop_spec (fuel : Nat) (assumptions required : Bounds)
    (groups : List ComparisonGroups.Group) (queries : List BoolExpr)
    (types : List (Nat × CompareTy))
    {final : MProd (List BoolExpr) (List (Nat × CompareTy))}
    (h : forIn groups (⟨queries, types⟩ : MProd (List BoolExpr) (List (Nat × CompareTy)))
      (fun g state => do
      let result ← group fuel assumptions required g
      pure (ForInStep.yield (⟨result.query :: state.fst, state.snd ++ result.types⟩))) =
        RunResult.success final) :
    ∃ results : List Result,
      List.Forall₂ (fun g result => group fuel assumptions required g = .success result)
        groups results ∧
      final.fst = (results.map Result.query).reverse ++ queries ∧
      final.snd = types ++ results.flatMap Result.types := by
  induction groups generalizing queries types final with
  | nil => cases h; exact ⟨[], .nil, rfl, by simp⟩
  | cons g gs ih =>
    simp only [List.forIn_cons, bind, pure, RunResult.bind] at h
    cases hg : group fuel assumptions required g <;> simp only [hg] at h <;> try contradiction
    next result =>
      obtain ⟨results, hr, hq, ht⟩ := ih _ _ h
      refine ⟨result :: results, .cons hg hr, ?_, ?_⟩
      · simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append] using hq
      · simpa only [List.flatMap_cons, List.append_assoc] using ht

theorem run_spec {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {result : Result}
    (h : run fuel p shapes templates reduced = .success result) :
    ∃ groups results,
      ComparisonGroups.collect p shapes templates reduced = .success groups ∧
      List.Forall₂ (fun g output => group fuel p.assumptions reduced.modes g = .success output)
        groups results ∧
      result.types = results.flatMap Result.types ∧
      result.query = .all ((results.map Result.query).reverse ++
        [.imp (boundsModeFormula p.assumptions) (boundsModeFormula reduced.modes)]) := by
  unfold run at h
  simp only [bind, pure, RunResult.bind] at h
  split at h
  · next groups hg =>
    split at h
    · next final hloop =>
      cases h
      obtain ⟨results, hr, hq, ht⟩ := loop_spec fuel p.assumptions reduced.modes groups _ _ hloop
      refine ⟨groups, results, hg, hr, ?_, ?_⟩
      · simpa using ht
      · exact congrArg BoolExpr.all hq
    · contradiction
    · contradiction
  · contradiction
  · contradiction

theorem run_mode_models {fuel p shapes templates reduced result σ}
    (h : run fuel p shapes templates reduced = .success result)
    (hq : result.query.eval σ = true)
    (hΔ : ModeModels p.assumptions (projectedModes σ)) :
    ModeModels reduced.modes (projectedModes σ) := by
  obtain ⟨_, _, _, _, _, he⟩ := run_spec h
  rw [he] at hq
  have hc := (all_eval_true _ _).mp hq _ (List.mem_append_right _ List.mem_cons_self)
  exact (boundsModeFormula_correct _ _).mp
    ((BoolExpr.eval_imp_true _ _ _).mp hc ((boundsModeFormula_correct _ _).mpr hΔ))

theorem run_group_queries {fuel p shapes templates reduced result σ}
    (h : run fuel p shapes templates reduced = .success result)
    (hq : result.query.eval σ = true) :
    ∃ groups, ComparisonGroups.collect p shapes templates reduced = .success groups ∧
      ∀ g ∈ groups, ∃ output, group fuel p.assumptions reduced.modes g = .success output ∧
        output.query.eval σ = true ∧ ∀ entry ∈ output.types, entry ∈ result.types := by
  obtain ⟨groups, results, hg, hr, ht, he⟩ := run_spec h
  refine ⟨groups, hg, ?_⟩
  intro g hgm
  obtain ⟨output, ho, hgo⟩ := forall₂_mem_left hr hgm
  refine ⟨output, hgo, ?_, ?_⟩
  · rw [he] at hq
    apply (all_eval_true _ _).mp hq
    exact List.mem_append_left _ (List.mem_reverse.mpr (List.mem_map.mpr ⟨output, ho, rfl⟩))
  · intro entry hent
    rw [ht]
    exact List.mem_flatMap.mpr ⟨output, ho, hent⟩

theorem run_synthesized_models {fuel modeFuel p shapes templates reduced result modeIds modes}
    (h : run fuel p shapes templates reduced = .success result)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (η : ModVar → Mode) (hη : ModeModels p.assumptions η) :
    ∃ τ : ModVar → Mode,
      (∀ v, (modes.substitution.mode v).eval (some ∘ η) = some (τ v)) ∧
      ModeModels reduced.modes τ := by
  obtain ⟨τ, hτ, hq⟩ := SchemeModeSynthesis.run_actual hm η
  refine ⟨τ, hτ, ?_⟩
  have hΔ : ModeModels p.assumptions τ := by
    apply (ModeModels.congr p.assumptions ?_).mpr hη
    intro v hv
    exact Option.some.inj ((hτ v).symm.trans (by rw [hf v hv]; rfl))
  simpa only [projectedModes_encodeModes] using
    run_mode_models h hq (by simpa only [projectedModes_encodeModes] using hΔ)

theorem run_synthesized_submode {fuel modeFuel p shapes templates reduced result modeIds modes a b}
    (h : run fuel p shapes templates reduced = .success result)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hc : Constraint.mode a b ∈ reduced.modes) :
    Submode p.assumptions (a.subst modes.substitution.mode) (b.subst modes.substitution.mode) := by
  apply Submode.valid
  intro η hη
  obtain ⟨τ, hτ, hmodels⟩ := run_synthesized_models h hm hf η hη
  have he : (fun v => (modes.substitution.mode v).eval (some ∘ η)) = some ∘ τ := funext hτ
  simpa only [ModeSatisfies, ModExpr.Below, ModExpr.eval_subst, he] using hmodels _ hc

theorem run_synthesized_defined {fuel modeFuel p shapes templates reduced result modeIds modes m}
    (h : run fuel p shapes templates reduced = .success result)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hc : Constraint.defined m ∈ reduced.modes) :
    Entails p.assumptions (.defined (m.subst modes.substitution.mode)) := by
  intro η hη
  obtain ⟨τ, hτ, hmodels⟩ := run_synthesized_models h hm hf η hη
  have he : (fun v => (modes.substitution.mode v).eval (some ∘ η)) = some ∘ τ := funext hτ
  simpa only [ModeSatisfies, ModExpr.WellFormed, ModExpr.eval_subst, he] using hmodels _ hc

open ComparisonPropagation

def groupLabels (g : ComparisonGroups.Group) : List ModExpr :=
  ((g.assumptions ++ g.goals).flatMap fun (a, b) => [a.mode, b.mode]).dedup

def actionStep (fuel : Nat) (basis : ComparisonControls.Basis) (label : ModExpr)
    (actions : List (ModExpr × Action)) : RunResult (ForInStep (List (ModExpr × Action))) := do
  let lower ← ComparisonControls.low fuel basis label
  let upper ← ComparisonControls.high fuel basis label
  pure (.yield ((label, ⟨lower, upper⟩) :: actions))

def assumptionStep (basis : ComparisonControls.Basis) (action : ModExpr → Action)
    (pair : ComparisonGroups.Inequality) (theory : CNF) : RunResult (ForInStep CNF) := do
  let mut clauses := theory
  let a ← endpoint basis [] pair.1
  let b ← endpoint basis [] pair.2
  match a.leaf, b.leaf with
  | .fixed x, .fixed y =>
      clauses := meet clauses (implies ((action a.mode).apply x) ((action b.mode).apply y))
  | .flex i, _ => nomatch i
  | _, .flex i => nomatch i
  pure (.yield clauses)

/-- A trace of the actual successful group computation, including both bounded
CNF conversions and the exact residual obligation returned by propagation. -/
structure GroupTrace (fuel : Nat) (assumptions required : Bounds)
    (g : ComparisonGroups.Group) (output : Result) where
  first : TypeVar
  rest : List TypeVar
  heads : g.heads = first :: rest
  actions : List (ModExpr × Action)
  actions_eq : forIn (groupLabels g) []
    (actionStep fuel (groupBasis assumptions required g first rest)) = .success actions
  controls : CNF
  controls_eq : controlsTheory fuel (groupBasis assumptions required g first rest) = .success controls
  guards : CNF
  guards_eq : CompactCNF.toCNF fuel true
    (let count := (groupBasis assumptions required g first rest).types.length
     .or (.and (.imp (.atom count) (.const false))
       (.imp (.atom (count + 1)) (.const false)))
       (SymbolicCNF.substitute (fun i => .atom (count + 2 + i))
         (.and (boundsModeFormula assumptions) (boundsModeFormula required)))) = .success guards
  theory : CNF
  theory_eq : forIn g.assumptions (meet controls guards)
    (assumptionStep (groupBasis assumptions required g first rest)
      (fun label => (actions.lookup label).getD ⟨[[]], []⟩)) = .success theory
  bounds : List (Bound g.leaves.length)
  bounds_eq : g.goals.mapM (bound (groupBasis assumptions required g first rest) g.leaves) =
    .success bounds
  reduction : Reduction g.leaves.length
  reduction_eq : reduce (groupBasis assumptions required g first rest).types
    (compile (groupBasis assumptions required g first rest).types.length
      (fun label => (actions.lookup label).getD ⟨[[]], []⟩) theory bounds) = .success reduction
  types_eq : output.types = g.leaves.zip reduction.images.toList
  query_eq : output.query =
    let count := (groupBasis assumptions required g first rest).types.length
    formula (rename (· - (count + 2))
      (SymbolicCNF.abstract (fun i => count + 2 ≤ i) reduction.obligation))

theorem group_trace {fuel assumptions required g output}
    (h : group fuel assumptions required g = .success output) :
    Nonempty (GroupTrace fuel assumptions required g output) := by
  unfold group at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  cases h
  rename_i _ first rest hheads _ actions ha _ controls hc _ guards hg _ theory ht
    _ bounds hb _ reduction hr
  exact ⟨⟨first, rest, hheads, actions, ha, controls, hc, guards, hg,
    theory, ht, bounds, hb, reduction, hr, rfl, rfl⟩⟩

private theorem any_eval_true (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.any es).eval σ = true ↔ ∃ e ∈ es, e.eval σ = true := by
  induction es <;> simp_all [BoolExpr.any, BoolExpr.eval]

@[simp] theorem literalFormula_correct (l : Literal) (σ : Nat → Bool) :
    (literalFormula l).eval σ = true ↔ σ l.1 = l.2 := by
  rcases l with ⟨v, p⟩
  cases p <;> simp [literalFormula, BoolExpr.eval]

theorem formula_correct (cs : CNF) (σ : Nat → Bool) :
    (formula cs).eval σ = true ↔ CNFHolds σ cs := by
  have hc (c : Clause) : (BoolExpr.any (c.map literalFormula)).eval σ = true ↔ ClauseHolds σ c := by
    rw [any_eval_true]
    constructor
    · rintro ⟨e, he, hh⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      exact ⟨l.1, l.2, hl, (literalFormula_correct l σ).mp hh⟩
    · rintro ⟨v, p, hl, he⟩
      exact ⟨_, List.mem_map.mpr ⟨(v, p), hl, rfl⟩, (literalFormula_correct _ σ).mpr he⟩
  simp only [formula, all_eval_true, List.forall_mem_map, hc, CNFHolds]

/-- Validity of the returned scalar query reinstates every universally removed
head and selector coordinate, while fixing the shifted modality coordinates. -/
theorem abstract_query_sound {cs : CNF} {offset : Nat} {σ τ : Nat → Bool}
    (hq : (formula (rename (· - offset)
      (SymbolicCNF.abstract (fun i => offset ≤ i) cs))).eval σ = true)
    (htail : ∀ i, τ (offset + i) = σ i) : CNFHolds τ cs := by
  have hcnf := (rename_correct _ _ σ).mp ((formula_correct _ _).mp hq)
  apply (SymbolicCNF.abstract_correct _ _ _).mp hcnf τ
  intro v hv
  have hv : offset ≤ v := by simpa using hv
  simpa only [Nat.add_sub_of_le hv, Function.comp_apply] using htail (v - offset)

theorem GroupTrace.obligation {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) {σ τ : Nat → Bool}
    (hq : output.query.eval σ = true)
    (htail : ∀ i, τ ((groupBasis assumptions required g trace.first trace.rest).types.length + 2 + i) = σ i) :
    CNFHolds τ trace.reduction.obligation := by
  rw [trace.query_eq] at hq
  exact abstract_query_sound hq htail

private theorem action_loop_valid {fuel : Nat} {basis : ComparisonControls.Basis}
    {labels : List ModExpr} {initial actions : List (ModExpr × Action)}
    (h : forIn labels initial (actionStep fuel basis) = .success actions)
    (hinit : ∀ entry ∈ initial,
      ComparisonControls.low fuel basis entry.1 = .success entry.2.lower ∧
      ComparisonControls.high fuel basis entry.1 = .success entry.2.upper) :
    ∀ entry ∈ actions,
      ComparisonControls.low fuel basis entry.1 = .success entry.2.lower ∧
      ComparisonControls.high fuel basis entry.1 = .success entry.2.upper := by
  apply RunResult.forIn_preserves _ h hinit
  intro label _ before after hb hs
  unfold actionStep at hs
  simp only [bind, pure, RunResult.bind] at hs
  cases hl : ComparisonControls.low fuel basis label <;> simp only [hl] at hs <;> try contradiction
  next lower =>
    cases hu : ComparisonControls.high fuel basis label <;> simp only [hu] at hs <;> try contradiction
    next upper =>
      cases hs
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨hl, hu⟩
      · exact hb entry he

private theorem action_loop_domain {fuel : Nat} {basis : ComparisonControls.Basis}
    {labels : List ModExpr} {initial actions : List (ModExpr × Action)}
    (h : forIn labels initial (actionStep fuel basis) = .success actions) :
    actions.map Prod.fst = labels.reverse ++ initial.map Prod.fst := by
  induction labels generalizing initial with
  | nil => cases h; rfl
  | cons label labels ih =>
    simp only [List.forIn_cons, actionStep, bind, pure, RunResult.bind] at h
    cases hl : ComparisonControls.low fuel basis label <;> simp only [hl] at h <;> try contradiction
    next lower =>
      cases hu : ComparisonControls.high fuel basis label <;> simp only [hu] at h <;> try contradiction
      next upper =>
        simpa using ih h

theorem GroupTrace.action_compiled {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) {label : ModExpr}
    (hl : label ∈ groupLabels g) :
    let action := (trace.actions.lookup label).getD ⟨[[]], []⟩
    ComparisonControls.low fuel (groupBasis assumptions required g trace.first trace.rest) label =
      .success action.lower ∧
    ComparisonControls.high fuel (groupBasis assumptions required g trace.first trace.rest) label =
      .success action.upper := by
  have hm : label ∈ trace.actions.map Prod.fst := by
    rw [action_loop_domain trace.actions_eq]
    simpa using hl
  obtain ⟨entry, he, hlabel⟩ := List.mem_map.mp hm
  obtain ⟨action, ha⟩ := Option.isSome_iff_exists.mp
    ((List.lookup_isSome_iff (k := label)).mpr ⟨entry, he, by simp [hlabel]⟩)
  obtain ⟨left, right, hlist, _⟩ := List.lookup_eq_some_iff.mp ha
  have hmem : (label, action) ∈ trace.actions := by simp [hlist]
  simpa only [ha, Option.getD_some] using
    action_loop_valid trace.actions_eq (by simp) (label, action) hmem

def controlsStep (fuel : Nat) (basis : ComparisonControls.Basis)
    (pair : ComparisonControls.Coordinate × BoolExpr) (clauses : CNF) :
    RunResult (ForInStep CNF) := do
  let next ← CompactCNF.toCNF fuel true
    (.imp pair.2 (basis.theoryAt id id (basis.types.length + 2 + ·) pair.1))
  pure (.yield (meet clauses next))

private theorem controls_loop_correct {fuel : Nat} {basis : ComparisonControls.Basis}
    {pairs : List (ComparisonControls.Coordinate × BoolExpr)} {initial result : CNF}
    (h : forIn pairs initial (controlsStep fuel basis) = .success result) (σ : Nat → Bool) :
    CNFHolds σ result ↔ CNFHolds σ initial ∧ ∀ pair ∈ pairs,
      pair.2.eval σ = true →
        (basis.theoryAt id id (basis.types.length + 2 + ·) pair.1).eval σ = true := by
  induction pairs generalizing initial with
  | nil => cases h; simp
  | cons pair pairs ih =>
    simp only [List.forIn_cons, controlsStep, bind, pure, RunResult.bind] at h
    cases hn : CompactCNF.toCNF fuel true
      (.imp pair.2 (basis.theoryAt id id (basis.types.length + 2 + ·) pair.1)) <;>
        simp only [hn] at h <;> try contradiction
    next clauses =>
      rw [ih h, meet_correct, CompactCNF.toCNF_correct hn, BoolExpr.eval_imp_true]
      simp only [List.forall_mem_cons]
      tauto

theorem controlsTheory_correct {fuel basis result}
    (h : controlsTheory fuel basis = .success result) (σ : Nat → Bool) :
    CNFHolds σ result ↔ ∀ pair ∈ coordinateCases basis.types.length,
      pair.2.eval σ = true →
        (basis.theoryAt id id (basis.types.length + 2 + ·) pair.1).eval σ = true := by
  unfold controlsTheory at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  next clauses hc =>
    cases h
    have he := controls_loop_correct (basis := basis) (pairs := coordinateCases basis.types.length) hc σ
    simpa [CNFHolds] using he

def AssumptionHolds (basis : ComparisonControls.Basis) (action : ModExpr → Action)
    (pair : ComparisonGroups.Inequality) (σ : Nat → Bool) : Prop :=
  ∀ a b, endpoint basis [] pair.1 = .success a → endpoint basis [] pair.2 = .success b →
    a.Holds action σ (fun i => nomatch i) → b.Holds action σ (fun i => nomatch i)

private theorem assumptions_loop_correct {basis : ComparisonControls.Basis}
    {action : ModExpr → Action} {pairs : List ComparisonGroups.Inequality} {initial result : CNF}
    (h : forIn pairs initial (assumptionStep basis action) = .success result) (σ : Nat → Bool) :
    CNFHolds σ result ↔ CNFHolds σ initial ∧ ∀ pair ∈ pairs, AssumptionHolds basis action pair σ := by
  induction pairs generalizing initial with
  | nil => cases h; simp
  | cons pair pairs ih =>
    simp only [List.forIn_cons, assumptionStep, bind, pure, RunResult.bind] at h
    cases ha : endpoint basis [] pair.1 <;> simp only [ha] at h <;> try contradiction
    next a =>
      cases hb : endpoint basis [] pair.2 <;> simp only [hb] at h <;> try contradiction
      next b =>
        rcases a with ⟨al, am⟩
        rcases b with ⟨bl, bm⟩
        cases al with
        | flex i => exact Fin.elim0 i
        | fixed x =>
          cases bl with
          | flex i => exact Fin.elim0 i
          | fixed y =>
            have happly (a : Action) (cs : CNF) :
                CNFHolds σ (a.apply cs) ↔ a.Holds σ (CNFHolds σ cs) := by
              simp only [Action.apply, meet_correct, join_correct, Action.Holds]
            have hp : AssumptionHolds basis action pair σ ↔
                (CNFHolds σ ((action am).apply x) → CNFHolds σ ((action bm).apply y)) := by
              constructor
              · intro hp hx
                exact (happly _ _).mpr (hp _ _ ha hb ((happly _ _).mp hx))
              · intro hp a b hea heb hx
                have ea := RunResult.success.inj (ha.symm.trans hea)
                have eb := RunResult.success.inj (hb.symm.trans heb)
                subst a; subst b
                exact (happly _ _).mp (hp ((happly _ _).mpr hx))
            rw [ih h, meet_correct, implies_correct, List.forall_mem_cons, hp, and_assoc]

theorem GroupTrace.theory_correct {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) (σ : Nat → Bool) :
    CNFHolds σ trace.theory ↔ CNFHolds σ trace.controls ∧ CNFHolds σ trace.guards ∧
      ∀ pair ∈ g.assumptions, AssumptionHolds
        (groupBasis assumptions required g trace.first trace.rest)
        (fun label => (trace.actions.lookup label).getD ⟨[[]], []⟩) pair σ := by
  rw [assumptions_loop_correct trace.theory_eq σ, meet_correct, and_assoc]

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

private theorem mapM_forall₂ {α β : Type} {f : α → RunResult β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .success ys) :
    List.Forall₂ (fun x y => f x = .success y) xs ys := by
  induction xs generalizing ys with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hx : f x <;> simp only [hx] at h <;> try contradiction
    next y =>
      cases hxs : xs.mapM f <;> simp only [hxs] at h <;> try contradiction
      next rest =>
        cases h
        exact .cons hx (ih hxs)

theorem GroupTrace.goal_compiled {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) {pair : ComparisonGroups.Inequality}
    (hp : pair ∈ g.goals) :
    ∃ b ∈ trace.bounds, bound (groupBasis assumptions required g trace.first trace.rest) g.leaves pair =
      .success b :=
  forall₂_mem_left (mapM_forall₂ trace.bounds_eq) hp

theorem GroupTrace.goal_holds {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) {σ τ : Nat → Bool}
    (hq : output.query.eval σ = true)
    (htail : ∀ i, τ ((groupBasis assumptions required g trace.first trace.rest).types.length + 2 + i) = σ i)
    (ht : CNFHolds τ trace.theory) {b : Bound g.leaves.length} (hb : b ∈ trace.bounds) :
    b.left.Holds (fun label => (trace.actions.lookup label).getD ⟨[[]], []⟩) τ
      (fun v => CNFHolds τ trace.reduction.store[v]) →
    b.right.Holds (fun label => (trace.actions.lookup label).getD ⟨[[]], []⟩) τ
      (fun v => CNFHolds τ trace.reduction.store[v]) :=
  reduce_compile_pointwise trace.reduction_eq (trace.obligation hq htail) b hb ht

end ModalityInference.ComparisonElimination
