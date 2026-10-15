import ModalityInference.Proofs.ComparisonWitnessProperties
import ModalityInference.Proofs.Projection

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

end ModalityInference.ComparisonElimination
