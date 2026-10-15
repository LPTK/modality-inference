import ModalityInference.Proofs.ComparisonGroupExtraction
import ModalityInference.Proofs.ComparisonWitnessShapes
import ModalityInference.Proofs.ComparisonGroupSoundness
import ModalityInference.Proofs.ComparisonEliminationLookup

/-! Assembly of opaque group witnesses and their synthesized scalar action. -/
namespace ModalityInference

private theorem sub_not_wellFormedBounds (a b t : Ty) :
    Constraint.sub a b ∉ t.wellFormedBounds := by
  intro h
  obtain ⟨m, hm⟩ := t.wellFormedBounds_is_defined _ h
  contradiction

theorem Bounds.typeBoundsDefined_append_assumptions (ambient bounds : Bounds)
    (ha : ambient.TypeBoundsDefined) : (ambient ++ bounds.assumptions).TypeBoundsDefined := by
  intro a b hab
  rcases List.mem_append.mp hab with hab | hab
  · have hd := ha a b hab
    exact ⟨fun η hη => hd.1 η (fun c hc => hη c (List.mem_append_left _ hc)),
      fun η hη => hd.2 η (fun c hc => hη c (List.mem_append_left _ hc))⟩
  · obtain ⟨c, hc, hab⟩ := List.mem_flatMap.mp hab
    have he := bounds.assumptions_entails_append ambient c hc
    cases c <;> simp only [Constraint.assumptions, List.mem_append, List.mem_cons,
      List.not_mem_nil, sub_not_wellFormedBounds, or_false] at hab
    case sub x y => cases hab; exact ⟨he.2.1, he.2.2⟩
    case equiv x y =>
      rcases hab with hab | hab <;> cases hab
      · exact ⟨he.2.2.1, he.2.2.2⟩
      · exact ⟨he.2.2.2, he.2.2.1⟩
    case equal v t =>
      rcases hab with hab | hab <;> cases hab
      · exact ⟨by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels], he.2.2⟩
      · exact ⟨he.2.2, by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩
    all_goals contradiction

theorem Bounds.assumptions_typeBoundsDefined (bounds : Bounds) : bounds.assumptions.TypeBoundsDefined :=
  Bounds.typeBoundsDefined_append_assumptions [] bounds (by simp [Bounds.TypeBoundsDefined])

theorem SchemePreparation.prepared_typeBoundsDefined (source target : Scheme) :
    (SchemePreparation.prepare [] source target).assumptions.TypeBoundsDefined :=
  Bounds.assumptions_typeBoundsDefined _

namespace ComparisonElimination

def imageAction (images : List (Nat × CompareTy)) (modes : Substitution) : CompareSubstitution :=
  { types := images.map fun (name, t) => (name, t.subst CompareTy.var modes.mode)
    modes := modes.modes }

@[simp] theorem imageAction_mode (images : List (Nat × CompareTy)) (modes : Substitution) :
    (imageAction images modes).mode = modes.mode := rfl

theorem imageAction_type (images : List (Nat × CompareTy)) (modes : Substitution) (v : TypeVar) :
    (imageAction images modes).type v =
      (({ types := images } : CompareSubstitution).type v).subst CompareTy.var modes.mode := by
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [imageAction, CompareSubstitution.type, lookup_map_values]
    cases images.lookup n <;> rfl

theorem imageAction_ty (images : List (Nat × CompareTy)) (modes : Substitution) (t : Ty) :
    (imageAction images modes).ty t =
      (({ types := images } : CompareSubstitution).ty t).subst CompareTy.var modes.mode := by
  have hm : ({ types := images } : CompareSubstitution).mode = ModExpr.var := by
    funext v
    cases v <;> rfl
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    imageAction_type, ModExpr.subst_id]

theorem imageAction_wellShaped {Δ : Bounds} {images : List (Nat × CompareTy)}
    (h : ∀ entry ∈ images, entry.2.WellShaped Δ) (modes : Substitution) :
    (imageAction images modes).WellShaped Δ := by
  intro entry he
  obtain ⟨⟨name, t⟩, ht, rfl⟩ := List.mem_map.mp he
  exact (CompareTy.wellShaped_subst_modes_iff t modes.mode).mpr (h (name, t) ht)

def Result.action (result : Result) (modes : Substitution) : CompareSubstitution :=
  imageAction result.types modes

@[simp] theorem Result.action_mode (result : Result) (modes : Substitution) :
    (result.action modes).mode = modes.mode := rfl

theorem Result.action_type (result : Result) (modes : Substitution) (v : TypeVar) :
    (result.action modes).type v =
      (({ types := result.types } : CompareSubstitution).type v).subst CompareTy.var modes.mode :=
  imageAction_type result.types modes v

theorem Result.action_ty (result : Result) (modes : Substitution) (t : Ty) :
    (result.action modes).ty t =
      (({ types := result.types } : CompareSubstitution).ty t).subst CompareTy.var modes.mode :=
  imageAction_ty result.types modes t

theorem Result.action_wellShaped {Δ : Bounds} {result : Result}
    (h : ∀ entry ∈ result.types, entry.2.WellShaped Δ) (modes : Substitution) :
    (result.action modes).WellShaped Δ := imageAction_wellShaped h modes

theorem run_fixed_type {fuel p shapes templates reduced result}
    (h : run fuel p shapes templates reduced = .success result) {v : TypeVar}
    (hf : ∀ leaf ∈ templates.leaves, v ≠ .flex leaf.name) :
    ({ types := result.types } : CompareSubstitution).type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    have hn : result.types.lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      obtain ⟨leaf, hl, hn⟩ := run_type_domain h entry he
      apply bne_iff_ne.mpr
      intro he
      exact hf leaf hl (congrArg TypeVar.flex (he.trans hn.symm))
    simp only [CompareSubstitution.type, hn, Option.getD_none]

def actualModes (modes : Substitution) (η : ModVar → Mode) (v : ModVar) : Mode :=
  ((modes.mode v).eval (some ∘ η)).getD Mode.identity

theorem synthesized_actual {fuel modeIds formula modes}
    (h : SchemeModeSynthesis.run fuel modeIds formula = .success modes) (η : ModVar → Mode)
    (v : ModVar) :
    (modes.substitution.mode v).eval (some ∘ η) = some (actualModes modes.substitution η v) := by
  obtain ⟨τ, hτ, _⟩ := SchemeModeSynthesis.run_actual h η
  simp only [actualModes, hτ v, Option.getD_some]

theorem synthesized_query {fuel modeIds formula modes}
    (h : SchemeModeSynthesis.run fuel modeIds formula = .success modes) (η : ModVar → Mode) :
    formula.eval (encodeModes (actualModes modes.substitution η)) = true :=
  SchemeModeSynthesis.run_actual_valid h (synthesized_actual h η)

theorem synthesized_original_models {fuel modeIds formula modes Δ}
    (h : SchemeModeSynthesis.run fuel modeIds formula = .success modes)
    (hf : ∀ v ∈ Δ.modVars, modes.substitution.mode v = .var v)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    ModeModels Δ (actualModes modes.substitution η) := by
  apply (ModeModels.congr Δ ?_).mpr hη
  intro v hv
  exact Option.some.inj ((synthesized_actual h η v).symm.trans
    (by rw [hf v hv]; rfl))

theorem synthesized_guards {fuel modeFuel p shapes templates reduced result modeIds modes}
    (h : run fuel p shapes templates reduced = .success result)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    {η : ModVar → Mode} (hη : ModeModels p.assumptions η) :
    ModeModels p.assumptions (actualModes modes.substitution η) ∧
      ModeModels reduced.modes (actualModes modes.substitution η) := by
  have hΔ := synthesized_original_models hm hf hη
  refine ⟨hΔ, ?_⟩
  simpa only [projectedModes_encodeModes] using
    run_mode_models h (synthesized_query hm η)
      (by simpa only [projectedModes_encodeModes] using hΔ)

theorem synthesized_label_defined {Δ : Bounds} {m : ModExpr} {modes : Substitution}
    (h : ∀ η, ModeModels Δ η → m.WellFormed (actualModes modes η))
    (ht : ∀ η v, (modes.mode v).eval (some ∘ η) = some (actualModes modes η v)) :
    Entails Δ (.defined (m.subst modes.mode)) := by
  intro η hη
  have he : (fun v => (modes.mode v).eval (some ∘ η)) = some ∘ actualModes modes η := funext (ht η)
  simpa only [ModExpr.WellFormed, ModExpr.eval_subst, he] using h η hη

theorem run_group_labels_defined {fuel modeFuel p shapes templates reduced result modeIds modes groups}
    (h : run fuel p shapes templates reduced = .success result)
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced) :
    ∀ g ∈ groups, ∀ m ∈ groupLabels g,
      Entails p.assumptions (.defined (m.subst modes.substitution.mode)) := by
  intro g hg m hmemb
  apply synthesized_label_defined ?_ (synthesized_actual hm)
  intro η hη
  have hmodels := synthesized_guards h hm hf hη
  obtain ⟨pair, hp, hmemb⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hmemb)
  rcases List.mem_append.mp hp with hp | hp
  · have hlabels := ComparisonGroups.collect_assumption_modes hd hc g hg pair hp
    rcases List.mem_cons.mp hmemb with rfl | hmemb
    · exact hlabels.1 _ hmodels.1
    · obtain rfl := List.mem_singleton.mp hmemb
      exact hlabels.2 _ hmodels.1
  · have hlabels := ComparisonGroups.collect_goal_guards hc hguards g hg pair hp
    rcases List.mem_cons.mp hmemb with rfl | hmemb
    · exact hmodels.2 (.defined pair.1.mode) hlabels.1
    · obtain rfl := List.mem_singleton.mp hmemb
      exact hmodels.2 (.defined pair.2.mode) hlabels.2

theorem run_group_assumptions {fuel modeFuel p shapes templates reduced result modeIds modes groups}
    (h : run fuel p shapes templates reduced = .success result)
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (action : CompareSubstitution)
    (hmode : action.mode = modes.substitution.mode)
    (ht : ∀ v ∈ p.assumptions.typeVars, action.type v = .var v)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hshape : action.WellShaped p.assumptions) :
    ∀ g ∈ groups, ∀ pair ∈ g.assumptions,
      AlgebraSubtype p.assumptions (pair.1.interpret action) (pair.2.interpret action) := by
  intro g hg pair hp
  obtain ⟨left, right, hbound, hi⟩ := ComparisonGroups.collect_assumption_origin hc g hg pair hp
  apply (ComparisonGroups.inequality_algebra_iff hshape hi ?_ ?_).mp
    (CompareSubstitution.declared_subtype ht (by simpa only [hmode] using hf) hbound)
  all_goals rw [hmode]
  all_goals apply run_group_labels_defined h hc hm hf hd hguards g hg
  all_goals
    exact List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨pair, List.mem_append_left _ hp, by simp⟩)

theorem run_output_query {fuel p shapes templates reduced result groups g output σ}
    (h : run fuel p shapes templates reduced = .success result)
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hg : g ∈ groups) (ho : group fuel p.assumptions reduced.modes g = .success output)
    (hq : result.query.eval σ = true) : output.query.eval σ = true := by
  obtain ⟨otherGroups, hcollect, houtputs⟩ := run_group_queries h hq
  have he := RunResult.success.inj (hcollect.symm.trans hc)
  subst otherGroups
  obtain ⟨other, hother, hquery, _⟩ := houtputs g hg
  have he := RunResult.success.inj (hother.symm.trans ho)
  exact he ▸ hquery

/-- The group witnesses may be extended on other names, provided their opaque
leaf images and fixed heads are preserved. This admits the simultaneously
reconstructed partial intervals before applying the synthesized modalities. -/
theorem run_algebra_sound_images {fuel modeFuel p shapes templates reduced result modeIds modes}
    (h : run fuel p shapes templates reduced = .success result)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hshape : ∀ a b, ComparisonShape.Equivalent p.assumptions a b ↔
      a.subst shapes.fixedShapes = b.subst shapes.fixedShapes)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b)
    (hmode : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (images : List (Nat × CompareTy))
    (himages : ∀ leaf ∈ templates.leaves,
      ({ types := images } : CompareSubstitution).type (.flex leaf.name) =
        ({ types := result.types } : CompareSubstitution).type (.flex leaf.name))
    (hfixed : ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
      p.sourceType.typeVariables ++ p.sourceBounds.typeVariables,
      ComparisonShapeSolver.sourceAllowed p v = false →
        ({ types := images } : CompareSubstitution).type v = .var v)
    (hassumptions : ∀ v ∈ p.assumptions.typeVars,
      ({ types := images } : CompareSubstitution).type v = .var v)
    (hwell : ∀ entry ∈ images, entry.2.WellShaped p.assumptions) :
    ∀ goal ∈ reduced.inequalities,
      ComparisonReduction.PairHolds p.assumptions (imageAction images modes.substitution) goal := by
  let action := imageAction images modes.substitution
  have haction : action.WellShaped p.assumptions := imageAction_wellShaped hwell _
  have hafixed : ∀ v ∈ p.assumptions.typeVars, action.type v = .var v := by
    intro v hv
    rw [imageAction_type, hassumptions v hv]
    rfl
  obtain ⟨groups, hc, houtputs⟩ := run_group_queries h
    (synthesized_query hm (fun _ => Mode.identity))
  have hgroup : ∀ g ∈ groups, ∀ pair ∈ g.goals,
      AlgebraSubtype p.assumptions (pair.1.interpret action) (pair.2.interpret action) := by
    intro g hg
    obtain ⟨output, ho, _, _⟩ := houtputs g hg
    obtain ⟨trace⟩ := group_trace ho
    have hcommon := ComparisonGroups.collect_heads_compatible hshape hc hfresh g hg
    have hs := trace.sound (Δ := p.assumptions) (shape := .var trace.first)
      ({ types := images } : CompareSubstitution).type modes.substitution.mode
      (actualModes modes.substitution) (synthesized_actual hm) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [instantiatedAtom, ComparisonGroups.Atom.interpret, action,
        imageAction_type, imageAction_mode] using hs
    · intro v hv
      obtain ⟨hv, hsource, _⟩ := ComparisonGroups.collect_head_origin hc g hg v hv
      exact hfixed v hv hsource
    · intro i
      obtain ⟨leaf, hl, he, _⟩ := ComparisonGroups.collect_leaf_origin hc g hg _ (List.getElem_mem i.isLt)
      change leaf.name = g.leaves[i] at he
      rw [← he, himages leaf hl]
      simp only [CompareSubstitution.type, he, run_group_image h hc hn hname hg trace ho i,
        Option.getD_some]
    · intro v hv
      exact ⟨trivial, by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels],
        hcommon v hv trace.first (trace.heads ▸ List.mem_cons_self)⟩
    · exact run_group_labels_defined h hc hm hmode hd hguards g hg
    · intro η
      exact run_output_query h hc hg ho (synthesized_query hm η)
    · exact fun η hη => synthesized_guards h hm hmode hη
    · simpa only [instantiatedAtom, ComparisonGroups.Atom.interpret, action,
        imageAction_type, imageAction_mode] using
        run_group_assumptions h hc hm action rfl hafixed hmode hd hguards haction g hg
  intro goal hgoal
  obtain ⟨g, hg, pair, hp, hi⟩ := ComparisonGroups.collect_goal_coverage hc goal hgoal
  obtain ⟨hl, hr⟩ := ComparisonGroups.collect_goal_guards hc hguards g hg pair hp
  exact (ComparisonGroups.inequality_algebra_iff haction hi
    (run_synthesized_defined h hm hmode hl) (run_synthesized_defined h hm hmode hr)).mpr
    (hgroup g hg pair hp)

theorem run_algebra_sound {fuel modeFuel p shapes templates reduced result modeIds modes}
    (h : run fuel p shapes templates reduced = .success result)
    (hm : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hshape : ∀ a b, ComparisonShape.Equivalent p.assumptions a b ↔
      a.subst shapes.fixedShapes = b.subst shapes.fixedShapes)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b)
    (hmode : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced) :
    ∀ goal ∈ reduced.inequalities,
      ComparisonReduction.PairHolds p.assumptions (result.action modes.substitution) goal := by
  apply run_algebra_sound_images h hm hshape hfresh hn hname hmode hd hguards result.types
  · exact fun _ _ => rfl
  · intro v hv _
    exact run_fixed_type h (fun leaf hl => hfresh leaf hl v hv)
  · intro v hv
    apply run_fixed_type h
    intro leaf hl
    apply hfresh leaf hl v
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      ((Bounds.mem_typeVariables _ _).mpr hv)))
  · exact run_wellShaped hshape h hfresh

end ComparisonElimination
end ModalityInference
