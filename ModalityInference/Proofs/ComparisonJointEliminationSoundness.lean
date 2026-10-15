import ModalityInference.Proofs.ComparisonJointElimination
import ModalityInference.Proofs.ComparisonJointGroupAtoms
import ModalityInference.Proofs.ComparisonJointBatchOutput
import ModalityInference.Proofs.ComparisonJointEliminationDomains
import ModalityInference.Proofs.ComparisonCollectedDomains

/-! The finite result of shared elimination satisfies every original reduced
opaque inequality and the retained scalar obligations under declared guards. -/
namespace ModalityInference.ComparisonJointElimination

open ComparisonJointBatchReification ComparisonJointAssemblyReification
  ComparisonJointGroupAtoms ComparisonControls ComparisonTupleReification ComparisonPropagation

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

private theorem prepare_group_projection {fuel : Nat} {assumptions required : Bounds}
    {groups : List ComparisonGroups.Group} {compiled : List Compiled}
    (h : prepare fuel assumptions required groups = .success compiled) :
    compiled.map Compiled.group = groups := by
  induction groups generalizing compiled with
  | nil => cases h; rfl
  | cons group groups ih =>
    simp only [prepare, List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hg : ComparisonJointGroup.prepare fuel assumptions required group <;>
      simp only [hg] at h <;> try contradiction
    next input =>
      change (do
        let rest ← prepare fuel assumptions required groups
        pure (Compiled.mk group input :: rest)) = .success compiled at h
      cases hs : prepare fuel assumptions required groups <;>
        simp only [hs, bind, RunResult.bind, pure] at h <;> try contradiction
      next rest => cases h; exact congrArg (group :: ·) (ih hs)

private theorem option_mapM_input {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rest, hr, rfl⟩ := h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨y, hy⟩
    · exact ih hr z hz

theorem Trace.compiled_groups {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output) :
    t.compiled.map Compiled.group = t.groups := prepare_group_projection t.preparation

theorem Trace.compiled_input {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (i : Fin t.compiled.length) :
    t.compiled[i].group ∈ t.groups ∧
      ComparisonJointGroup.prepare fuel p.assumptions reduced.modes t.compiled[i].group =
        .success t.compiled[i].input :=
  prepare_mem t.preparation _ (List.getElem_mem i.isLt)

theorem Trace.basis_exists {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (i : Fin t.compiled.length) : ∃ b, basis allowed t.compiled[i].group = some b := by
  obtain ⟨pieces, hp, _⟩ := typeImages_spec (assemble_spec t.assembly).2
  obtain ⟨images, hi⟩ := option_mapM_input hp i (List.mem_finRange i)
  obtain ⟨b, hb, _⟩ := groupImages_spec hi
  exact ⟨b, hb⟩

theorem Trace.fixed_type {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    {v : TypeVar} (hv : ∀ leaf ∈ templates.leaves, v ≠ .flex leaf.name) :
    output.substitution.type v = .var v := by
  apply assemble_type_fixed t.assembly
  intro n hn
  obtain ⟨c, hc, hn⟩ := List.mem_flatMap.mp hn
  have hg := (prepare_mem t.preparation c hc).1
  obtain ⟨leaf, hl, he, _⟩ := ComparisonGroups.collect_leaf_origin t.collection c.group hg n hn
  exact he ▸ hv leaf hl

theorem Trace.head_shape {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hfixed : ∀ η, ComparisonShape.Models p.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (i : Fin t.compiled.length) :
    ∀ v ∈ t.compiled[i].group.heads,
      ComparisonShape.Equivalent p.assumptions (.var v) (.var t.compiled[i].group.shapeClass) := by
  intro v hv η hη
  obtain ⟨hm, _, hc⟩ := ComparisonGroups.collect_head_origin t.collection _ (t.compiled_input i).1 v hv
  have he := ComparisonGroups.shapeClass_fixed (fun leaf hl => hfresh leaf hl v hm) hc
  simpa only [he, ComparisonShape.subst] using (hfixed η hη v).symm

theorem Trace.wellShaped {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hfixed : ∀ η, ComparisonShape.Models p.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name) :
    output.substitution.WellShaped p.assumptions :=
  assemble_wellShaped t.batch_eq (fun i => (t.compiled_input i).2) t.assembly
    (t.head_shape hfixed hfresh)

theorem Trace.wellFormed {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output) :
    output.substitution.WellFormedUnder p.assumptions :=
  assemble_wellFormed t.batch_eq (fun i => (t.compiled_input i).2) t.assembly p.assumptions

theorem Trace.leaves_nodup {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b) :
    (t.compiled.flatMap (fun c => c.group.leaves)).Nodup := by
  have h := ComparisonGroups.collect_all_leaves_nodup t.collection hn hname
  rw [← t.compiled_groups] at h
  simpa only [List.flatMap_map, Function.comp_def] using h

theorem Trace.groups_sound {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hfixedShape : ∀ η, ComparisonShape.Models p.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b)
    (hfixed : ∀ v ∈ p.assumptions.modVars,
      v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ SchemeModeSynthesis.atoms modeIds)
    (hrequired : ∀ v ∈ reduced.modes.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (hlabels : ∀ g ∈ t.groups, ∀ m ∈ ComparisonElimination.groupLabels g,
      ∀ v ∈ m.vars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hscalar : ComparisonReduction.ScalarModes reduced) :
    ∀ g ∈ t.groups, ∀ pair ∈ g.goals,
      AlgebraSubtype p.assumptions (pair.1.interpret output.substitution)
        (pair.2.interpret output.substitution) := by
  have hs := t.wellShaped hfixedShape hfresh
  have hm := t.scalar_entails hscalar hfixed hrequired
  have hfmode : ∀ v ∈ p.assumptions.modVars, output.substitution.mode v = .var v := by
    intro v hv
    apply assemble_mode_fixed t.assembly
    intro n hn he
    subst v
    exact (hfixed _ hv).2 0 (by decide) ((SchemeModeSynthesis.mem_atoms_flex (by decide)).mpr hn)
  have hftype : ∀ v ∈ p.assumptions.typeVars, output.substitution.type v = .var v := by
    intro v hv
    apply t.fixed_type
    intro leaf hl
    exact hfresh leaf hl v (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ ((Bounds.mem_typeVariables _ _).mpr hv))))
  have hlabel := collected_labels_defined t.collection hfmode hd hguards hm
  have hassumptions := collected_assumptions t.collection hftype hfmode hlabel hs
  intro g hg
  have hg' : g ∈ t.compiled.map Compiled.group := t.compiled_groups.symm ▸ hg
  obtain ⟨compiled, hcompiled, rfl⟩ := List.mem_map.mp hg'
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hcompiled
  let idx : Fin t.compiled.length := ⟨i, hi⟩
  change t.compiled[idx] = compiled at he
  subst compiled
  obtain ⟨b, hb⟩ := t.basis_exists idx
  have hbasis := basis_spec hb
  have hinput := (t.compiled_input idx).2
  let world := fun η k => (t.batch.solution.modes.substitute k).eval
    (projectWorld allowed (encodeModes η))
  let values := fun heads η => (localResult t.compiled t.batch idx minimumModes).state
    t.compiled[idx].group.heads.length (basisValue b.heads heads)
      (projectWorld allowed (encodeModes η))
  have hleaf (j : Fin t.compiled[idx].group.leaves.length) :
      ∃ image : ComparisonControls.Generated b,
        output.substitution.type (.flex (t.compiled[idx].group.leaves.get j)) = image.term ∧ Total image ∧
        ∀ heads η c, observe c heads η image = values heads η (ComparisonJointGroup.state c j) := by
    obtain ⟨other, ho, image, hlookup, ht, he⟩ := assemble_leaf t.batch_eq t.assembly
      (t.leaves_nodup hn hname) idx hinput j
    have heq : other = b := Option.some.inj (ho.symm.trans hb)
    subst other
    exact ⟨image, hlookup, ht, he⟩
  choose images hlookup htotal hobs using hleaf
  have hheadFresh {v : TypeVar} (hv : v ∈ t.compiled[idx].group.heads) :
      ∀ leaf ∈ templates.leaves, v ≠ .flex leaf.name := by
    have ho := (ComparisonGroups.collect_head_origin t.collection _ hg v hv).1
    exact fun leaf hl => hfresh leaf hl v ho
  apply ComparisonJointGroupAtoms.group_sound (assumptions := p.assumptions)
    (required := reduced.modes) (shape := .var t.compiled[idx].group.shapeClass)
    images world values hbasis.1
    (ComparisonJointGroup.prepare_covered hinput)
  · intro v hv n hn
    obtain ⟨leaf, hl, he, _⟩ := ComparisonGroups.collect_leaf_origin t.collection _ hg n hn
    exact he ▸ hheadFresh hv leaf hl
  · intro a ha
    rw [hbasis.1] at ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact ⟨trivial, by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels],
      t.head_shape hfixedShape hfresh idx v hv⟩
  · exact fun v hv => t.fixed_type (hheadFresh hv)
  · exact hlookup
  · exact htotal
  · exact fun j c heads η => hobs j heads η c
  · intro m hm v hv
    rw [hbasis.2]
    exact projected_assemble_supported (assemble_spec t.assembly).1 (hlabels _ hg m hm) v hv
  · exact hlabel _ hg
  · exact fun m hm η => projected_assemble_expression (assemble_spec t.assembly).1
      (hlabels _ hg m hm) η
  · exact hassumptions _ hg
  · intro heads η
    have hstrategy : (localResult t.compiled t.batch idx minimumModes).strategy
        (projectWorld allowed (encodeModes η)) = world η := by
      funext k
      simp only [ComparisonJointAssembly.Result.strategy, local_modes, world]
    have hgroup := local_group_sound t.batch_eq idx hinput (basis_nonempty hb)
      (basisValue b.heads heads) (projectWorld allowed (encodeModes η))
    rw [hstrategy] at hgroup
    exact hgroup
  · intro η hη
    exact ⟨(projected_fixed_models hfixed η).mpr hη,
      (projected_assemble_models (assemble_spec t.assembly).1 hrequired η).mp
        (t.scalar_guards hfixed hrequired η hη)⟩

/-- Successful shared elimination returns a defined, well-shaped action that
satisfies the original opaque inequalities and all retained scalar guards. -/
theorem Trace.sound {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    (hfixedShape : ∀ η, ComparisonShape.Models p.assumptions η →
      ∀ v, (shapes.fixedShapes v).subst η = η v)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b)
    (hfixed : ∀ v ∈ p.assumptions.modVars,
      v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ SchemeModeSynthesis.atoms modeIds)
    (hrequired : ∀ v ∈ reduced.modes.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (hlabels : ∀ g ∈ t.groups, ∀ m ∈ ComparisonElimination.groupLabels g,
      ∀ v ∈ m.vars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hscalar : ComparisonReduction.ScalarModes reduced) :
    output.substitution.WellShaped p.assumptions ∧
      output.substitution.WellFormedUnder p.assumptions ∧
      AlgebraEntailsAll p.assumptions (output.substitution.bounds reduced.modes) ∧
      ∀ pair ∈ reduced.inequalities,
        ComparisonReduction.PairHolds p.assumptions output.substitution pair := by
  have hs := t.wellShaped hfixedShape hfresh
  have hm := t.scalar_entails hscalar hfixed hrequired
  refine ⟨hs, t.wellFormed, hm, ?_⟩
  exact ComparisonGroups.collect_reconstruct hs t.collection hguards hm
    (t.groups_sound hfixedShape hfresh hn hname hfixed hrequired hlabels hd hguards hscalar)

end ModalityInference.ComparisonJointElimination
