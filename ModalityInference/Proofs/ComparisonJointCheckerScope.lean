import ModalityInference.ComparisonJointChecker
import ModalityInference.Proofs.ComparisonDefinedSetup
import ModalityInference.Proofs.ComparisonFixedModeScope
import ModalityInference.Proofs.ComparisonReductionSupport
import ModalityInference.Proofs.ComparisonEliminationSupport
import ModalityInference.Proofs.ComparisonReductionClosure

/-! The ordinary guarded comparison pipeline preserves exact scalar-name
provenance from preparation through templates, reduction, and collected groups.
Original permitted names are fixed; all other names are allocated coordinates. -/
namespace ModalityInference.ComparisonJointChecker

open ComparisonChecker SchemePreparation ComparisonFixedModeWitness

def originalModes (p : Prepared) : Finset ModVar :=
  ((p.assumptions.modVars ∪ p.sourceBounds.modVars) ∪ p.sourceType.modVars) ∪ p.targetType.modVars

theorem allowedModes_spec (p : Prepared) (v : ModVar) :
    v ∈ allowedModes p ↔ v ∈ originalModes p ∧ v.index < p.firstMode := by
  simp [allowedModes, originalModes, Bounds.mem_modeVariables, TypeExpr.mem_modeVariables]
  tauto

def CoveredMode (s : Setup) (v : ModVar) : Prop :=
  v ∈ allowedModes s.original ∨ ∃n∈s.modeIds, v = .flex n

theorem assumptions_allowed (ambient : Bounds) (source target : Scheme) {v : ModVar}
    (hv : v ∈ (SchemePreparation.prepare ambient source target).assumptions.modVars) :
    v ∈ allowedModes (SchemePreparation.prepare ambient source target) := by
  apply (allowedModes_spec _ _).mpr
  exact ⟨by simp [originalModes, hv], ((Bounds.bounded_iff _ _ _).mp
    (prepare_assumptions_bounded_first ambient source target)).2 v hv⟩

theorem target_allowed (ambient : Bounds) (source target : Scheme) {v : ModVar}
    (hv : v ∈ (SchemePreparation.prepare ambient source target).targetType.modVars) :
    v ∈ allowedModes (SchemePreparation.prepare ambient source target) := by
  apply (allowedModes_spec _ _).mpr
  exact ⟨by simp [originalModes, hv], ((TypeExpr.bounded_iff _ _ _).mp
    (prepare_targetType_bounded_first ambient source target)).2 v hv⟩

theorem modeIds_lower {s : Setup} {n : Nat} (hn : n ∈ s.modeIds) : s.original.firstMode ≤ n :=
  (List.mem_range'_1.mp (List.mem_filter.mp hn).1).1

theorem allowed_atoms_fixed {s : Setup} {v : ModVar} (hv : v ∈ allowedModes s.original)
    {axis : Nat} (ha : axis < 3) : v.atomIndex axis ∉ SchemeModeSynthesis.atoms s.modeIds := by
  cases v with
  | rigid n => exact SchemeModeSynthesis.not_mem_atoms_rigid ha
  | flex n =>
    rw [SchemeModeSynthesis.mem_atoms_flex ha]
    intro hn
    have hl := (allowedModes_spec _ _).mp hv |>.2
    have hr := modeIds_lower hn
    simp only [ModVar.index] at hl
    omega

theorem source_covered {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (shapes : ComparisonShapeSolver.Solved) (known : List ModExpr) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ∀v∈inputModes s.original.sourceBounds s.original.sourceType, CoveredMode s v := by
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, shapes, known, false⟩
  have hg : BinderGuards p := prepare_binderGuards [] source target ht hm
  have hn : p.nextMode ≤ s.templates.nextMode := by
    rw [s.templates_of_binderGuards rfl hg rfl]
    change p.nextMode ≤ (ComparisonSkeleton.allocate p shapes _ _ _).nextMode
    rw [(ComparisonSkeleton.allocate_next _ _ _).2]
    change p.nextMode ≤ p.nextMode + _
    omega
  change ∀v∈inputModes s.original.sourceBounds s.original.sourceType, CoveredMode s v
  intro v hv
  have hv' : v ∈ p.sourceBounds.modVars ∪ p.sourceType.modVars := hv
  have hb : v.index < p.nextMode := by
    rcases Finset.mem_union.mp hv' with hv' | hv'
    · exact ((Bounds.bounded_iff _ _ _).mp
        (prepare_sourceBounds_bounded [] source.requireDefinedInstances target)).2 v hv'
    · exact ((TypeExpr.bounded_iff _ _ _).mp
        (prepare_sourceType_bounded [] source.requireDefinedInstances target)).2 v hv'
  by_cases hl : v.index < p.firstMode
  · apply Or.inl
    apply (allowedModes_spec _ _).mpr
    exact ⟨by simp only [originalModes, Finset.mem_union] at *; tauto, hl⟩
  · cases v with
    | rigid n =>
      exact False.elim (hl (prepared_rigidScoped [] source.requireDefinedInstances target (.rigid n) hv))
    | flex n =>
      refine Or.inr ⟨n, ?_, rfl⟩
      rw [s.modeIds_of_binderGuards rfl hg]
      apply List.mem_range'_1.mpr
      change p.firstMode ≤ n ∧ n < p.firstMode + (s.templates.nextMode - p.firstMode)
      simp only [ModVar.index] at hl hb
      omega

theorem prepared_template_covered {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (shapes : ComparisonShapeSolver.Solved) (known : List ModExpr) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ∀v∈inputModes (s.templates.substitution.bounds s.work.sourceBounds)
      (s.templates.substitution.ty s.work.sourceType), CoveredMode s v := by
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, shapes, known, false⟩
  let templates := ComparisonSkeleton.prepare p shapes
  have hg : BinderGuards p := prepare_binderGuards [] source target ht hm
  have htemplates : s.templates = templates := s.templates_of_binderGuards rfl hg rfl
  change ∀v∈inputModes (s.templates.substitution.bounds s.work.sourceBounds)
    (s.templates.substitution.ty s.work.sourceType), CoveredMode s v
  rw [s.work_of_binderGuards rfl hg, htemplates]
  have hfirst : p.firstMode ≤ p.nextMode := Nat.le_add_right _ _
  have himages : ∀entry∈templates.substitution.types, ∀v∈entry.2.modVars, CoveredMode s v := by
    intro entry he v hv
    obtain ⟨n, rfl, hn⟩ := ComparisonSkeleton.allocate_modeSupport
      (Q := fun v => ∃n, v = .flex n ∧ p.nextMode ≤ n)
      p shapes _ _ _ (fun n hn => ⟨n, rfl, hn⟩) entry he v hv
    have hb := ComparisonSkeleton.allocate_modeBound p shapes _ _ _ entry he (.flex n) hv
    refine Or.inr ⟨n, ?_, rfl⟩
    rw [s.modeIds_of_binderGuards rfl hg, htemplates]
    apply List.mem_range'_1.mpr
    change p.firstMode ≤ n ∧ n < p.firstMode + (templates.nextMode - p.firstMode)
    change n < templates.nextMode at hb
    omega
  have htypes : ∀v, ∀w∈(templates.substitution.type v).modVars, CoveredMode s w :=
    Substitution.type_modeSupport himages
  have hmodes (v : ModVar) (hv : CoveredMode s v) :
      ∀w∈(templates.substitution.mode v).vars, CoveredMode s w := by
    rw [ComparisonSkeleton.prepare_mode]
    simpa only [ModExpr.vars, Finset.mem_singleton, forall_eq] using hv
  have hsource := source_covered (target := target) ht hm shapes known
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact bounds_mode_support p.sourceBounds templates.substitution htypes hmodes
      (fun v hv => hsource v (Finset.mem_union_left _ hv)) v hv
  · exact TypeExpr.mode_support_subst p.sourceType templates.substitution
      (fun v _ => htypes v)
      (fun v hv => hmodes v (hsource v (Finset.mem_union_right _ hv))) v hv

theorem reduced_modes (s : Setup) (hb : s.before = {}) (hg : BinderGuards s.original)
    (result : ComparisonReduction.State) :
    (s.reduced result).modes = ComparisonGuardedTotal.scalarBounds s.original.sourceBounds ++ result.modes := by
  simp only [Setup.reduced, Setup.annotations, s.absorbed_of_binderGuards hb hg,
    (annotations_trivial hg s.total).2.1, s.input_empty hb, List.nil_append]

theorem scalarBounds_support {Q : ModVar → Prop} {bounds : Bounds}
    (h : ∀v∈bounds.modVars, Q v) : ∀v∈(ComparisonGuardedTotal.scalarBounds bounds).modVars, Q v := by
  intro v hv
  obtain ⟨c, hc, hv⟩ := ((ComparisonGuardedTotal.scalarBounds bounds).mem_modVars_iff v).mp hv
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp (List.mem_filter.mp hc).1
  exact d.assumptions_modeSupport
    (fun v hv => h v ((bounds.mem_modVars_iff v).mpr ⟨d, hd, hv⟩)) c hc v hv


theorem reduction_modeSupport {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    {result : ComparisonReduction.State}
    (hr : ComparisonReduction.prepare fuel
      (Setup.work ⟨SchemePreparation.prepare [] source.requireDefinedInstances target, {}, shapes, known, false⟩)
      (Setup.templates ⟨SchemePreparation.prepare [] source.requireDefinedInstances target, {}, shapes, known, false⟩)
      (Setup.bare ⟨SchemePreparation.prepare [] source.requireDefinedInstances target, {}, shapes, known, false⟩)
      known false = .success result) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ComparisonReduction.ModeSupport (CoveredMode s) (s.reduced result) := by
  let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
    {}, shapes, known, false⟩
  have hg : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hs := prepared_template_covered (target := target) ht hm shapes known
  have hwork := s.work_of_binderGuards rfl hg
  have hbase := ComparisonReduction.prepare_modeSupport hr
    (fun c hc v hv => hs v (Finset.mem_union_left _
      (((s.templates.substitution.bounds s.work.sourceBounds).mem_modVars_iff v).mpr ⟨c, hc, hv⟩)))
    (fun v hv => hs v (Finset.mem_union_right _ hv))
    (fun v hv => Or.inl (target_allowed [] source.requireDefinedInstances target (by simpa only [hwork] using hv)))
  refine ⟨hbase.pending, hbase.inequalities, ?_, hbase.bareBounds, hbase.partialTypes⟩
  intro c hc v hv
  rw [reduced_modes s rfl hg] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact scalarBounds_support
      (fun v hv => source_covered ht hm shapes known v (Finset.mem_union_left _ hv))
      v (((ComparisonGuardedTotal.scalarBounds s.original.sourceBounds).mem_modVars_iff v).mpr ⟨c, hc, hv⟩)
  · exact hbase.modes c hc v hv


theorem scalarBounds_scalar (bounds : Bounds) :
    ∀c∈ComparisonGuardedTotal.scalarBounds bounds, ComparisonReduction.Scalar c := by
  intro c hc
  have hf := (List.mem_filter.mp hc).2
  cases c <;> simp_all [ComparisonReduction.Scalar]

theorem reduced_scalarModes {s : Setup} {fuel : Nat} {result : ComparisonReduction.State}
    (hb : s.before = {}) (hg : BinderGuards s.original)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success result) :
    ComparisonReduction.ScalarModes (s.reduced result) := by
  intro c hc
  rw [reduced_modes s hb hg] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact scalarBounds_scalar _ c hc
  · exact (ComparisonReduction.prepare_closed hr).2.2 c hc

theorem collected_labels_support {p : Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    {Q : ModVar → Prop}
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (ha : ∀v∈p.assumptions.modVars, Q v)
    (hi : ∀pair∈reduced.inequalities, ∀v∈pair.1.modVars ∪ pair.2.modVars, Q v) :
    ∀g∈groups, ∀pair∈g.assumptions ++ g.goals,
      ∀v∈pair.1.mode.vars ∪ pair.2.mode.vars, Q v := by
  intro g hg pair hp v hv
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨left, right, hc, he⟩ := ComparisonGroups.collect_assumption_origin hc g hg pair hp
    obtain ⟨hl, hr⟩ := ComparisonGroups.inequality_spec he
    apply ha v
    apply (p.assumptions.mem_modVars_iff v).mpr
    refine ⟨.sub left right, hc, ?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ComparisonGroups.atom_modeVars_subset hl hv)
    · exact Finset.mem_union_right _ (ComparisonGroups.atom_modeVars_subset hr hv)
  · obtain ⟨goal, hgoal, he, _⟩ := ComparisonGroups.collect_goal_origin hc g hg pair hp
    obtain ⟨hl, hr⟩ := ComparisonGroups.inequality_spec he
    apply hi goal hgoal v
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ComparisonGroups.atom_modeVars_subset hl hv)
    · exact Finset.mem_union_right _ (ComparisonGroups.atom_modeVars_subset hr hv)

theorem collection_scope {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    {result : ComparisonReduction.State} {groups : List ComparisonGroups.Group} :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ComparisonReduction.prepare fuel s.work s.templates s.bare known false = .success result →
    ComparisonGroups.collect s.work shapes s.templates (s.reduced result) = .success groups →
    (∀v∈s.work.assumptions.modVars, v∈allowedModes s.original) ∧
    (∀v∈(s.reduced result).modes.modVars, CoveredMode s v) ∧
    ComparisonReduction.ScalarModes (s.reduced result) ∧
    (∀g∈groups, ∀pair∈g.assumptions ++ g.goals,
      ∀v∈pair.1.mode.vars ∪ pair.2.mode.vars, CoveredMode s v) ∧
    (∀g∈groups, ∀v∈ComparisonElimination.groupModes s.work.assumptions (s.reduced result).modes g,
      CoveredMode s v) := by
  intro s hr hc
  have hg : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hw := s.work_of_binderGuards rfl hg
  have ha : ∀v∈s.work.assumptions.modVars, v∈allowedModes s.original := by
    intro v hv
    exact assumptions_allowed [] source.requireDefinedInstances target (by simpa only [hw] using hv)
  have hs := reduction_modeSupport ht hm hr
  have hmodes : ∀v∈(s.reduced result).modes.modVars, CoveredMode s v := by
    intro v hv
    obtain ⟨c, hc, hv⟩ := ((s.reduced result).modes.mem_modVars_iff v).mp hv
    exact hs.modes c hc v hv
  have hi : ∀pair∈(s.reduced result).inequalities,
      ∀v∈pair.1.modVars ∪ pair.2.modVars, CoveredMode s v := by
    intro pair hp v hv
    exact (Finset.mem_union.mp hv).elim ((hs.inequalities pair hp).1 v)
      ((hs.inequalities pair hp).2 v)
  exact ⟨ha, hmodes, reduced_scalarModes rfl hg hr,
    collected_labels_support hc (fun v hv => Or.inl (ha v hv)) hi,
    ComparisonElimination.collected_groupModes_support hc
      (fun v hv => Or.inl (ha v hv)) hmodes hi⟩


/-- The actual guarded pipeline uses permitted original names and exactly its
allocated flexible scalar coordinates. Declared inputs are never synthesized. -/
theorem collection_mode_scope {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    {result : ComparisonReduction.State} {groups : List ComparisonGroups.Group} :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ComparisonReduction.prepare fuel s.work s.templates s.bare known false = .success result →
    ComparisonGroups.collect s.work shapes s.templates (s.reduced result) = .success groups →
    (∀v∈s.work.assumptions.modVars, v∈allowedModes s.original ∧
      ∀axis<3, v.atomIndex axis ∉ SchemeModeSynthesis.atoms s.modeIds) ∧
    (∀v∈(s.reduced result).modes.modVars,
      v∈allowedModes s.original ∨ ∃n∈s.modeIds, v = .flex n) ∧
    (∀g∈groups, ∀m∈ComparisonElimination.groupLabels g,
      ∀v∈m.vars, v∈allowedModes s.original ∨ ∃n∈s.modeIds, v = .flex n) ∧
    ComparisonReduction.ScalarModes (s.reduced result) := by
  intro s hr hc
  obtain ⟨ha, hmodes, hscalar, hl, _⟩ := collection_scope ht hm hr hc
  refine ⟨fun v hv => ⟨ha v hv, fun axis haxis => allowed_atoms_fixed (ha v hv) haxis⟩,
    hmodes, ?_, hscalar⟩
  intro g hg m hm v hv
  obtain ⟨pair, hp, hm⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hm)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hl g hg pair hp v (Finset.mem_union_left _ hv)
  · obtain rfl := List.mem_singleton.mp hm
    exact hl g hg pair hp v (Finset.mem_union_right _ hv)

end ModalityInference.ComparisonJointChecker
