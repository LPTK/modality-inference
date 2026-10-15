import ModalityInference.Proofs.ComparisonFixedModeWitness

/-! The projected common witness changes only modality names allocated by the
actual source and structural-template preparation. -/

namespace ModalityInference.ComparisonSkeleton

theorem build_modeBound (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt nm : Nat) :
    ∀v∈(build p shape nt nm).modVars, v.index < nm + modeCount p shape := by
  induction shape generalizing nt nm with
  | var v =>
    simp only [build, modeCount]
    split
    · simp [TypeExpr.modVars, ModExpr.vars, ModVar.index]
    · simp [TypeExpr.modVars]
  | unit | credit => simp [build, modeCount, TypeExpr.modVars, ModExpr.vars, ModVar.index]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [build, TypeExpr.modVars, ModExpr.vars, Finset.mem_union,
      Finset.mem_singleton, or_imp, forall_and, forall_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v hv
      have h := iha nt (nm + 1) v hv
      simp only [modeCount]
      omega
    · intro v hv
      have h := ihb (nt + typeCount p a) (nm + 1 + modeCount p a) v hv
      simp only [modeCount]
      omega
    · simp only [ModVar.index, modeCount]
      omega

theorem allocate_modeBound (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (names : List Nat) (nt nm : Nat) :
    ∀entry∈(allocate p shapes names nt nm).substitution.types,
      ∀v∈entry.2.modVars, v.index < (allocate p shapes names nt nm).nextMode := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons name names ih =>
    intro entry he v hv
    rcases List.mem_cons.mp he with rfl | he
    · have h := build_modeBound p (shapes.resolveAll (.flex name)) nt nm v hv
      simp only [(allocate_next (name :: names) nt nm).2, modeSpan]
      omega
    · exact ih _ _ entry he v hv

end ModalityInference.ComparisonSkeleton

namespace ModalityInference.ComparisonFixedModeWitness

theorem template_inputModes_bound {p : SchemePreparation.Prepared}
    (shapes : ComparisonShapeSolver.Solved)
    (hs : ∀v∈inputModes p.sourceBounds p.sourceType, v.index < p.nextMode) :
    let templates := ComparisonSkeleton.prepare p shapes
    ∀v∈inputModes (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType), v.index < templates.nextMode := by
  let templates := ComparisonSkeleton.prepare p shapes
  change ∀v∈inputModes (templates.substitution.bounds p.sourceBounds)
    (templates.substitution.ty p.sourceType), v.index < templates.nextMode
  have hnext : p.nextMode ≤ templates.nextMode := by
    change p.nextMode ≤ (ComparisonSkeleton.allocate p shapes _ _ _).nextMode
    rw [(ComparisonSkeleton.allocate_next _ _ _).2]
    omega
  have ht : ∀v, ∀w∈(templates.substitution.type v).modVars,
      w.index < templates.nextMode :=
    Substitution.type_modeSupport (ComparisonSkeleton.allocate_modeBound p shapes _ _ _)
  have hm (v : ModVar) (hv : v.index < templates.nextMode) :
      ∀w∈(templates.substitution.mode v).vars, w.index < templates.nextMode := by
    rw [ComparisonSkeleton.prepare_mode]
    simpa only [ModExpr.vars, Finset.mem_singleton, forall_eq] using hv
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact bounds_mode_support p.sourceBounds templates.substitution ht hm
      (fun v hv => (hs v (Finset.mem_union_left _ hv)).trans_le hnext) v hv
  · exact TypeExpr.mode_support_subst p.sourceType templates.substitution
      (fun v _ => ht v)
      (fun v hv => hm v ((hs v (Finset.mem_union_right _ hv)).trans_le hnext)) v hv

theorem prepared_template_inputModes_bound (ambient : Bounds) (source target : Scheme)
    (shapes : ComparisonShapeSolver.Solved) :
    let p := SchemePreparation.prepare ambient source target
    let templates := ComparisonSkeleton.prepare p shapes
    ∀v∈inputModes (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType), v.index < templates.nextMode := by
  apply template_inputModes_bound
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).2 v hv
  · exact ((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceType_bounded ambient source target)).2 v hv

theorem project_modeDomain {cutoff upper : Nat} {bounds : Bounds} {body : Ty}
    (σ : CompareSubstitution) (hs : ∀v∈inputModes bounds body, v.index < upper) :
    ∀entry∈(project cutoff bounds body σ).modes,
      cutoff ≤ entry.1 ∧ entry.1 < upper := by
  intro entry he
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
  obtain ⟨hl, hi⟩ := mem_keys.mp hn
  exact ⟨hl, hs _ hi⟩

/-- The projected common assignment has no modality-domain keys beyond the
actual allocation frontier. -/
theorem prepared_template_fixed_scoped {source target : Scheme}
    {fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved shapes))
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hR : Residual target.bounds) :
    let p := SchemePreparation.prepare [] source target
    let templates := ComparisonSkeleton.prepare p shapes
    ∃core : CompareSubstitution,
      core.DomainsAbove p.nextType p.firstMode ∧
      core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
      AlgebraEntailsAll p.assumptions (core.bounds (templates.substitution.bounds p.sourceBounds)) ∧
      (core.ty (templates.substitution.ty p.sourceType)).DefinedUnder p.assumptions ∧
      AlgebraSubtype p.assumptions (core.ty (templates.substitution.ty p.sourceType)) (.ofTy p.targetType) ∧
      FixedImages p.firstMode core ∧
      (∀leaf∈templates.leaves, ComparisonShape.Equivalent p.assumptions
        (core.type (.flex leaf.name)).shape (.var leaf.shapeClass)) ∧
      (∀v∈inputModes (templates.substitution.bounds p.sourceBounds)
          (templates.substitution.ty p.sourceType),
        ∀w∈(core.mode v).vars, w.index < p.firstMode) ∧
      ComparisonReduction.OpaqueAction core ∧
      (∀entry∈core.modes, entry.1 < templates.nextMode) := by
  let p := SchemePreparation.prepare [] source target
  let templates := ComparisonSkeleton.prepare p shapes
  obtain ⟨trees, hsh, hWF, hb, hd, hbody, _, _⟩ :=
    ComparisonSkeleton.prepared_template_under hshape hw hR
  let old := ComparisonSkeleton.preparedForest p shapes trees σ
  have hdom : old.DomainsAbove p.nextType p.firstMode :=
    ComparisonSkeleton.preparedForest_domains p shapes trees σ (Nat.le_add_right _ _) hw.1.1
  have hf := hdom.mode_fixed
  have hs := template_rigidScoped shapes (prepared_rigidScoped [] source target)
  have hΔ := prepared_assumptions [] source target
  let core := project p.firstMode (templates.substitution.bounds p.sourceBounds)
    (templates.substitution.ty p.sourceType) old
  refine ⟨core, project_domainsAbove hdom, project_wellShaped hsh,
    project_wellFormedUnder hΔ hWF, project_bounds hΔ hf hs hb,
    project_body_defined hΔ hf hs hd,
    project_body hΔ hf hs (prepared_target [] source target) hbody,
    project_fixedImages _ _ _ _, ?_, ?_, ?_, ?_⟩
  · intro leaf hl
    rw [project_type_shape]
    exact ComparisonSkeleton.preparedForest_leaf p shapes trees σ hl
  · exact fun v hv => project_mode_support hf hs hv
  · intro v
    rw [project_type_shape]
    exact ComparisonSkeleton.preparedForest_opaque
      (SchemePreparation.prepare_assumptions_residual hR) p shapes trees σ v
  · exact fun entry he => (project_modeDomain old
      (prepared_template_inputModes_bound [] source target shapes) entry he).2

end ModalityInference.ComparisonFixedModeWitness
