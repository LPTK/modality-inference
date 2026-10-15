import ModalityInference.Proofs.ComparisonPropagationImages
import ModalityInference.Proofs.ComparisonPropagationSetup
import ModalityInference.Proofs.ComparisonPropagationTotal
import ModalityInference.Proofs.ComparisonReductionClosure
import ModalityInference.Proofs.ComparisonPropagationDefinedness

namespace ModalityInference.ComparisonChecker

def Setup.coreImages (_s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) : List (Nat × CompareTy) :=
  reduced.partialTypes ++ types.types

def Setup.coreAction (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) : CompareSubstitution :=
  ComparisonElimination.imageAction (s.coreImages reduced types) modes.substitution

theorem Setup.coreImages_leaf (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (leaf : ComparisonSkeleton.Leaf) (hl : leaf ∈ s.templates.leaves) :
    ({ types := s.coreImages reduced types } : CompareSubstitution).type (.flex leaf.name) =
      ({ types := types.types } : CompareSubstitution).type (.flex leaf.name) := by
  apply CompareSubstitution.type_append_right
  intro entry he heq
  have hn := List.mem_map_of_mem (f := Prod.fst) he
  rw [ComparisonReduction.prepare_partial_domain hr] at hn
  have hhi := (s.bare_range hn).2
  have hlo := (ComparisonSkeleton.allocate_leaf_range _ _ _ _ _ leaf hl).1
  have heq := TypeVar.flex.inj heq
  omega

theorem Setup.coreImages_fixed (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (v : TypeVar) (hv : v.index < s.original.nextType)
    (hf : ComparisonShapeSolver.sourceAllowed s.original v = false) :
    ({ types := s.coreImages reduced types } : CompareSubstitution).type v = .var v := by
  apply CompareSubstitution.type_fixed_of_keys
  intro entry hm heq
  rcases List.mem_append.mp hm with hm | hm
  · have hn := List.mem_map_of_mem (f := Prod.fst) hm
    rw [ComparisonReduction.prepare_partial_domain hr] at hn
    obtain ⟨hlo, hhi⟩ := s.bare_range hn
    subst v
    simp only [ComparisonShapeSolver.sourceAllowed, hlo, hhi, decide_true, Bool.true_and] at hf
    contradiction
  · obtain ⟨leaf, hl, hn⟩ := ComparisonElimination.run_type_domain he entry hm
    have hlo := (ComparisonSkeleton.allocate_leaf_range _ _ _ _ _ leaf hl).1
    subst v
    change entry.1 < s.original.nextType at hv
    omega

theorem Setup.synthesized_fixed (s : Setup) {fuel query modes}
    (hm : SchemeModeSynthesis.run fuel s.modeIds query = .success modes)
    (v : ModVar) (hv : v.index < s.original.firstMode) :
    modes.substitution.mode v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply SchemeModeSynthesis.run_mode_fixed hm
    intro hn
    have hn := (List.mem_filter.mp hn).1
    simp only [List.mem_range'] at hn
    change n < s.original.firstMode at hv
    omega

theorem Setup.synthesized_assumptions (s : Setup) {fuel query modes}
    (hm : SchemeModeSynthesis.run fuel s.modeIds query = .success modes)
    (ha : s.original.assumptions.Bounded s.original.firstType s.original.firstMode) :
    ∀ v ∈ s.original.assumptions.modVars, modes.substitution.mode v = .var v :=
  fun v hv => s.synthesized_fixed hm v ((Bounds.bounded_iff _ _ _).mp ha |>.2 v hv)

theorem Setup.prepared_fresh (s : Setup) {source target : Scheme}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hb : s.before.Bounded s.original.nextType s.original.nextMode) :
    ∀ leaf ∈ s.templates.leaves,
      ∀ v ∈ s.work.assumptions.typeVariables ++ s.work.targetType.typeVariables ++
        s.work.sourceType.typeVariables ++ s.work.sourceBounds.typeVariables, v ≠ .flex leaf.name := by
  apply s.leaves_fresh
  apply s.original_types_bounded
  · simpa only [hp] using SchemePreparation.prepare_assumptions_bounded [] source target
  · simpa only [hp] using SchemePreparation.prepare_targetType_bounded [] source target
  · simpa only [hp] using SchemePreparation.prepare_sourceType_bounded [] source target
  · simpa only [hp] using SchemePreparation.prepare_sourceBounds_bounded [] source target
  · exact hb

theorem Setup.partial_wellShaped (s : Setup) {source target : Scheme} {fuel reduced}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced) :
    ∀ entry ∈ reduced.partialTypes, entry.2.WellShaped s.original.assumptions := by
  rcases s with ⟨p, before, shapes, known, shared⟩
  dsimp only at hp
  subst p
  exact partial_images_wellShaped hs hb hr

theorem Setup.coreImages_wellShaped (s : Setup) {source target : Scheme} {fuel reduced types}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types) :
    ∀ entry ∈ s.coreImages reduced types, entry.2.WellShaped s.original.assumptions := by
  intro entry hm
  rcases List.mem_append.mp hm with hm | hm
  · exact s.partial_wellShaped hp hs hb hr entry hm
  · exact ComparisonElimination.run_wellShaped (p := s.work)
      (ComparisonShapeSolver.prepare_fixed_equivalent (p := s.original) hs) he (s.prepared_fresh hp hbounded) entry hm

theorem Setup.coreAction_fixed (s : Setup) {fuel reduced types modes}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (v : TypeVar) (hv : v.index < s.original.nextType)
    (hf : ComparisonShapeSolver.sourceAllowed s.original v = false) :
    (s.coreAction reduced types modes).type v = .var v := by
  rw [coreAction, ComparisonElimination.imageAction_type, s.coreImages_fixed hr he v hv hf]
  rfl

theorem Setup.coreAction_target_types (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types) :
    ∀ v ∈ s.original.targetType.typeVars, (s.coreAction reduced types modes).type v = .var v := by
  have hb : s.original.targetType.Bounded s.original.nextType s.original.nextMode := by
    simpa only [hp] using SchemePreparation.prepare_targetType_bounded [] source target
  intro v hv
  apply s.coreAction_fixed hr he v ((TypeExpr.bounded_iff _ _ _).mp hb |>.1 v hv)
  simpa only [hp] using ComparisonShapeSolver.prepared_target_fixed [] source target v (hp ▸ hv)

theorem Setup.coreAction_partial (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types) :
    ∀ entry ∈ reduced.partialTypes, (s.coreAction reduced types modes).type (.flex entry.1) =
      entry.2.subst (s.coreAction reduced types modes).type (s.coreAction reduced types modes).mode := by
  have ht : s.original.targetType.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_targetType_bounded_first [] source target
  exact ComparisonReduction.partial_image_equations types.types modes.substitution hr
    (s.initial_pinned ht) (s.coreAction_target_types hp hr he)

theorem Setup.prepared_types_bounded (s : Setup) {source target : Scheme}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hb : s.before.Bounded s.original.nextType s.original.nextMode) :
    ∀ v ∈ s.work.assumptions.typeVariables ++ s.work.targetType.typeVariables ++
      s.work.sourceType.typeVariables ++ s.work.sourceBounds.typeVariables, v.index < s.original.nextType := by
  apply s.original_types_bounded
  · simpa only [hp] using SchemePreparation.prepare_assumptions_bounded [] source target
  · simpa only [hp] using SchemePreparation.prepare_targetType_bounded [] source target
  · simpa only [hp] using SchemePreparation.prepare_sourceType_bounded [] source target
  · simpa only [hp] using SchemePreparation.prepare_sourceBounds_bounded [] source target
  · exact hb

theorem sourceAllowed_false_of_lt (p : SchemePreparation.Prepared) (v : TypeVar)
    (hv : v.index < p.firstType) : ComparisonShapeSolver.sourceAllowed p v = false := by
  cases v with
  | rigid n => rfl
  | flex n =>
    change n < p.firstType at hv
    simp [ComparisonShapeSolver.sourceAllowed, Nat.not_le.mpr hv]

theorem Setup.coreImages_assumptions (s : Setup) {source target : Scheme} {fuel reduced types}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types) :
    ∀ v ∈ s.original.assumptions.typeVars,
      ({ types := s.coreImages reduced types } : CompareSubstitution).type v = .var v := by
  have ha : s.original.assumptions.Bounded s.original.nextType s.original.nextMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded [] source target
  have hf : s.original.assumptions.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded_first [] source target
  intro v hv
  exact s.coreImages_fixed hr he v ((Bounds.bounded_iff _ _ _).mp ha |>.1 v hv)
    (sourceAllowed_false_of_lt _ v ((Bounds.bounded_iff _ _ _).mp hf |>.1 v hv))

theorem Setup.core_inequalities (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (hm : SchemeModeSynthesis.run fuel s.modeIds types.query = .success modes) :
    ∀ goal ∈ reduced.inequalities,
      ComparisonReduction.PairHolds s.original.assumptions (s.coreAction reduced types modes) goal := by
  have ha : s.original.assumptions.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded_first [] source target
  apply ComparisonElimination.run_algebra_sound_images (p := s.work) he hm
    (ComparisonShapeSolver.prepare_fixed_equivalent (p := s.original) hs) (s.prepared_fresh hp hbounded)
    (ComparisonSkeleton.allocate_leaf_names_nodup _ _ _ _ _)
    (fun _ ha _ hb => ComparisonSkeleton.allocate_leaf_name_injective _ _ _ _ _ ha hb)
    (s.synthesized_assumptions hm ha)
  · change s.original.assumptions.TypeBoundsDefined
    simpa only [hp] using SchemePreparation.prepared_typeBoundsDefined source target
  · exact (ComparisonReduction.prepare_opaqueGuards hr).prepend_modes _
  · exact s.coreImages_leaf hr
  · intro v hv hf
    exact s.coreImages_fixed hr he v (s.prepared_types_bounded hp hbounded v hv) hf
  · exact s.coreImages_assumptions hp hr he
  · exact s.coreImages_wellShaped hp hs hb hbounded hr he

set_option maxHeartbeats 1000000 in
/-- The synthesized core discharges the original reduction input, retaining
partial interval witnesses only in the body paths where they were admitted. -/
theorem Setup.core_sound_of_total (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (htotal : ∀ m, s.total m = true → Submode s.original.assumptions
      (m.subst modes.substitution.mode) (m.subst modes.substitution.mode))
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (hm : SchemeModeSynthesis.run fuel s.modeIds types.query = .success modes) :
    (s.coreAction reduced types modes).WellShaped s.original.assumptions ∧
    AlgebraEntailsAll s.original.assumptions
      ((s.coreAction reduced types modes).bounds (s.templates.substitution.bounds s.work.sourceBounds)) ∧
    AlgebraSubtype s.original.assumptions
      ((s.coreAction reduced types modes).ty (s.templates.substitution.ty s.work.sourceType))
      (.ofTy s.original.targetType) := by
  have ha : s.original.assumptions.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded_first [] source target
  have ht : s.original.targetType.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_targetType_bounded_first [] source target
  have hmode := s.synthesized_assumptions hm ha
  have hwell : (s.coreAction reduced types modes).WellShaped s.original.assumptions :=
    ComparisonElimination.imageAction_wellShaped (s.coreImages_wellShaped hp hs hb hbounded hr he) _
  have hat : ∀ v ∈ s.original.assumptions.typeVars,
      (s.coreAction reduced types modes).type v = .var v := by
    intro v hv
    rw [coreAction, ComparisonElimination.imageAction_type, s.coreImages_assumptions hp hr he v hv]
    rfl
  have hresult := ComparisonReduction.prepare_holds (σ := s.coreAction reduced types modes) hr
    (s.core_inequalities hp hs hb hbounded hr he hm)
    (fun a b hab => ComparisonElimination.run_synthesized_submode (p := s.work)
      (reduced := s.reduced reduced) he hm hmode
      (List.mem_append_right _ hab))
    (fun m hmem => ComparisonElimination.run_synthesized_defined (p := s.work)
      (reduced := s.reduced reduced) he hm hmode
      (List.mem_append_right _ hmem))
  have hinitial := ComparisonReduction.prepare_sound (p := s.work) hwell
    (fun _ _ hc => CompareSubstitution.declared_subtype hat hmode hc)
    htotal
    (s.coreAction_partial hp hr he) hr hresult
  have hstart : ComparisonReduction.Holds s.original.assumptions (s.coreAction reduced types modes)
      (ComparisonReduction.initial (s.templates.substitution.bounds s.work.sourceBounds)
        (s.templates.substitution.ty s.work.sourceType) s.original.targetType) :=
    ⟨hinitial.pending, hinitial.inequalities, hinitial.modes, hinitial.bareBounds⟩
  refine ⟨hwell, ComparisonReduction.initial_entails hstart
    (s.sourceBounds_defined hr he (SchemeModeSynthesis.run_mode_defined hm _)), ?_⟩
  have htarget : (s.coreAction reduced types modes).ty s.original.targetType =
      .ofTy s.original.targetType := CompareSubstitution.ty_fixed _
    (s.coreAction_target_types hp hr he)
    (fun v hv => s.synthesized_fixed hm v ((TypeExpr.bounded_iff _ _ _).mp ht |>.2 v hv))
  simpa only [htarget] using ComparisonReduction.initial_body hstart

/-- Totality established under the original assumptions instantiates the
post-synthesis totality interface. -/
theorem Setup.core_sound (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (hk : ComparisonBody.knownTotal fuel s.input.assumptions
      (ComparisonAnnotations.expressions s.input.sourceType ++
        ComparisonAnnotations.expressions s.input.targetType) = .success s.known)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (hm : SchemeModeSynthesis.run fuel s.modeIds types.query = .success modes) :
    (s.coreAction reduced types modes).WellShaped s.original.assumptions ∧
    AlgebraEntailsAll s.original.assumptions
      ((s.coreAction reduced types modes).bounds (s.templates.substitution.bounds s.work.sourceBounds)) ∧
    AlgebraSubtype s.original.assumptions
      ((s.coreAction reduced types modes).ty (s.templates.substitution.ty s.work.sourceType))
      (.ofTy s.original.targetType) := by
  have ha : s.original.assumptions.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded_first [] source target
  exact s.core_sound_of_total hp hs hb hbounded
    (fun _ ht => ComparisonBody.isTotal_synthesized hk hm (s.synthesized_assumptions hm ha) ht)
    hr he hm

end ModalityInference.ComparisonChecker
