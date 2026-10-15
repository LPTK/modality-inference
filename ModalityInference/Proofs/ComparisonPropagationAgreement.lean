import ModalityInference.Proofs.ComparisonPropagationModes
import ModalityInference.Proofs.ComparisonPropagationImages
import ModalityInference.Proofs.ComparisonPropagationTrace

/-! The returned finite witness agrees on the original scheme with the
semantic composition of structural and partial-context substitutions. -/
namespace ModalityInference.ComparisonChecker

def Setup.semanticAfter (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) : CompareSubstitution :=
  ComparisonExactContext.finish s.absorption.action
    (ComparisonExactContext.finish s.annotations.substitution
      (ComparisonExactContext.finish s.templates.substitution
        (ComparisonElimination.imageAction (reduced.partialTypes ++ types.types) modes.substitution)))

def Setup.semanticAction (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) : CompareSubstitution :=
  ComparisonExactContext.finish s.before (s.semanticAfter reduced types modes)

theorem Setup.templates_disjoint_partial (s : Setup) {fuel reduced}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced) :
    ∀ entry ∈ s.templates.substitution.types, entry.1 ∉ reduced.partialTypes.map Prod.fst := by
  intro entry he hn
  have ht := List.mem_map_of_mem (f := Prod.fst) he
  simp only [Setup.templates, ComparisonSkeleton.allocate_domain] at ht
  rw [ComparisonReduction.prepare_partial_domain hr] at hn
  exact s.bare_not_names hn ht

theorem Setup.template_images_avoid_partial (s : Setup) {fuel reduced}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced) :
    ∀ entry ∈ s.templates.substitution.types, ∀ v ∈ entry.2.typeVars,
      ∀ pair ∈ reduced.partialTypes, v ≠ .flex pair.1 := by
  intro entry he v hv pair hp heq
  have hn := List.mem_map_of_mem (f := Prod.fst) hp
  rw [ComparisonReduction.prepare_partial_domain hr] at hn
  have hf := ComparisonSkeleton.allocate_images_free s.work s.shapes s.names s.bare
    s.original.nextType s.annotations.nextMode (fun _ hn => (s.bare_range hn).2) entry he pair.1 hn
  exact hf (heq ▸ hv)

theorem Setup.elimination_keys_fresh (s : Setup) {fuel reduced types}
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (v : TypeVar) (hv : v.index < s.original.nextType) :
    ∀ entry ∈ types.types, v ≠ .flex entry.1 := by
  intro entry hm heq
  obtain ⟨leaf, hl, hn⟩ := ComparisonElimination.run_type_domain he entry hm
  have hlo := (ComparisonSkeleton.allocate_leaf_range _ _ _ _ _ leaf hl).1
  subst v
  change entry.1 < s.original.nextType at hv
  omega

theorem Setup.runtimeAfter_types (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (modes : SchemeModeSynthesis.Result) :
    (s.runtimeAfter reduced types modes).types =
      (ComparisonElimination.imageAction (s.rawImages reduced types) modes.substitution).types := by
  apply List.map_congr_left
  intro entry hm
  exact congrArg (Prod.mk entry.1)
    (s.rawImages_mode_eq hr he htarget hassumptions modes.substitution entry hm)

theorem Setup.semanticAfter_type (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (modes : SchemeModeSynthesis.Result) (v : TypeVar) (hv : v.index < s.original.nextType) :
    (s.semanticAfter reduced types modes).type v = (s.runtimeAfter reduced types modes).type v := by
  unfold semanticAfter
  have hann : ∀ w, s.annotations.substitution.type w = .var w :=
    ComparisonAnnotations.prepare_type s.absorbed s.total
  rw [ComparisonExactContext.finish_type_of_identity _ (ComparisonAbsorption.action_type _),
    ComparisonExactContext.finish_type_of_identity _ hann]
  have ha := assembled_type_eq s.templates.substitution reduced.partialTypes types.types modes.substitution
    (s.templates_disjoint_partial hr) (s.template_images_avoid_partial hr) v (s.elimination_keys_fresh he v hv)
  refine ha.trans ?_
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [CompareSubstitution.type, s.runtimeAfter_types hr he htarget hassumptions modes]
    rfl

theorem Setup.semanticAfter_mode (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) (v : ModVar) :
    (s.semanticAfter reduced types modes).mode v = (s.runtimeAfter reduced types modes).mode v := by
  have hm : (ComparisonExactContext.finish s.templates.substitution
      (ComparisonElimination.imageAction (reduced.partialTypes ++ types.types) modes.substitution)).modes =
      modes.substitution.modes := by
    simp [ComparisonExactContext.finish, Substitution.compose, s.templates_modes,
      ComparisonElimination.imageAction]
  have he := restoredModes_finish s.absorption s.annotations
    (ComparisonExactContext.finish s.templates.substitution
      (ComparisonElimination.imageAction (reduced.partialTypes ++ types.types) modes.substitution)) v
  simpa only [hm] using he.symm

theorem Setup.semanticAction_mode (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) (v : ModVar) :
    (s.semanticAction reduced types modes).mode v = (s.runtimeAction reduced types modes).mode v := by
  unfold semanticAction runtimeAction
  rw [ComparisonExactContext.finish_mode, ComparisonExactContext.finish_mode]
  exact (s.before.mode v).subst_congr (fun w _ => s.semanticAfter_mode reduced types modes w)

theorem Setup.semanticAction_type (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hbefore : s.before.Bounded s.original.nextType s.original.nextMode)
    (modes : SchemeModeSynthesis.Result) (v : TypeVar) (hv : v.index < s.original.nextType) :
    (s.semanticAction reduced types modes).type v = (s.runtimeAction reduced types modes).type v := by
  unfold semanticAction runtimeAction
  rw [ComparisonExactContext.finish_type, ComparisonExactContext.finish_type]
  apply CompareSubstitution.ty_congr_on
  · intro w hw
    exact s.semanticAfter_type hr he htarget hassumptions modes w
      ((TypeExpr.bounded_iff _ _ _).mp (hbefore.type v hv) |>.1 w hw)
  · intro w _
    exact s.semanticAfter_mode reduced types modes w

theorem Setup.semanticAction_ty (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hbefore : s.before.Bounded s.original.nextType s.original.nextMode)
    (modes : SchemeModeSynthesis.Result) (a : Ty)
    (ha : a.Bounded s.original.nextType s.original.nextMode) :
    (s.semanticAction reduced types modes).ty a = (s.runtimeAction reduced types modes).ty a := by
  apply CompareSubstitution.ty_congr_on
  · exact fun v hv => s.semanticAction_type hr he htarget hassumptions hbefore modes v
      ((TypeExpr.bounded_iff _ _ _).mp ha |>.1 v hv)
  · exact fun v _ => s.semanticAction_mode reduced types modes v

theorem Setup.semanticAction_bounds (s : Setup) {fuel reduced types}
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (htarget : ∀ v ∈ s.original.targetType.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hassumptions : ∀ v ∈ s.original.assumptions.modVars,
      ComparisonInstance.modeAllowed s.original v = false)
    (hbefore : s.before.Bounded s.original.nextType s.original.nextMode)
    (modes : SchemeModeSynthesis.Result) (bounds : Bounds)
    (hb : bounds.Bounded s.original.nextType s.original.nextMode) :
    AlgebraEntailsAll s.original.assumptions ((s.semanticAction reduced types modes).bounds bounds) ↔
      AlgebraEntailsAll s.original.assumptions ((s.runtimeAction reduced types modes).bounds bounds) := by
  apply CompareSubstitution.algebra_bounds_congr
  · exact fun c hc v hv => s.semanticAction_type hr he htarget hassumptions hbefore modes v
      ((Constraint.bounded_iff _ _ _).mp (hb c hc) |>.1 v hv)
  · exact fun _ _ v _ => s.semanticAction_mode reduced types modes v

theorem Setup.runtimeAction_wellShaped_of_images (s : Setup) {reduced types}
    (hpartial : ∀ entry ∈ reduced.partialTypes, entry.2.WellShaped s.original.assumptions)
    (hleaves : ∀ entry ∈ types.types, entry.2.WellShaped s.original.assumptions)
    (modes : SchemeModeSynthesis.Result) :
    (s.runtimeAction reduced types modes).WellShaped s.original.assumptions := by
  apply ComparisonExactContext.finish_wellShaped
  apply ComparisonElimination.imageAction_wellShaped
  intro entry he
  rcases List.mem_append.mp he with he | he
  · exact hpartial entry he
  · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp he
    have hw : ({types := types.types} : CompareSubstitution).WellShaped s.original.assumptions := hleaves
    exact hw.ty old.2

end ModalityInference.ComparisonChecker
