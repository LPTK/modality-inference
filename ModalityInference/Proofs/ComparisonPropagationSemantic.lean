import ModalityInference.Proofs.ComparisonPropagationCore
import ModalityInference.Proofs.ComparisonPropagationAgreement

/-! Reconstruct the guarded source bounds and bare body through every prepass. -/
namespace ModalityInference.ComparisonChecker

/-- Transparent labels retain the synthesized action because every adapted
modality key lies outside their support. -/
theorem Setup.transparent_semanticAfter_of_total (s : Setup) {modes reduced types}
    (htotal : ∀ m, s.total m = true → Submode s.original.assumptions
      (m.subst modes.substitution.mode) (m.subst modes.substitution.mode))
    (m : ModExpr) (ht : ComparisonAbsorption.transparent s.input s.total m = true) :
    Submode s.original.assumptions
      (m.subst (s.semanticAfter reduced types modes).mode)
      (m.subst (s.semanticAfter reduced types modes).mode) := by
  have he := ComparisonAbsorption.transparent_subst_eq
    (left := (s.semanticAfter reduced types modes).mode)
    (right := modes.substitution.mode) ht (fun v hv => by
      rw [s.semanticAfter_mode]
      apply restoredModes_agrees
      apply avoids_adaptedNames_of_fixed (p := s.input) (total := s.total)
      cases v with
      | rigid n => rfl
      | flex n => exact hv n rfl)
  rw [he]
  exact htotal m (Bool.and_eq_true_iff.mp ht).1

theorem Setup.transparent_semanticAfter (s : Setup) {fuel modes query reduced types}
    (hk : ComparisonBody.knownTotal fuel s.input.assumptions
      (ComparisonAnnotations.expressions s.input.sourceType ++
        ComparisonAnnotations.expressions s.input.targetType) = .success s.known)
    (hm : SchemeModeSynthesis.run fuel s.modeIds query = .success modes)
    (hf : ∀ v ∈ s.original.assumptions.modVars, modes.substitution.mode v = .var v)
    (m : ModExpr) (ht : ComparisonAbsorption.transparent s.input s.total m = true) :
    Submode s.original.assumptions
      (m.subst (s.semanticAfter reduced types modes).mode)
      (m.subst (s.semanticAfter reduced types modes).mode) := by
  exact s.transparent_semanticAfter_of_total
    (fun _ ht => ComparisonBody.isTotal_synthesized hk hm hf ht) m ht

theorem Setup.semantic_sound_of_total (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (htotal : ∀ m, s.total m = true → Submode s.original.assumptions
      (m.subst modes.substitution.mode) (m.subst modes.substitution.mode))
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types)
    (hm : SchemeModeSynthesis.run fuel s.modeIds types.query = .success modes) :
    (s.semanticAction reduced types modes).WellShaped s.original.assumptions ∧
    AlgebraEntailsAll s.original.assumptions
      ((s.semanticAction reduced types modes).bounds s.original.sourceBounds) ∧
    AlgebraSubtype s.original.assumptions
      ((s.semanticAction reduced types modes).ty s.original.sourceType)
      (.ofTy s.original.targetType) := by
  have hc := s.core_sound_of_total hp hs hb hbounded htotal hr he hm
  exact compose_prepasses s.original s.before s.known s.templates.substitution
    (s.coreAction reduced types modes) hc.1
    (s.transparent_semanticAfter_of_total htotal) hc.2.1 hc.2.2

theorem Setup.semantic_sound (s : Setup) {source target : Scheme} {fuel reduced types modes}
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
    (s.semanticAction reduced types modes).WellShaped s.original.assumptions ∧
    AlgebraEntailsAll s.original.assumptions
      ((s.semanticAction reduced types modes).bounds s.original.sourceBounds) ∧
    AlgebraSubtype s.original.assumptions
      ((s.semanticAction reduced types modes).ty s.original.sourceType)
      (.ofTy s.original.targetType) := by
  have ha : s.original.assumptions.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded_first [] source target
  exact s.semantic_sound_of_total hp hs hb hbounded
    (fun _ ht => ComparisonBody.isTotal_synthesized hk hm (s.synthesized_assumptions hm ha) ht)
    hr he hm

end ModalityInference.ComparisonChecker
