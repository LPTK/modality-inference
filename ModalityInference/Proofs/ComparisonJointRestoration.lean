import ModalityInference.ComparisonJointChecker
import ModalityInference.Proofs.ComparisonDefinedSetup
import ModalityInference.Proofs.ComparisonReductionClosure
import ModalityInference.Proofs.ComparisonGuardedTotal
import ModalityInference.Proofs.ComparisonDefinedSubstitution
import ModalityInference.Proofs.ComparisonCheckerScope

/-! Restore structural templates after a shared guarded comparison solve. -/
namespace ModalityInference.ComparisonJointChecker

open ComparisonChecker ComparisonReduction ComparisonGuardedTotal

theorem scalar_models {Δ required : Bounds} {σ : CompareSubstitution}
    (hs : ∀ c ∈ required, Scalar c)
    (h : AlgebraEntailsAll Δ (σ.bounds required)) {η : ModVar → Mode}
    (hη : ModeModels Δ η) : ModeModels required (valuation σ.mode η) := by
  intro c hc
  have he := h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have hc := hs c hc
  cases c with
  | sub | equiv | equal => contradiction
  | mode a b => exact below_valuation (he.denote hη)
  | defined m => exact wellFormed_valuation (he η hη)

theorem knownTotal_scalar_subst {Δ guards : Bounds} {σ : CompareSubstitution}
    {fuel : Nat} {expressions known : List ModExpr}
    (hk : ComparisonBody.knownTotal fuel (Δ ++ guards.assumptions) expressions = .success known)
    (hguards : AlgebraEntailsAll Δ (σ.bounds (scalarBounds guards)))
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v)
    (hw : ∀ v, Entails Δ (.defined (σ.mode v)))
    {m : ModExpr} (hm : ComparisonBody.isTotal known m = true) :
    Submode Δ (m.subst σ.mode) (m.subst σ.mode) := by
  apply Submode.refl
  intro η hη
  have hmodel : ModeModels (Δ ++ guards.assumptions) (valuation σ.mode η) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact valuation_original hf hη c hc
    · apply (scalarBounds_models guards _).mp (scalar_models (σ := σ) ?_ hguards hη) c hc
      intro d hd
      have hd := (List.mem_filter.mp hd).2
      cases d <;> simp_all [Scalar]
  change ((m.subst σ.mode).eval (some ∘ η)).isSome = true
  rw [eval_subst_valuation (fun v _ => hw v η hη)]
  exact ComparisonBody.isTotal_defined (ComparisonBody.knownTotal_sound hk) hm _ hmodel

/-- Opaque inequalities and the original scalar obligations reconstruct the
complete source bounds and body. No source guard is added to the context. -/
theorem restore_sound {s : Setup} {fuel : Nat} {reduced : ComparisonReduction.State}
    {core : CompareSubstitution}
    (hbefore : s.before = {}) (hshared : s.shared = false)
    (hguards : SchemePreparation.BinderGuards s.original)
    (hk : ComparisonBody.knownTotal fuel
      (s.original.assumptions ++ s.original.sourceBounds.assumptions)
      (ComparisonAnnotations.obligationExpressions s.original) = .success s.known)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (hshape : core.WellShaped s.original.assumptions)
    (hdefined : core.WellFormedUnder s.original.assumptions)
    (hfixedType : ∀ v ∈ s.original.assumptions.typeVars, core.type v = .var v)
    (hfixedMode : ∀ v ∈ s.original.assumptions.modVars, core.mode v = .var v)
    (htarget : core.ty s.original.targetType = .ofTy s.original.targetType)
    (hi : ∀ pair ∈ reduced.inequalities, PairHolds s.original.assumptions core pair)
    (hm : AlgebraEntailsAll s.original.assumptions (core.bounds (s.reduced reduced).modes)) :
    let action := ComparisonExactContext.finish s.templates.substitution core
    action.WellShaped s.original.assumptions ∧
      AlgebraEntailsAll s.original.assumptions (action.bounds s.original.sourceBounds) ∧
      AlgebraSubtype s.original.assumptions (action.ty s.original.sourceType)
        (.ofTy s.original.targetType) := by
  have hwork := s.work_of_binderGuards hbefore hguards
  have hbare := s.bare_of_binderGuards hbefore hguards hshared
  have hscalar : AlgebraEntailsAll s.original.assumptions
      (core.bounds (scalarBounds s.original.sourceBounds)) := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    apply hm _ (List.mem_map.mpr ⟨d, ?_, rfl⟩)
    apply List.mem_append_left
    apply List.mem_append_right
    simpa only [s.input_empty hbefore] using hd
  have htotal : ∀ m, ComparisonBody.isTotal s.known m = true →
      Submode s.original.assumptions (m.subst core.mode) (m.subst core.mode) :=
    fun _ ht => knownTotal_scalar_subst hk hscalar hfixedMode hdefined.modes ht
  have hpartial : reduced.partialTypes = [] := by
    apply List.eq_nil_of_map_eq_nil
    simpa only [hbare] using ComparisonReduction.prepare_partial_domain hr
  have hresult := ComparisonReduction.prepare_holds hr hi
    (fun a b hab => hm _ (List.mem_map.mpr
      ⟨.mode a b, List.mem_append_right _ hab, rfl⟩))
    (fun m hmem => hm _ (List.mem_map.mpr
      ⟨.defined m, List.mem_append_right _ hmem, rfl⟩))
  have hinitial := ComparisonReduction.prepare_sound hshape
    (fun a b hc => CompareSubstitution.declared_subtype hfixedType hfixedMode
      (by simpa only [hwork] using hc)) htotal
    (by simp only [hpartial, List.not_mem_nil, false_implies, implies_true]) hr hresult
  have hstart : ComparisonReduction.Holds s.original.assumptions core
      (ComparisonReduction.initial (s.templates.substitution.bounds s.original.sourceBounds)
        (s.templates.substitution.ty s.original.sourceType) s.original.targetType) := by
    rw [hwork] at hinitial
    exact ⟨hinitial.pending, hinitial.inequalities, hinitial.modes, hinitial.bareBounds⟩
  refine ⟨ComparisonExactContext.finish_wellShaped s.templates.substitution hshape, ?_, ?_⟩
  · rw [ComparisonExactContext.finish_bounds]
    exact ComparisonReduction.initial_entails hstart (fun _ _ v _ => hdefined.types v)
  · rw [ComparisonExactContext.finish_ty]
    simpa only [htarget] using ComparisonReduction.initial_body hstart

end ModalityInference.ComparisonJointChecker
