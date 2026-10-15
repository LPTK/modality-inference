import ModalityInference.Proofs.ComparisonExactMatchingScope
import ModalityInference.Proofs.ComparisonContextMatchingCoverage
import ModalityInference.Proofs.ComparisonCapsuleSemanticSpecialization

namespace ModalityInference.ComparisonFrozenContext

open ComparisonInstance ComparisonCapsuleContext ComparisonPreparation
open ComparisonBody ComparisonCapsuleIntervals ComparisonInterpolation ComparisonPartialCapsule

private theorem fixed_of_bounded {p : Prepared} {t : Ty}
    (ht : t.Bounded p.firstType p.firstMode) :
    (∀ v ∈ t.typeVars, typeAllowed p v = false) ∧
      ∀ v ∈ t.modVars, modeAllowed p v = false := by
  have hh := (TypeExpr.bounded_iff _ _ _).mp ht
  constructor
  · intro v hv
    cases v with
    | rigid n => rfl
    | flex n =>
      have hn := hh.1 (.flex n) hv
      simp only [typeAllowed, TypeVar.index, Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
      exact Or.inl (by omega)
  · intro v hv
    cases v with
    | rigid n => rfl
    | flex n =>
      have hn := hh.2 (.flex n) hv
      simp only [modeAllowed, ModVar.index, Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
      exact Or.inl (by omega)

theorem targetFresh_of_bounded {p : Prepared}
    (ht : p.targetType.Bounded p.firstType p.firstMode) : targetFresh p = true := by
  simpa only [targetFresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    TypeExpr.mem_typeVariables, TypeExpr.mem_modeVariables] using fixed_of_bounded ht

/-- Every actual frozen request retains only fixed target identifiers. -/
theorem collect_fixed {p : Prepared} {total : ModExpr → Bool}
    (ht : p.targetType.Bounded p.firstType p.firstMode) :
    ∀ r ∈ collect p total,
      (∀ v ∈ r.2.typeVars, typeAllowed p v = false) ∧
        ∀ v ∈ r.2.modVars, modeAllowed p v = false :=
  fun r hr => fixed_of_bounded (requests_bounded p total _ _ _ ht r hr)

/-- The actual component solver preserves scope even when an unrelated
component has no exact match. -/
theorem independent_scoped {p : Prepared} {total : ModExpr → Bool}
    (ht : p.targetType.Bounded p.firstType p.firstMode) :
    ComparisonExactContext.Scoped p (independent p total) := by
  apply ComparisonContext.solvePriorityComponents_property _ _ _ _ _
    (ComparisonExactContext.Scoped p)
    (fun request : Request =>
      (∀ v ∈ request.2.typeVars, typeAllowed p v = false) ∧
        ∀ v ∈ request.2.modVars, modeAllowed p v = false)
    (by constructor <;> intro _ _ he <;> cases he) (collect_fixed ht)
  intro request hr before after hb hm
  exact matchType_scoped hm hr.1 hr.2 hb

/-- Freshness and scope checks accept every canonically bounded frozen-context
preparation. Exact equation consistency is handled by the component solver. -/
theorem prepare_eq_independent {p : Prepared} {total : ModExpr → Bool}
    (ht : p.targetType.Bounded p.firstType p.firstMode) :
    prepare p total = some (independent p total) := by
  have hf := targetFresh_of_bounded ht
  have hs := (ComparisonExactContext.scopeCheck_iff p _).mpr (independent_scoped (total := total) ht)
  simp only [prepare, hf, Bool.not_true, Bool.false_eq_true, if_false, hs, if_true]

/-- The fresh prepared namespace satisfies the exact-context admission checks. -/
theorem prepared_prepare_eq (source target : Scheme) (total : ModExpr → Bool) :
    prepare (SchemePreparation.prepare [] source target) total =
      some (independent (SchemePreparation.prepare [] source target) total) :=
  prepare_eq_independent (SchemePreparation.prepare_targetType_bounded_first [] source target)

noncomputable section
open Classical

/-- Actual component matching preserves the original complete witness and
covers every semantically frozen key when its collected equations are forced. -/
theorem prepare_shared_specialization {p : Prepared} {total : ModExpr → Bool}
    {σ : CompareSubstitution} (h : PreparedWitness p σ)
    (htarget : p.targetType.Bounded p.firstType p.firstMode)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (he : ∀ r ∈ collect p total, (CompareTy.ofTy r.1).subst σ.type σ.mode = .ofTy r.2)
    (hcover : ∀ a ∈ semanticFrozenOperands p.assumptions σ.mode p.sourceType,
      ∃ r ∈ collect p total, a.typeVars ⊆ r.1.typeVars) :
    let before := independent p total
    prepare p total = some before ∧ ComparisonExactContext.Scoped p before ∧
      AgreesWith before σ.type σ.mode ∧
      PreparedWitness (ComparisonExactContext.rewrite p before) σ ∧
      (∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
        (.defined (m.subst σ.mode)))) p.sourceType,
        typeAllowed p v = true → v.index ∈ before.types.map Prod.fst) ∧
      (∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
        (.defined (m.subst σ.mode)))) (before.ty p.sourceType), typeAllowed p v = false) := by
  have hs := independent_scoped (total := total) htarget
  have ha := independent_agreesWith ht hm he
  have hc := matched_semantic_frozen_keys (independent_covers ht hm he) hcover
  exact ⟨prepare_eq_independent htarget, hs, ha,
    ⟨h.1, h.2.1, (ha.rewrite_bounds hs ht hm _ _).mpr h.2.2.1,
      (ha.rewrite_ty hs ht hm p.sourceType).symm ▸ h.2.2.2⟩,
    hc, specialized_semantic_frozen_fixed hs ha hm hc⟩


/-- The actual frozen-context preparation supplies the following public
parameterized comparison, retaining the shared original mode assignment and
all guards while the suffixes are assigned jointly. -/
theorem prepare_parameterized_witness {p : Prepared} {total : ModExpr → Bool}
    {ρ : TypeVar → ComparisonShape} {σ : CompareSubstitution}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    (h : PreparedWitness p σ)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (he : ∀ r ∈ collect p total, (CompareTy.ofTy r.1).subst σ.type σ.mode = .ofTy r.2)
    (hcover : ∀ a ∈ semanticFrozenOperands p.assumptions σ.mode p.sourceType,
      ∃ r ∈ collect p total, a.typeVars ⊆ r.1.typeVars)
    (horder : p.firstType ≤ p.nextType ∧ p.firstMode ≤ p.nextMode)
    (hsource : p.sourceType.Bounded p.nextType p.nextMode)
    (hbounds : p.sourceBounds.Bounded p.nextType p.nextMode)
    (htarget : p.targetType.Bounded p.firstType p.firstMode) :
    let before := independent p total
    prepare p total = some before ∧
      ∀ (fuel : Nat) (known : List ModExpr),
        knownTotal fuel p.assumptions
          (ComparisonAnnotations.expressions (before.ty p.sourceType) ++
            ComparisonAnnotations.expressions p.targetType) = .success known →
        ∀ (P : TypeVar → Prop) (Q : ModVar → Prop),
          (∀ b ∈ unfrozenBindings (ComparisonExactContext.rewrite p before) (isTotal known),
            Supports P Q (σ.type (.flex b.name))) →
          (∀ b ∈ unfrozenBindings (ComparisonExactContext.rewrite p before) (isTotal known),
            ∀ r ∈ b.requests, Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) →
          let input := ComparisonExactContext.rewrite p before
          let bs := unfrozenBindings input (isTotal known)
          let derived := ComparisonParameterization.source input (symbolic bs)
            (bs.map Binding.fresh) (goals (isTotal known) bs)
          ∃ after : CompareSubstitution,
            CompareInstantiates derived after ∧ after.WellShaped p.assumptions ∧
              AlgebraEntailsAll p.assumptions (after.bounds derived.bounds) ∧
              AlgebraSubtype p.assumptions (after.ty derived.body) (.ofTy p.targetType) := by
  obtain ⟨hp, hs, ha, _, hc, _⟩ :=
    prepare_shared_specialization h htarget ht hm he hcover
  refine ⟨hp, ?_⟩
  intro fuel known hk P Q hsupport hatomic
  exact specialized_parameterized_witness hΔ hR hρ h hs ha ht hm hc horder.2
    hsource hbounds htarget (independent_bounded (htarget.mono horder.1 horder.2))
    hk hsupport hatomic

/-- A requested source key makes the actual selected action nonempty, so the
comparison dispatcher enters the resulting specialization branch. -/
theorem independent_nonempty_of_request {p : Prepared} {total : ModExpr → Bool}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (he : ∀ r ∈ collect p total, (CompareTy.ofTy r.1).subst ts ms = .ofTy r.2)
    {r : Request} (hr : r ∈ collect p total)
    (hk : (∃ n, TypeVar.flex n ∈ r.1.typeVars ∧ typeAllowed p (.flex n) = true) ∨
      (∃ n, ModVar.flex n ∈ r.1.modVars ∧ modeAllowed p (.flex n) = true)) :
    ((independent p total).types.isEmpty && (independent p total).modes.isEmpty) = false := by
  have hc := independent_covers ht hm he r hr
  rcases hk with ⟨n, hn, ha⟩ | ⟨n, hn, ha⟩
  · have hh := hc.types n hn ha
    cases ht : (independent p total).types with
    | nil => simp only [ht, List.map_nil, List.not_mem_nil] at hh
    | cons entry entries => simp
  · have hh := hc.modes n hn ha
    cases hm : (independent p total).modes with
    | nil => simp only [hm, List.map_nil, List.not_mem_nil] at hh
    | cons entry entries => simp

end

end ModalityInference.ComparisonFrozenContext
