import ModalityInference.Proofs.ComparisonCapsuleSemanticSpecialization
import ModalityInference.Proofs.ComparisonExactMatchingScope
import ModalityInference.Proofs.ComparisonContextSupport

namespace ModalityInference.ComparisonInstance

/-- The complete literal matching fold retains the original allocation bounds. -/
theorem matchTypes_bounded {p : Prepared} (requests : List (Ty × Ty))
    {before after : Substitution}
    (h : requests.foldlM (fun action r => matchType p r.1 r.2 action) before = some after)
    (ht : ∀ r ∈ requests, r.2.Bounded p.nextType p.nextMode)
    (hb : before.Bounded p.nextType p.nextMode) :
    after.Bounded p.nextType p.nextMode := by
  induction requests generalizing before with
  | nil => cases h; exact hb
  | cons r rs ih =>
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact ih hr (fun r hr => ht r (List.mem_cons_of_mem _ hr))
      (matchType_bounded hl (ht r List.mem_cons_self) hb)

end ModalityInference.ComparisonInstance

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonInstance ComparisonPreparation ComparisonBody ComparisonCapsuleIntervals
open ComparisonInterpolation ComparisonPartialCapsule

noncomputable section
open Classical

/-- Matching shared whole-operand equations yields one bounded specialization
that retains every guard and the body judgment, and covers all semantic frozen
keys before the remaining interval images are changed. -/
theorem matchTypes_prepared_specialization {p : Prepared} {σ : CompareSubstitution}
    (h : PreparedWitness p σ) (requests : List (Ty × Ty))
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hfixed : ∀ r ∈ requests,
      (∀ v ∈ r.2.typeVars, typeAllowed p v = false) ∧
        ∀ v ∈ r.2.modVars, modeAllowed p v = false)
    (hbounded : ∀ r ∈ requests, r.2.Bounded p.nextType p.nextMode)
    (he : ∀ r ∈ requests, (CompareTy.ofTy r.1).subst σ.type σ.mode = .ofTy r.2)
    (hcover : ∀ a ∈ semanticFrozenOperands p.assumptions σ.mode p.sourceType,
      ∃ request ∈ requests, a.typeVars ⊆ request.1.typeVars) :
    ∃ before : Substitution,
      requests.foldlM (fun action r => matchType p r.1 r.2 action) {} = some before ∧
      AgreesWith before σ.type σ.mode ∧ ComparisonExactContext.Scoped p before ∧
      before.Bounded p.nextType p.nextMode ∧
      PreparedWitness (ComparisonExactContext.rewrite p before) σ ∧
      (∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
        (.defined (m.subst σ.mode)))) p.sourceType,
        typeAllowed p v = true → v.index ∈ before.types.map Prod.fst) ∧
      (∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
        (.defined (m.subst σ.mode)))) (before.ty p.sourceType), typeAllowed p v = false) := by
  obtain ⟨before, hh, ha, hs, _, hmatched⟩ := matchTypes_complete_scoped_covers p requests ht hm
    (AgreesWith.empty _ _) (by constructor <;> intro _ _ he <;> cases he) hfixed he
  have hc := matched_semantic_frozen_keys hmatched hcover
  exact ⟨before, hh, ha, hs,
    matchTypes_bounded requests hh hbounded (Substitution.bounded_empty _ _),
    ⟨h.1, h.2.1, (ha.rewrite_bounds hs ht hm _ _).mpr h.2.2.1,
      (ha.rewrite_ty hs ht hm p.sourceType).symm ▸ h.2.2.2⟩,
    hc, specialized_semantic_frozen_fixed hs ha hm hc⟩

/-- One successful matching pass supplies the next actual public comparison.
Every original mode image is retained, and all selected suffixes are interpreted
simultaneously by the same derived-scheme witness. -/
theorem matchTypes_parameterized_witness {p : Prepared} {ρ : TypeVar → ComparisonShape}
    {σ : CompareSubstitution}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    (h : PreparedWitness p σ) (requests : List (Ty × Ty))
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hfixed : ∀ r ∈ requests,
      (∀ v ∈ r.2.typeVars, typeAllowed p v = false) ∧
        ∀ v ∈ r.2.modVars, modeAllowed p v = false)
    (hbounded : ∀ r ∈ requests, r.2.Bounded p.nextType p.nextMode)
    (he : ∀ r ∈ requests, (CompareTy.ofTy r.1).subst σ.type σ.mode = .ofTy r.2)
    (hcover : ∀ a ∈ semanticFrozenOperands p.assumptions σ.mode p.sourceType,
      ∃ request ∈ requests, a.typeVars ⊆ request.1.typeVars)
    (horder : p.firstMode ≤ p.nextMode)
    (hsource : p.sourceType.Bounded p.nextType p.nextMode)
    (hbounds : p.sourceBounds.Bounded p.nextType p.nextMode)
    (htarget : p.targetType.Bounded p.firstType p.firstMode) :
    ∃ before : Substitution,
      requests.foldlM (fun action r => matchType p r.1 r.2 action) {} = some before ∧
      AgreesWith before σ.type σ.mode ∧ ComparisonExactContext.Scoped p before ∧
      before.Bounded p.nextType p.nextMode ∧
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
  obtain ⟨before, hh, ha, hs, hb, _, hc, _⟩ :=
    matchTypes_prepared_specialization h requests ht hm hfixed hbounded he hcover
  refine ⟨before, hh, ha, hs, hb, ?_⟩
  intro fuel known hk P Q hsupport hatomic
  exact specialized_parameterized_witness hΔ hR hρ h hs ha ht hm hc
    horder hsource hbounds htarget hb hk hsupport hatomic

end

end ModalityInference.ComparisonCapsuleContext
