import ModalityInference.Proofs.ComparisonCarrierBodyReduction
import ModalityInference.Proofs.ComparisonPreparationComplete

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonPreparation

/-- A finite carrier-interval presentation of a prepared witness. Bounds retain
their original images, and the modal action is shared by the entire plan. -/
structure PreparedPlan (p : Prepared) (σ : CompareSubstitution) where
  requests : List BodyRequest
  frozen : Finset TypeVar
  endpoints : ∀ r ∈ requests, Carrier p.assumptions r.endpoint
  holds : ∀ r ∈ requests, r.Holds p.assumptions σ.type
  scope : ∀ r ∈ requests, r.name ∈ p.sourceType.typeVars
  frozen_carrier : ∀ v ∈ frozen, Carrier p.assumptions (σ.type v)
  frozen_scope : frozen ⊆ p.sourceType.typeVars ∪ p.sourceBounds.typeVars
  reconstruct : ∀ τ : CompareSubstitution,
    τ.DomainsAbove p.firstType p.firstMode → τ.WellShaped p.assumptions →
    (∀ v, τ.mode v = σ.mode v) → (∀ v ∈ frozen, τ.type v = σ.type v) →
    (∀ r ∈ requests, r.Holds p.assumptions τ.type) → PreparedWitness p τ

/-- Lift a body interval plan while preserving every guarded source bound. -/
def BodyPlan.toPrepared {p : Prepared} {σ : CompareSubstitution}
    (b : BodyPlan p.assumptions σ.type σ.mode false p.sourceType (.ofTy p.targetType))
    (hσ : PreparedWitness p σ) : PreparedPlan p σ := by
  refine {
    requests := b.requests
    frozen := b.frozen ∪ p.sourceBounds.typeVars
    endpoints := b.endpoints
    holds := b.holds
    scope := b.scope
    frozen_carrier := ?_
    frozen_scope := ?_
    reconstruct := ?_ }
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact b.frozen_carrier v hv
    · exact Carrier.of_defined (hσ.2.2.1.bounds_support_defined.1 v hv)
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (b.frozen_scope hv)
    · exact Finset.mem_union_right _ hv
  · intro τ hd hs hm hf hr
    refine ⟨hd, hs, ?_, ?_⟩
    · apply (CompareSubstitution.algebra_bounds_congr σ τ p.sourceBounds ?_ ?_).mp hσ.2.2.1
      · intro c hc v hv
        exact (hf v (Finset.mem_union_right _
          ((p.sourceBounds.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩))).symm
      · intro _ _ v _
        exact (hm v).symm
    · have hb := b.reconstruct τ.type (fun v hv => hf v (Finset.mem_union_left _ hv)) hr
      change AlgebraSubtype p.assumptions (publicImage τ.type τ.mode p.sourceType) _
      have he : publicImage τ.type τ.mode p.sourceType =
          publicImage τ.type σ.mode p.sourceType :=
        ComparisonAbsorption.instantiate_congr p.sourceType (fun _ _ => rfl) (fun v _ => hm v)
      rw [he]
      exact hb

/-- Every prepared witness admits finite, shared-parameter carrier intervals.
Parameters used by guarded bounds or frozen partial actions retain their images. -/
theorem prepared_plan {p : Prepared} {σ : CompareSubstitution}
    (hΔ : p.assumptions.TypeBoundsDefined) (hσ : PreparedWitness p σ) :
    Nonempty (PreparedPlan p σ) := by
  obtain ⟨b⟩ := body_plan_of_subtype hΔ (Carrier.of_public p.targetType) hσ.2.2.2
  exact ⟨b.toPrepared hσ⟩

/-- Actual scheme preparation provides the context condition needed above. -/
theorem prepared_plan_actual {source target : Scheme} {σ : CompareSubstitution}
    (hσ : PreparedWitness (prepare [] source target) σ) :
    Nonempty (PreparedPlan (prepare [] source target) σ) :=
  prepared_plan (SchemePreparation.prepared_typeBoundsDefined source target) hσ

end ModalityInference.ComparisonPartialCarrier
