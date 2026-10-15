import ModalityInference.Proofs.ComparisonPreparedCarrierNormalization

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonDefinedCovers ComparisonPreparation

/-- Count occurrences rather than distinct parameters: repeated occurrences can
contribute independent lower and upper interval endpoints. -/
def parameterOccurrences : Ty → Nat
  | .var _ => 1
  | .unit | .credit => 0
  | .prod a b | .sum a b | .fn a b => parameterOccurrences a + parameterOccurrences b
  | .modal a _ => parameterOccurrences a

/-- The interval count is bounded by public input syntax, independently of the
original witness and the derivation used to compare it. -/
theorem body_plans_bounded {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) (body : Ty) :
    ∀ lower endpoint, (publicImage ts ms body).WellShaped Δ →
      InDirection Δ lower (publicImage ts ms body) endpoint →
      ∃ plan : BodyPlan Δ ts ms lower body endpoint,
        plan.requests.length ≤ parameterOccurrences body := by
  induction body with
  | var v =>
      intro lower endpoint hs h
      refine ⟨{
        requests := [⟨v, lower, endpoint⟩]
        frozen := ∅
        endpoints := ?_
        holds := ?_
        scope := ?_
        frozen_carrier := by simp
        frozen_scope := by simp
        reconstruct := ?_ }, Nat.le_refl 1⟩
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact h.carrier
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact h.sound hs
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact Finset.mem_singleton_self _
      · intro us _ hr
        exact hr _ (List.mem_singleton_self _)
  | unit =>
      intro lower endpoint hs h
      exact ⟨BodyPlan.freeze trivial (h.sound hs), Nat.le_refl 0⟩
  | credit =>
      intro lower endpoint hs h
      exact ⟨BodyPlan.freeze trivial (h.sound hs), Nat.le_refl 0⟩
  | prod a b ia ib =>
      intro lower endpoint hs h
      obtain ⟨c, d, hc, hd, hcd⟩ := h.prod_factor hΔ
      obtain ⟨p, hp⟩ := ia lower c hs.1 hc
      obtain ⟨q, hq⟩ := ib lower d hs.2 hd
      refine ⟨p.combine q (fun _ h => Finset.mem_union_left _ h)
        (fun _ h => Finset.mem_union_right _ h)
        (fun _ ha hb => refine_trans hcd (ha.prod hb)), ?_⟩
      simpa only [BodyPlan.combine, List.length_append, parameterOccurrences] using Nat.add_le_add hp hq
  | sum a b ia ib =>
      intro lower endpoint hs h
      obtain ⟨c, d, hc, hd, hcd⟩ := h.sum_factor hΔ
      obtain ⟨p, hp⟩ := ia lower c hs.1 hc
      obtain ⟨q, hq⟩ := ib lower d hs.2 hd
      refine ⟨p.combine q (fun _ h => Finset.mem_union_left _ h)
        (fun _ h => Finset.mem_union_right _ h)
        (fun _ ha hb => refine_trans hcd (ha.sum hb)), ?_⟩
      simpa only [BodyPlan.combine, List.length_append, parameterOccurrences] using Nat.add_le_add hp hq
  | fn a b ia ib =>
      intro lower endpoint hs h
      obtain ⟨c, d, hc, hd, hcd⟩ := h.fn_factor hΔ
      obtain ⟨p, hp⟩ := ia (!lower) c hs.1 hc
      obtain ⟨q, hq⟩ := ib lower d hs.2 hd
      refine ⟨p.combine q (fun _ h => Finset.mem_union_left _ h)
        (fun _ h => Finset.mem_union_right _ h)
        (fun _ ha hb => refine_trans hcd (ha.fn hb)), ?_⟩
      simpa only [BodyPlan.combine, List.length_append, parameterOccurrences] using Nat.add_le_add hp hq
  | modal a m ia =>
      intro lower endpoint hs h
      classical
      by_cases hm : Entails Δ (.defined (m.subst ms))
      · obtain ⟨c, hc, he⟩ := h.modal_factor hΔ hm
        obtain ⟨p, hp⟩ := ia lower c hs hc
        exact ⟨p.map (Finset.Subset.refl _) (fun _ ha =>
          refine_trans he (refine_modal hm ha)), hp⟩
      · exact ⟨BodyPlan.freeze (InDirection.partial_carrier (a := publicImage ts ms a) hm h)
          (h.sound hs), Nat.zero_le _⟩

theorem body_plan_bounded_of_subtype {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr} {body : Ty} {endpoint : CompareTy}
    (hc : Carrier Δ endpoint) (h : AlgebraSubtype Δ (publicImage ts ms body) endpoint) :
    ∃ plan : BodyPlan Δ ts ms false body endpoint,
      plan.requests.length ≤ parameterOccurrences body :=
  body_plans_bounded hΔ ts ms body false endpoint h.wellShaped_left
    ((algebra_related hΔ h).2 _ (denote_self hc h.wellShaped_right).2)

/-- Full prepared witnesses admit outer partial-lattice normal forms with at
most one interval endpoint per public source-parameter occurrence. -/
theorem prepared_bounded_normalized_witness {source target : Scheme} {σ : CompareSubstitution}
    (hσ : PreparedWitness (prepare [] source target) σ) :
    ∃ plan : PreparedPlan (prepare [] source target) σ,
      plan.requests.length ≤ parameterOccurrences (prepare [] source target).sourceType ∧
      ∃ τ : CompareSubstitution, PreparedWitness (prepare [] source target) τ ∧
        τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
        (∀ v ∈ plan.frozen, τ.type v = σ.type v) ∧
        ∀ v, FamilyForm (prepare [] source target).assumptions
          (requestDemands plan.requests v true).length
          (requestDemands plan.requests v false).length (τ.type v) := by
  have hΔ := SchemePreparation.prepared_typeBoundsDefined source target
  obtain ⟨b, hb⟩ := body_plan_bounded_of_subtype hΔ (Carrier.of_public _) hσ.2.2.2
  let plan := b.toPrepared hσ
  exact ⟨plan, hb, plan.normalized_witness hΔ hσ⟩

end ModalityInference.ComparisonPartialCarrier
