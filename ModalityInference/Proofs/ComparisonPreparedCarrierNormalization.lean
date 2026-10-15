import ModalityInference.Proofs.ComparisonCarrierRequestNormalization

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonPreparation ComparisonDefinedCovers

/-- Change images while retaining the exact type-key and modality lists. -/
def reimage (σ : CompareSubstitution) (images : TypeVar → CompareTy) : CompareSubstitution where
  types := (σ.types.map Prod.fst).map fun n => (n, images (.flex n))
  modes := σ.modes

 theorem reimage_keys (σ : CompareSubstitution) (images : TypeVar → CompareTy) :
    (reimage σ images).types.map Prod.fst = σ.types.map Prod.fst := by
  simp only [reimage, List.map_map, Function.comp_def]

private theorem lookup_none_of_not_key {xs : List (Nat × CompareTy)} {n : Nat}
    (h : n ∉ xs.map Prod.fst) : xs.lookup n = none := by
  exact List.lookup_eq_none_iff.mpr fun entry he => bne_iff_ne.mpr fun hn =>
    h (List.mem_map.mpr ⟨entry, he, hn.symm⟩)

 theorem reimage_type_cases (σ : CompareSubstitution) (images : TypeVar → CompareTy)
    (v : TypeVar) : (reimage σ images).type v = images v ∨
      ((reimage σ images).type v = σ.type v ∧ σ.type v = .var v) := by
  cases v with
  | rigid n => exact Or.inr ⟨rfl, rfl⟩
  | flex n =>
    by_cases hn : n ∈ σ.types.map Prod.fst
    · exact Or.inl (by simp only [reimage, CompareSubstitution.type,
        lookup_map_self _ _ hn, Option.getD_some])
    · have hσ := lookup_none_of_not_key hn
      have hτ := lookup_none_of_not_key (show n ∉ (reimage σ images).types.map Prod.fst by
        rwa [reimage_keys])
      exact Or.inr (by simp only [CompareSubstitution.type, hσ, hτ, Option.getD_none, and_self])

 theorem reimage_domainsAbove {σ : CompareSubstitution} {nt nm : Nat}
    (h : σ.DomainsAbove nt nm) (images : TypeVar → CompareTy) :
    (reimage σ images).DomainsAbove nt nm := by
  refine ⟨?_, h.2⟩
  intro entry he
  change entry ∈ (σ.types.map Prod.fst).map (fun n => (n, images (.flex n))) at he
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
  obtain ⟨pair, hp, hpn⟩ := List.mem_map.mp hn
  simpa only [← hpn] using h.1 pair hp

 theorem reimage_wellShaped {σ : CompareSubstitution} {Δ : Bounds}
    {images : TypeVar → CompareTy} (h : ∀ v, (images v).WellShaped Δ) :
    (reimage σ images).WellShaped Δ := by
  intro entry he
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
  exact h (.flex n)

/-- A complete prepared witness can be replaced by one with bounded outer
partial-lattice structure in every image. Modal syntax and parameter domains are
preserved exactly; guarded bounds and frozen partial contexts retain their images. -/
 theorem PreparedPlan.normalized_witness {p : Prepared} {σ : CompareSubstitution}
    (plan : PreparedPlan p σ) (hΔ : p.assumptions.TypeBoundsDefined)
    (hσ : PreparedWitness p σ) :
    ∃ τ : CompareSubstitution, PreparedWitness p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      (∀ v ∈ plan.frozen, τ.type v = σ.type v) ∧
      ∀ v, FamilyForm p.assumptions (requestDemands plan.requests v true).length
        (requestDemands plan.requests v false).length (τ.type v) := by
  classical
  have hchoose : ∀ v, ∃ a, a.WellShaped p.assumptions ∧
      FamilyForm p.assumptions (requestDemands plan.requests v true).length
        (requestDemands plan.requests v false).length a ∧
      (v ∈ plan.frozen → a = σ.type v) ∧
      ∀ r ∈ plan.requests, r.name = v → Refines p.assumptions r.lower r.endpoint a := by
    intro v
    by_cases hv : v ∈ plan.frozen
    · refine ⟨σ.type v, hσ.2.1.type v, .carrier (plan.frozen_carrier v hv),
        fun _ => rfl, ?_⟩
      intro r hr hn
      simpa only [BodyRequest.Holds, hn] using plan.holds r hr
    · obtain ⟨a, hs, hf, hh⟩ := request_normal_form hΔ plan.endpoints plan.holds v
      exact ⟨a, hs, hf, fun h => (hv h).elim, hh⟩
  choose images himages using hchoose
  let τ := reimage σ images
  have hfrozen : ∀ v ∈ plan.frozen, τ.type v = σ.type v := by
    intro v hv
    rcases reimage_type_cases σ images v with h | h
    · exact h.trans ((himages v).2.2.1 hv)
    · exact h.1
  have hrequests : ∀ r ∈ plan.requests, r.Holds p.assumptions τ.type := by
    intro r hr
    change Refines p.assumptions r.lower r.endpoint ((reimage σ images).type r.name)
    rcases reimage_type_cases σ images r.name with h | h
    · rw [h]
      exact (himages r.name).2.2.2 r hr rfl
    · rw [h.1]
      exact plan.holds r hr
  refine ⟨τ, plan.reconstruct τ (reimage_domainsAbove hσ.1 images)
    (reimage_wellShaped fun v => (himages v).1) (fun _ => rfl) hfrozen hrequests,
    reimage_keys σ images, rfl, hfrozen, ?_⟩
  intro v
  rcases reimage_type_cases σ images v with h | h
  · rw [h]
    exact (himages v).2.1
  · rw [h.1, h.2]
    exact .carrier trivial

/-- No extra conditions are required of a witness from actual preparation. -/
theorem prepared_normalized_witness {source target : Scheme} {σ : CompareSubstitution}
    (hσ : PreparedWitness (prepare [] source target) σ) :
    ∃ plan : PreparedPlan (prepare [] source target) σ,
      ∃ τ : CompareSubstitution, PreparedWitness (prepare [] source target) τ ∧
        τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
        (∀ v ∈ plan.frozen, τ.type v = σ.type v) ∧
        ∀ v, FamilyForm (prepare [] source target).assumptions
          (requestDemands plan.requests v true).length
          (requestDemands plan.requests v false).length (τ.type v) := by
  obtain ⟨plan⟩ := prepared_plan_actual hσ
  exact ⟨plan, plan.normalized_witness
    (SchemePreparation.prepared_typeBoundsDefined source target) hσ⟩

end ModalityInference.ComparisonPartialCarrier
