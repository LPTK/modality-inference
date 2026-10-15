import ModalityInference.Proofs.ComparisonPreparedCarrierPlan

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonDefinedCovers ComparisonPartialCovers

def requestDemands (requests : List BodyRequest) (name : TypeVar) (lower : Bool) : List Demand :=
  (requests.filter fun r => r.name == name && r.lower == lower).map
    fun r => ⟨r.endpoint, .epsilon⟩

 theorem mem_requestDemands {requests : List BodyRequest} {name : TypeVar} {lower : Bool}
    {d : Demand} : d ∈ requestDemands requests name lower ↔
    ∃ r ∈ requests, r.name = name ∧ r.lower = lower ∧ d = ⟨r.endpoint, .epsilon⟩ := by
  simp only [requestDemands, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨r, ⟨hr, hn, hl⟩, hd⟩
    exact ⟨r, hr, hn, hl, hd.symm⟩
  · rintro ⟨r, hr, hn, hl, rfl⟩
    exact ⟨r, ⟨hr, hn, hl⟩, rfl⟩

/-- Shared requests for one parameter have a finite carrier join/meet witness. -/
 theorem request_normal_form {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {requests : List BodyRequest} {ts : TypeVar → CompareTy}
    (hc : ∀ r ∈ requests, Carrier Δ r.endpoint)
    (hh : ∀ r ∈ requests, r.Holds Δ ts) (name : TypeVar) :
    ∃ a, a.WellShaped Δ ∧
      FamilyForm Δ (requestDemands requests name true).length
        (requestDemands requests name false).length a ∧
      ∀ r ∈ requests, r.name = name → Refines Δ r.lower r.endpoint a := by
  have hcs : ∀ lower d, d ∈ requestDemands requests name lower → Carrier Δ d.endpoint := by
    intro lower d hd
    obtain ⟨r, hr, _, _, rfl⟩ := mem_requestDemands.mp hd
    exact hc r hr
  have hl : ∀ d ∈ requestDemands requests name true, Lower Δ d (ts name) := by
    intro d hd
    obtain ⟨r, hr, hn, he, rfl⟩ := mem_requestDemands.mp hd
    have hh := hh r hr
    simp only [BodyRequest.Holds, hn, he, Refines, ↓reduceIte] at hh
    exact hh.trans (.identityRev hh.wellShaped_right)
  have hu : ∀ d ∈ requestDemands requests name false, Upper Δ d (ts name) := by
    intro d hd
    obtain ⟨r, hr, hn, he, rfl⟩ := mem_requestDemands.mp hd
    have hh := hh r hr
    simp only [BodyRequest.Holds, hn, he, Refines, Bool.false_eq_true, ↓reduceIte] at hh
    exact (AlgebraSubtype.identity hh.wellShaped_left).trans hh
  obtain ⟨a, hs, hf, hla, hua⟩ := finite_family_normal_form hΔ
    (requestDemands requests name true) (requestDemands requests name false)
    (hcs true) (hcs false) hl hu
  refine ⟨a, hs, hf, ?_⟩
  intro r hr hn
  cases he : r.lower
  · have hmem : (⟨r.endpoint, .epsilon⟩ : Demand) ∈ requestDemands requests name false :=
      mem_requestDemands.mpr ⟨r, hr, hn, he, rfl⟩
    simpa only [he, Refines, Bool.false_eq_true, ↓reduceIte] using
      (AlgebraSubtype.identityRev hs).trans (hua _ hmem)
  · have hmem : (⟨r.endpoint, .epsilon⟩ : Demand) ∈ requestDemands requests name true :=
      mem_requestDemands.mpr ⟨r, hr, hn, he, rfl⟩
    simpa only [he, Refines, ↓reduceIte] using
      (hla _ hmem).trans (AlgebraSubtype.identity hs)

end ModalityInference.ComparisonPartialCarrier
