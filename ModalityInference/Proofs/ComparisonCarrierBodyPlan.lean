import ModalityInference.Proofs.ComparisonPartialCarrierFamilies

namespace ModalityInference.ComparisonPartialCarrier

abbrev publicImage (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) (t : Ty) : CompareTy :=
  (CompareTy.ofTy t).subst ts ms

 theorem Carrier.publicImage_iff {Δ : Bounds} (t : Ty)
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) :
    Carrier Δ (publicImage ts ms t) ↔ ∀ v ∈ t.typeVars, Carrier Δ (ts v) := by
  induction t <;> simp_all only [publicImage, CompareTy.ofTy, CompareTy.subst,
    Carrier, TypeExpr.typeVars, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
    or_imp, false_implies, implies_true, forall_eq, forall_and]

structure BodyRequest where
  name : TypeVar
  lower : Bool
  endpoint : CompareTy

def BodyRequest.Holds (Δ : Bounds) (ts : TypeVar → CompareTy) (r : BodyRequest) : Prop :=
  ComparisonDefinedCovers.Refines Δ r.lower r.endpoint (ts r.name)

/-- A finite, shared-parameter interval presentation of a public type context.
Frozen variables occur under an action for which congruence is unavailable. -/
structure BodyPlan (Δ : Bounds) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (lower : Bool) (body : Ty) (endpoint : CompareTy) where
  requests : List BodyRequest
  frozen : Finset TypeVar
  endpoints : ∀ r ∈ requests, Carrier Δ r.endpoint
  holds : ∀ r ∈ requests, r.Holds Δ ts
  scope : ∀ r ∈ requests, r.name ∈ body.typeVars
  frozen_carrier : ∀ v ∈ frozen, Carrier Δ (ts v)
  frozen_scope : frozen ⊆ body.typeVars
  reconstruct : ∀ us : TypeVar → CompareTy,
    (∀ v ∈ frozen, us v = ts v) → (∀ r ∈ requests, r.Holds Δ us) →
    ComparisonDefinedCovers.Refines Δ lower endpoint (publicImage us ms body)

 def BodyPlan.map {Δ : Bounds} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    {lower lower' : Bool} {body body' : Ty} {endpoint endpoint' : CompareTy}
    (p : BodyPlan Δ ts ms lower body endpoint)
    (hs : body.typeVars ⊆ body'.typeVars)
    (step : ∀ us, ComparisonDefinedCovers.Refines Δ lower endpoint (publicImage us ms body) →
      ComparisonDefinedCovers.Refines Δ lower' endpoint' (publicImage us ms body')) :
    BodyPlan Δ ts ms lower' body' endpoint' where
  requests := p.requests
  frozen := p.frozen
  endpoints := p.endpoints
  holds := p.holds
  scope := fun r hr => hs (p.scope r hr)
  frozen_carrier := p.frozen_carrier
  frozen_scope := fun _ hv => hs (p.frozen_scope hv)
  reconstruct := fun us hf hr => step us (p.reconstruct us hf hr)

 def BodyPlan.combine {Δ : Bounds} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    {lower leftLower rightLower : Bool} {body left right : Ty}
    {endpoint leftEndpoint rightEndpoint : CompareTy}
    (p : BodyPlan Δ ts ms leftLower left leftEndpoint)
    (q : BodyPlan Δ ts ms rightLower right rightEndpoint)
    (hl : left.typeVars ⊆ body.typeVars) (hr : right.typeVars ⊆ body.typeVars)
    (step : ∀ us,
      ComparisonDefinedCovers.Refines Δ leftLower leftEndpoint (publicImage us ms left) →
      ComparisonDefinedCovers.Refines Δ rightLower rightEndpoint (publicImage us ms right) →
      ComparisonDefinedCovers.Refines Δ lower endpoint (publicImage us ms body)) :
    BodyPlan Δ ts ms lower body endpoint where
  requests := p.requests ++ q.requests
  frozen := p.frozen ∪ q.frozen
  endpoints := fun r h => (List.mem_append.mp h).elim (p.endpoints r) (q.endpoints r)
  holds := fun r h => (List.mem_append.mp h).elim (p.holds r) (q.holds r)
  scope := fun r h => (List.mem_append.mp h).elim
    (fun h => hl (p.scope r h)) (fun h => hr (q.scope r h))
  frozen_carrier := fun v h => (Finset.mem_union.mp h).elim (p.frozen_carrier v) (q.frozen_carrier v)
  frozen_scope := fun _ h => (Finset.mem_union.mp h).elim
    (fun h => hl (p.frozen_scope h)) (fun h => hr (q.frozen_scope h))
  reconstruct := fun us hf hreq => step us
    (p.reconstruct us (fun v h => hf v (Finset.mem_union_left _ h))
      (fun r h => hreq r (List.mem_append_left _ h)))
    (q.reconstruct us (fun v h => hf v (Finset.mem_union_right _ h))
      (fun r h => hreq r (List.mem_append_right _ h)))

 def BodyPlan.freeze {Δ : Bounds} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    {lower : Bool} {body : Ty} {endpoint : CompareTy}
    (hc : Carrier Δ (publicImage ts ms body))
    (h : ComparisonDefinedCovers.Refines Δ lower endpoint (publicImage ts ms body)) :
    BodyPlan Δ ts ms lower body endpoint where
  requests := []
  frozen := body.typeVars
  endpoints := by simp
  holds := by simp
  scope := by simp
  frozen_carrier := (Carrier.publicImage_iff body ts ms).mp hc
  frozen_scope := Finset.Subset.refl _
  reconstruct := by
    intro us hf _
    have he : publicImage us ms body = publicImage ts ms body :=
      ComparisonAbsorption.instantiate_congr body hf (fun _ _ => rfl)
    rw [he]
    exact h

end ModalityInference.ComparisonPartialCarrier
