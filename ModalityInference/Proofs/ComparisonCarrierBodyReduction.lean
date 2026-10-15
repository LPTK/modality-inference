import ModalityInference.Proofs.ComparisonCarrierBodyPlan

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonDefinedCovers

/-- Membership in the carrier ideal for the indicated comparison polarity. -/
def InDirection (Δ : Bounds) (lower : Bool) (a endpoint : CompareTy) : Prop :=
  if lower then (denote Δ a).lower.mem endpoint else (denote Δ a).upper.mem endpoint

 theorem InDirection.carrier {Δ : Bounds} {lower : Bool} {a endpoint : CompareTy}
    (h : InDirection Δ lower a endpoint) : Carrier Δ endpoint := by
  cases lower
  · exact (denote Δ a).upper.carrier _ h
  · exact (denote Δ a).lower.carrier _ h

 theorem InDirection.sound {Δ : Bounds} {lower : Bool} {a endpoint : CompareTy}
    (hs : a.WellShaped Δ) (h : InDirection Δ lower a endpoint) :
    Refines Δ lower endpoint a := by
  cases lower
  · exact (denote_sound hs).2 _ h
  · exact (denote_sound hs).1 _ h

 theorem refine_trans {Δ : Bounds} {lower : Bool} {a b c : CompareTy}
    (hab : Refines Δ lower a b) (hbc : Refines Δ lower b c) :
    Refines Δ lower a c := by
  cases lower
  · exact hbc.trans hab
  · exact hab.trans hbc

 theorem InDirection.prod_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {lower : Bool} {a b endpoint : CompareTy} (h : InDirection Δ lower (.prod a b) endpoint) :
    ∃ c d, InDirection Δ lower a c ∧ InDirection Δ lower b d ∧
      Refines Δ lower endpoint (.prod c d) := by
  cases lower
  · exact UpperIdeal.prod_factor hΔ (denote Δ a).upper (denote Δ b).upper h
  · exact LowerIdeal.prod_factor hΔ (denote Δ a).lower (denote Δ b).lower h

 theorem InDirection.sum_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {lower : Bool} {a b endpoint : CompareTy} (h : InDirection Δ lower (.sum a b) endpoint) :
    ∃ c d, InDirection Δ lower a c ∧ InDirection Δ lower b d ∧
      Refines Δ lower endpoint (.sum c d) := by
  cases lower
  · exact UpperIdeal.sum_factor hΔ (denote Δ a).upper (denote Δ b).upper h
  · exact LowerIdeal.sum_factor hΔ (denote Δ a).lower (denote Δ b).lower h

 theorem InDirection.fn_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {lower : Bool} {a b endpoint : CompareTy} (h : InDirection Δ lower (.fn a b) endpoint) :
    ∃ c d, InDirection Δ (!lower) a c ∧ InDirection Δ lower b d ∧
      Refines Δ lower endpoint (.fn c d) := by
  cases lower
  · exact UpperIdeal.fn_factor hΔ (denote Δ a).lower (denote Δ b).upper h
  · exact LowerIdeal.fn_factor hΔ (denote Δ a).upper (denote Δ b).lower h

 theorem InDirection.modal_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {lower : Bool} {a endpoint : CompareTy} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (h : InDirection Δ lower (.modal a m) endpoint) :
    ∃ c, InDirection Δ lower a c ∧ Refines Δ lower endpoint (.modal c m) := by
  cases lower
  · exact denote_modal_upper_factor hΔ hm h
  · exact denote_modal_lower_factor hΔ hm h

 theorem InDirection.partial_carrier {Δ : Bounds} {lower : Bool}
    {a endpoint : CompareTy} {m : ModExpr} (hm : ¬Entails Δ (.defined m))
    (h : InDirection Δ lower (.modal a m) endpoint) : Carrier Δ a := by
  cases lower
  · exact denote_partial_upper_carrier hm h
  · exact denote_partial_lower_carrier hm h

 theorem refine_modal {Δ : Bounds} {lower : Bool} {a b : CompareTy} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (h : Refines Δ lower a b) :
    Refines Δ lower (.modal a m) (.modal b m) := by
  cases lower <;> exact AlgebraSubtype.congr h (.refl hm)

/-- Every public type context has a finite carrier-interval presentation under
an arbitrary fixed modal substitution. Repeated parameters share their requests;
images below a partial action are retained literally. -/
 theorem body_plans {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) (body : Ty) :
    ∀ lower endpoint, (publicImage ts ms body).WellShaped Δ →
      InDirection Δ lower (publicImage ts ms body) endpoint →
      Nonempty (BodyPlan Δ ts ms lower body endpoint) := by
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
        reconstruct := ?_ }⟩
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
      exact ⟨BodyPlan.freeze trivial (h.sound hs)⟩
  | credit =>
      intro lower endpoint hs h
      exact ⟨BodyPlan.freeze trivial (h.sound hs)⟩
  | prod a b ia ib =>
      intro lower endpoint hs h
      obtain ⟨c, d, hc, hd, hcd⟩ := h.prod_factor hΔ
      obtain ⟨p⟩ := ia lower c hs.1 hc
      obtain ⟨q⟩ := ib lower d hs.2 hd
      exact ⟨p.combine q (fun _ h => Finset.mem_union_left _ h)
        (fun _ h => Finset.mem_union_right _ h)
        (fun _ ha hb => refine_trans hcd (ha.prod hb))⟩
  | sum a b ia ib =>
      intro lower endpoint hs h
      obtain ⟨c, d, hc, hd, hcd⟩ := h.sum_factor hΔ
      obtain ⟨p⟩ := ia lower c hs.1 hc
      obtain ⟨q⟩ := ib lower d hs.2 hd
      exact ⟨p.combine q (fun _ h => Finset.mem_union_left _ h)
        (fun _ h => Finset.mem_union_right _ h)
        (fun _ ha hb => refine_trans hcd (ha.sum hb))⟩
  | fn a b ia ib =>
      intro lower endpoint hs h
      obtain ⟨c, d, hc, hd, hcd⟩ := h.fn_factor hΔ
      obtain ⟨p⟩ := ia (!lower) c hs.1 hc
      obtain ⟨q⟩ := ib lower d hs.2 hd
      exact ⟨p.combine q (fun _ h => Finset.mem_union_left _ h)
        (fun _ h => Finset.mem_union_right _ h)
        (fun _ ha hb => refine_trans hcd (ha.fn hb))⟩
  | modal a m ia =>
      intro lower endpoint hs h
      classical
      by_cases hm : Entails Δ (.defined (m.subst ms))
      · obtain ⟨c, hc, he⟩ := h.modal_factor hΔ hm
        obtain ⟨p⟩ := ia lower c hs hc
        exact ⟨p.map (Finset.Subset.refl _) (fun _ ha =>
          refine_trans he (refine_modal hm ha))⟩
      · exact ⟨BodyPlan.freeze (InDirection.partial_carrier (a := publicImage ts ms a) hm h)
          (h.sound hs)⟩

 theorem body_plan_of_subtype {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr} {body : Ty} {endpoint : CompareTy}
    (hc : Carrier Δ endpoint) (h : AlgebraSubtype Δ (publicImage ts ms body) endpoint) :
    Nonempty (BodyPlan Δ ts ms false body endpoint) :=
  body_plans hΔ ts ms body false endpoint h.wellShaped_left
    ((algebra_related hΔ h).2 _ (denote_self hc h.wellShaped_right).2)

 theorem body_plan_of_supertype {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr} {body : Ty} {endpoint : CompareTy}
    (hc : Carrier Δ endpoint) (h : AlgebraSubtype Δ endpoint (publicImage ts ms body)) :
    Nonempty (BodyPlan Δ ts ms true body endpoint) :=
  body_plans hΔ ts ms body true endpoint h.wellShaped_right
    ((algebra_related hΔ h).1 _ (denote_self hc h.wellShaped_left).1)

end ModalityInference.ComparisonPartialCarrier
