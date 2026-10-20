import ModalityInference.Proofs.ComparisonRawCarrierModal

/-! Structural carrier transport retains finite closure families when ambient
declared edges contain partial expressions. -/
namespace ModalityInference.ComparisonPartialCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Function variance transports whole carrier closures without selecting one
preimage or requiring guards for the ambient type bounds. -/
theorem Related.fn_general {Δ : Bounds}
    {a b c d : CompareTy} {m n : ModExpr}
    (hca : Related Δ c a) (hbd : Related Δ b d)
    (hmn : Submode Δ m (.compose n .top)) :
    Related Δ (.modal (.fn a b) m) (.modal (.fn c d) n) := by
  have hm := hmn.defined.1
  have hn := (Entails.defined_compose_iff.mp hmn.defined.2).1
  constructor
  · intro t ht
    simp only [denote, if_pos hm] at ht
    apply ht.lift (denote Δ (.modal (.fn c d) n)).lower
    rintro _ ⟨q, hq, rfl⟩
    apply LowerClosure.modal_lift (denote Δ (.modal (.fn c d) n)).lower hm ?_ hq
    rintro _ ⟨u, v, hu, hv, rfl⟩
    exact (denote Δ (.modal (.fn c d) n)).lower.lower _ _
      ⟨(denote Δ a).upper.carrier _ hu, (denote Δ b).lower.carrier _ hv⟩
      (.fn (.refl ((denote Δ a).upper.shaped _ hu))
        (.refl ((denote Δ b).lower.shaped _ hv)) hmn)
      (denote_modal_lower_mem hn (.base
        ⟨(denote Δ a).upper.carrier _ hu, (denote Δ b).lower.carrier _ hv⟩
        ⟨(denote Δ a).upper.shaped _ hu, (denote Δ b).lower.shaped _ hv⟩
        ⟨u, v, hca.2 _ hu, hbd.1 _ hv, rfl⟩))
  · intro t ht
    simp only [denote, if_pos hn] at ht
    apply ht.lift (denote Δ (.modal (.fn a b) m)).upper
    rintro _ ⟨q, hq, rfl⟩
    apply UpperClosure.modal_lift (denote Δ (.modal (.fn a b) m)).upper hn ?_ hq
    rintro _ ⟨u, v, hu, hv, rfl⟩
    exact (denote Δ (.modal (.fn a b) m)).upper.upper _ _
      ⟨(denote Δ c).lower.carrier _ hu, (denote Δ d).upper.carrier _ hv⟩
      (.fn (.refl ((denote Δ c).lower.shaped _ hu))
        (.refl ((denote Δ d).upper.shaped _ hv)) hmn)
      (denote_modal_upper_mem hm (.base
        ⟨(denote Δ c).lower.carrier _ hu, (denote Δ d).upper.carrier _ hv⟩
        ⟨(denote Δ c).lower.shaped _ hu, (denote Δ d).upper.shaped _ hv⟩
        ⟨u, v, hca.1 _ hu, hbd.2 _ hv, rfl⟩))

end
end ModalityInference.ComparisonPartialCarrier
