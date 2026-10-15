import ModalityInference.Proofs.ComparisonPartialCarrierInterpretationModalHelpers

/-! Structural carrier comparisons preserve arbitrary outer annotations. Total
annotations factor through carrier ideals; partial annotations retain their
literal structural context. -/

namespace ModalityInference.ComparisonPartialCarrier

noncomputable section

attribute [local instance] Classical.propDecidable

theorem Related.prod {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b c d : CompareTy} {m : ModExpr}
    (hac : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (hbd : AlgebraSubtype Δ (.modal b m) (.modal d m))
    (rac : Related Δ (.modal a m) (.modal c m))
    (rbd : Related Δ (.modal b m) (.modal d m)) :
    Related Δ (.modal (.prod a b) m) (.modal (.prod c d) m) := by
  by_cases hm : Entails Δ (.defined m)
  · constructor
    · intro x hx
      obtain ⟨w, hw, hxw⟩ := denote_modal_lower_factor hΔ hm hx
      obtain ⟨u, v, hu, hv, hwuv⟩ :=
        LowerIdeal.prod_factor hΔ (denote Δ a).lower (denote Δ b).lower hw
      obtain ⟨u', hu', huu'⟩ := denote_modal_lower_factor hΔ hm (rac.1 _ (denote_modal_lower_mem hm hu))
      obtain ⟨v', hv', hvv'⟩ := denote_modal_lower_factor hΔ hm (rbd.1 _ (denote_modal_lower_mem hm hv))
      have huv : (denote Δ (.prod c d)).lower.mem (.prod u' v') :=
        .base ⟨(denote Δ c).lower.carrier _ hu', (denote Δ d).lower.carrier _ hv'⟩
          ⟨(denote Δ c).lower.shaped _ hu', (denote Δ d).lower.shaped _ hv'⟩ ⟨u', v', hu', hv', rfl⟩
      exact (denote Δ (.modal (.prod c d) m)).lower.lower x _
        ((denote Δ (.modal (.prod a b) m)).lower.carrier _ hx)
        (hxw.trans ((AlgebraSubtype.congr hwuv (.refl hm)).trans (.prod huu' hvv')))
        (denote_modal_lower_mem hm huv)
    · intro x hx
      obtain ⟨w, hw, hwx⟩ := denote_modal_upper_factor hΔ hm hx
      obtain ⟨u, v, hu, hv, huv_w⟩ :=
        UpperIdeal.prod_factor hΔ (denote Δ c).upper (denote Δ d).upper hw
      obtain ⟨u', hu', hu'u⟩ := denote_modal_upper_factor hΔ hm (rac.2 _ (denote_modal_upper_mem hm hu))
      obtain ⟨v', hv', hv'v⟩ := denote_modal_upper_factor hΔ hm (rbd.2 _ (denote_modal_upper_mem hm hv))
      have huv : (denote Δ (.prod a b)).upper.mem (.prod u' v') :=
        .base ⟨(denote Δ a).upper.carrier _ hu', (denote Δ b).upper.carrier _ hv'⟩
          ⟨(denote Δ a).upper.shaped _ hu', (denote Δ b).upper.shaped _ hv'⟩ ⟨u', v', hu', hv', rfl⟩
      exact (denote Δ (.modal (.prod a b) m)).upper.upper x _
        ((denote Δ (.modal (.prod c d) m)).upper.carrier _ hx)
        ((AlgebraSubtype.prod hu'u hv'v).trans ((AlgebraSubtype.congr huv_w (.refl hm)).trans hwx))
        (denote_modal_upper_mem hm huv)
  · constructor
    · intro x hx
      have hab := denote_partial_lower_carrier hm hx
      have hc := denote_partial_lower_carrier hm
        (rac.1 _ (denote_self (a := .modal a m) hab.1 hac.wellShaped_left).1)
      have hd := denote_partial_lower_carrier hm
        (rbd.1 _ (denote_self (a := .modal b m) hab.2 hbd.wellShaped_left).1)
      exact (Related.carriers (a := .modal (.prod a b) m) (b := .modal (.prod c d) m)
        hab ⟨hc, hd⟩ (.prod hac hbd)).1 x hx
    · intro x hx
      have hcd := denote_partial_upper_carrier hm hx
      have ha := denote_partial_upper_carrier hm
        (rac.2 _ (denote_self (a := .modal c m) hcd.1 hac.wellShaped_right).2)
      have hb := denote_partial_upper_carrier hm
        (rbd.2 _ (denote_self (a := .modal d m) hcd.2 hbd.wellShaped_right).2)
      exact (Related.carriers (a := .modal (.prod a b) m) (b := .modal (.prod c d) m)
        ⟨ha, hb⟩ hcd (.prod hac hbd)).2 x hx


theorem Related.sum {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b c d : CompareTy} {m : ModExpr}
    (hac : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (hbd : AlgebraSubtype Δ (.modal b m) (.modal d m))
    (rac : Related Δ (.modal a m) (.modal c m))
    (rbd : Related Δ (.modal b m) (.modal d m)) :
    Related Δ (.modal (.sum a b) m) (.modal (.sum c d) m) := by
  by_cases hm : Entails Δ (.defined m)
  · constructor
    · intro x hx
      obtain ⟨w, hw, hxw⟩ := denote_modal_lower_factor hΔ hm hx
      obtain ⟨u, v, hu, hv, hwuv⟩ :=
        LowerIdeal.sum_factor hΔ (denote Δ a).lower (denote Δ b).lower hw
      obtain ⟨u', hu', huu'⟩ := denote_modal_lower_factor hΔ hm (rac.1 _ (denote_modal_lower_mem hm hu))
      obtain ⟨v', hv', hvv'⟩ := denote_modal_lower_factor hΔ hm (rbd.1 _ (denote_modal_lower_mem hm hv))
      have huv : (denote Δ (.sum c d)).lower.mem (.sum u' v') :=
        .base ⟨(denote Δ c).lower.carrier _ hu', (denote Δ d).lower.carrier _ hv'⟩
          ⟨(denote Δ c).lower.shaped _ hu', (denote Δ d).lower.shaped _ hv'⟩ ⟨u', v', hu', hv', rfl⟩
      exact (denote Δ (.modal (.sum c d) m)).lower.lower x _
        ((denote Δ (.modal (.sum a b) m)).lower.carrier _ hx)
        (hxw.trans ((AlgebraSubtype.congr hwuv (.refl hm)).trans (.sum huu' hvv')))
        (denote_modal_lower_mem hm huv)
    · intro x hx
      obtain ⟨w, hw, hwx⟩ := denote_modal_upper_factor hΔ hm hx
      obtain ⟨u, v, hu, hv, huv_w⟩ :=
        UpperIdeal.sum_factor hΔ (denote Δ c).upper (denote Δ d).upper hw
      obtain ⟨u', hu', hu'u⟩ := denote_modal_upper_factor hΔ hm (rac.2 _ (denote_modal_upper_mem hm hu))
      obtain ⟨v', hv', hv'v⟩ := denote_modal_upper_factor hΔ hm (rbd.2 _ (denote_modal_upper_mem hm hv))
      have huv : (denote Δ (.sum a b)).upper.mem (.sum u' v') :=
        .base ⟨(denote Δ a).upper.carrier _ hu', (denote Δ b).upper.carrier _ hv'⟩
          ⟨(denote Δ a).upper.shaped _ hu', (denote Δ b).upper.shaped _ hv'⟩ ⟨u', v', hu', hv', rfl⟩
      exact (denote Δ (.modal (.sum a b) m)).upper.upper x _
        ((denote Δ (.modal (.sum c d) m)).upper.carrier _ hx)
        ((AlgebraSubtype.sum hu'u hv'v).trans ((AlgebraSubtype.congr huv_w (.refl hm)).trans hwx))
        (denote_modal_upper_mem hm huv)
  · constructor
    · intro x hx
      have hab := denote_partial_lower_carrier hm hx
      have hc := denote_partial_lower_carrier hm
        (rac.1 _ (denote_self (a := .modal a m) hab.1 hac.wellShaped_left).1)
      have hd := denote_partial_lower_carrier hm
        (rbd.1 _ (denote_self (a := .modal b m) hab.2 hbd.wellShaped_left).1)
      exact (Related.carriers (a := .modal (.sum a b) m) (b := .modal (.sum c d) m)
        hab ⟨hc, hd⟩ (.sum hac hbd)).1 x hx
    · intro x hx
      have hcd := denote_partial_upper_carrier hm hx
      have ha := denote_partial_upper_carrier hm
        (rac.2 _ (denote_self (a := .modal c m) hcd.1 hac.wellShaped_right).2)
      have hb := denote_partial_upper_carrier hm
        (rbd.2 _ (denote_self (a := .modal d m) hcd.2 hbd.wellShaped_right).2)
      exact (Related.carriers (a := .modal (.sum a b) m) (b := .modal (.sum c d) m)
        ⟨ha, hb⟩ hcd (.sum hac hbd)).2 x hx

end
end ModalityInference.ComparisonPartialCarrier
