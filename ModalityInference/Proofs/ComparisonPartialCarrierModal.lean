import ModalityInference.Proofs.ComparisonPartialCarrierInterpretationModalHelpers

/-! Literal modal identity and composition preserve both carrier ideals,
including when either modality is partial. -/
namespace ModalityInference.ComparisonPartialCarrier

theorem Related.identity {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (a : CompareTy) :
    Related Δ (.modal a .epsilon) a := by
  have he : Entails Δ (.defined .epsilon) := by intro _ _; rfl
  constructor
  · intro c hc
    obtain ⟨b, hb, hcb⟩ := denote_modal_lower_factor hΔ he hc
    exact (denote Δ a).lower.lower c b ((denote Δ (.modal a .epsilon)).lower.carrier c hc)
      (hcb.trans (.identity ((denote Δ a).lower.shaped b hb))) hb
  · intro c hc
    exact (denote Δ (.modal a .epsilon)).upper.upper c (.modal c .epsilon)
      ((denote Δ a).upper.carrier c hc) (.identity ((denote Δ a).upper.shaped c hc))
      (denote_modal_upper_mem he hc)

theorem Related.identityRev {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (a : CompareTy) :
    Related Δ a (.modal a .epsilon) := by
  have he : Entails Δ (.defined .epsilon) := by intro _ _; rfl
  constructor
  · intro c hc
    exact (denote Δ (.modal a .epsilon)).lower.lower c (.modal c .epsilon)
      ((denote Δ a).lower.carrier c hc) (.identityRev ((denote Δ a).lower.shaped c hc))
      (denote_modal_lower_mem he hc)
  · intro c hc
    obtain ⟨b, hb, hbc⟩ := denote_modal_upper_factor hΔ he hc
    exact (denote Δ a).upper.upper c b ((denote Δ (.modal a .epsilon)).upper.carrier c hc)
      ((AlgebraSubtype.identityRev ((denote Δ a).upper.shaped b hb)).trans hbc) hb

theorem Related.compose_total {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (a : CompareTy)
    {m n : ModExpr} (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    Related Δ (.modal (.modal a m) n) (.modal a (.compose m n)) ∧
      Related Δ (.modal a (.compose m n)) (.modal (.modal a m) n) := by
  have hmn := Entails.defined_compose_iff.mpr ⟨hm, hn⟩
  constructor <;> constructor
  · intro c hc
    obtain ⟨x, hx, hcx⟩ := denote_modal_lower_factor hΔ hn hc
    obtain ⟨b, hb, hxb⟩ := denote_modal_lower_factor hΔ hm hx
    apply (denote Δ (.modal a (.compose m n))).lower.lower c (.modal b (.compose m n))
      ((denote Δ (.modal (.modal a m) n)).lower.carrier c hc)
    · exact hcx.trans ((AlgebraSubtype.congr hxb (.refl hn)).trans
        (.compose ((denote Δ a).lower.shaped b hb)))
    · exact denote_modal_lower_mem hmn hb
  · intro c hc
    obtain ⟨b, hb, hbc⟩ := denote_modal_upper_factor hΔ hmn hc
    apply (denote Δ (.modal (.modal a m) n)).upper.upper c (.modal (.modal b m) n)
      ((denote Δ (.modal a (.compose m n))).upper.carrier c hc)
    · exact (AlgebraSubtype.compose ((denote Δ a).upper.shaped b hb)).trans hbc
    · exact denote_modal_upper_mem hn (denote_modal_upper_mem hm hb)
  · intro c hc
    obtain ⟨b, hb, hcb⟩ := denote_modal_lower_factor hΔ hmn hc
    apply (denote Δ (.modal (.modal a m) n)).lower.lower c (.modal (.modal b m) n)
      ((denote Δ (.modal a (.compose m n))).lower.carrier c hc)
    · exact hcb.trans (.composeRev ((denote Δ a).lower.shaped b hb))
    · exact denote_modal_lower_mem hn (denote_modal_lower_mem hm hb)
  · intro c hc
    obtain ⟨x, hx, hxc⟩ := denote_modal_upper_factor hΔ hn hc
    obtain ⟨b, hb, hbx⟩ := denote_modal_upper_factor hΔ hm hx
    apply (denote Δ (.modal a (.compose m n))).upper.upper c (.modal b (.compose m n))
      ((denote Δ (.modal (.modal a m) n)).upper.carrier c hc)
    · exact (AlgebraSubtype.composeRev ((denote Δ a).upper.shaped b hb)).trans
        ((AlgebraSubtype.congr hbx (.refl hn)).trans hxc)
    · exact denote_modal_upper_mem hmn hb

theorem Related.compose {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a : CompareTy}
    (hs : a.WellShaped Δ) (m n : ModExpr) :
    Related Δ (.modal (.modal a m) n) (.modal a (.compose m n)) ∧
      Related Δ (.modal a (.compose m n)) (.modal (.modal a m) n) := by
  by_cases ha : Carrier Δ a
  · exact ⟨Related.carriers ha ha (.compose hs), Related.carriers ha ha (.composeRev hs)⟩
  by_cases hmn : Entails Δ (.defined m) ∧ Entails Δ (.defined n)
  · exact Related.compose_total hΔ a hmn.1 hmn.2
  have hc : ¬ Entails Δ (.defined (.compose m n)) := fun h =>
    hmn (Entails.defined_compose_iff.mp h)
  have hnlo : ∀ c, (denote Δ (.modal (.modal a m) n)).lower.mem c → False := by
    intro c h
    by_cases hn : Entails Δ (.defined n)
    · have hm : ¬ Entails Δ (.defined m) := fun hm => hmn ⟨hm, hn⟩
      obtain ⟨b, hb, _⟩ := denote_modal_lower_factor hΔ hn h
      exact ha (denote_partial_lower_carrier hm hb)
    · exact ha (denote_partial_lower_carrier (a := .modal a m) hn h)
  have hnhi : ∀ c, (denote Δ (.modal (.modal a m) n)).upper.mem c → False := by
    intro c h
    by_cases hn : Entails Δ (.defined n)
    · have hm : ¬ Entails Δ (.defined m) := fun hm => hmn ⟨hm, hn⟩
      obtain ⟨b, hb, _⟩ := denote_modal_upper_factor hΔ hn h
      exact ha (denote_partial_upper_carrier hm hb)
    · exact ha (denote_partial_upper_carrier (a := .modal a m) hn h)
  exact ⟨⟨fun c h => False.elim (hnlo c h),
      fun _ h => False.elim (ha (denote_partial_upper_carrier hc h))⟩,
    ⟨fun _ h => False.elim (ha (denote_partial_lower_carrier hc h)),
      fun c h => False.elim (hnhi c h)⟩⟩

end ModalityInference.ComparisonPartialCarrier
