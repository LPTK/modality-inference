import ModalityInference.Proofs.ComparisonPartialCarrierInterpretationModalHelpers

namespace ModalityInference.ComparisonPartialCarrier

 theorem Related.joinLeft {Δ : Bounds} (a b : CompareTy) : Related Δ a (.join a b) := by
  constructor
  · intro c hc
    exact .base ((denote Δ a).lower.carrier _ hc) ((denote Δ a).lower.shaped _ hc) (.inl hc)
  · intro c hc
    exact hc.1

 theorem Related.joinRight {Δ : Bounds} (a b : CompareTy) : Related Δ b (.join a b) := by
  constructor
  · intro c hc
    exact .base ((denote Δ b).lower.carrier _ hc) ((denote Δ b).lower.shaped _ hc) (.inr hc)
  · intro c hc
    exact hc.2

 theorem Related.meetLeft {Δ : Bounds} (a b : CompareTy) : Related Δ (.meet a b) a := by
  constructor
  · intro c hc
    exact hc.1
  · intro c hc
    exact .base ((denote Δ a).upper.carrier _ hc) ((denote Δ a).upper.shaped _ hc) (.inl hc)

 theorem Related.meetRight {Δ : Bounds} (a b : CompareTy) : Related Δ (.meet a b) b := by
  constructor
  · intro c hc
    exact hc.2
  · intro c hc
    exact .base ((denote Δ b).upper.carrier _ hc) ((denote Δ b).upper.shaped _ hc) (.inr hc)

 theorem Related.joinLeast {Δ : Bounds} {a b c : CompareTy}
    (ha : Related Δ a c) (hb : Related Δ b c) : Related Δ (.join a b) c := by
  constructor
  · intro t ht
    exact LowerClosure.lift (denote Δ c).lower (fun x hx => hx.elim (ha.1 x) (hb.1 x)) ht
  · intro t ht
    exact ⟨ha.2 _ ht, hb.2 _ ht⟩

 theorem Related.meetGreatest {Δ : Bounds} {a b c : CompareTy}
    (ha : Related Δ a b) (hb : Related Δ a c) : Related Δ a (.meet b c) := by
  constructor
  · intro t ht
    exact ⟨ha.1 _ ht, hb.1 _ ht⟩
  · intro t ht
    exact UpperClosure.lift (denote Δ a).upper (fun x hx => hx.elim (ha.2 x) (hb.2 x)) ht

noncomputable section
attribute [local instance] Classical.propDecidable

 theorem Related.congr {Δ : Bounds} {a b : CompareTy} {m n : ModExpr}
    (hab : Related Δ a b) (hmn : Submode Δ m n) :
    Related Δ (.modal a m) (.modal b n) := by
  have hm := hmn.defined.1
  have hn := hmn.defined.2
  constructor
  · intro c hc
    simp only [denote, if_pos hm] at hc
    let htarget := (denote Δ (.modal b n)).lower
    apply LowerClosure.lift htarget ?_ hc
    intro t ht
    obtain ⟨u, hu, rfl⟩ := ht
    have hs := (denote Δ a).lower.shaped _ hu
    exact htarget.lower _ _ ((denote Δ a).lower.carrier u hu)
      (.congr (.refl hs) hmn) (denote_modal_lower_mem hn (hab.1 _ hu))
  · intro c hc
    simp only [denote, if_pos hn] at hc
    let htarget := (denote Δ (.modal a m)).upper
    apply UpperClosure.lift htarget ?_ hc
    intro t ht
    obtain ⟨u, hu, rfl⟩ := ht
    have hs := (denote Δ b).upper.shaped _ hu
    exact htarget.upper _ _ ((denote Δ b).upper.carrier u hu)
      (.congr (.refl hs) hmn) (denote_modal_upper_mem hm (hab.2 _ hu))

 theorem Related.fn {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b c d : CompareTy} {m n : ModExpr}
    (hca : Related Δ c a) (hbd : Related Δ b d)
    (hmn : Submode Δ m (.compose n .top)) :
    Related Δ (.modal (.fn a b) m) (.modal (.fn c d) n) := by
  have hm := hmn.defined.1
  have hn := (Entails.defined_compose_iff.mp hmn.defined.2).1
  constructor
  · intro t ht
    have hct := (denote Δ (.modal (.fn a b) m)).lower.carrier t ht
    obtain ⟨q, hq, htq⟩ := denote_modal_lower_factor hΔ hm ht
    obtain ⟨u, v, hu, hv, hquv⟩ :=
      LowerIdeal.fn_factor hΔ (denote Δ a).upper (denote Δ b).lower hq
    have hu' := hca.2 u hu
    have hv' := hbd.1 v hv
    have hcu := (denote Δ c).upper.carrier u hu'
    have hcv := (denote Δ d).lower.carrier v hv'
    have hsu := (denote Δ c).upper.shaped u hu'
    have hsv := (denote Δ d).lower.shaped v hv'
    have huv : (denote Δ (.fn c d)).lower.mem (.fn u v) :=
      .base ⟨hcu, hcv⟩ ⟨hsu, hsv⟩ ⟨u, v, hu', hv', rfl⟩
    exact (denote Δ (.modal (.fn c d) n)).lower.lower t _ hct
      (htq.trans ((AlgebraSubtype.congr hquv (.refl hm)).trans
        (.fn (.refl hsu) (.refl hsv) hmn)))
      (denote_modal_lower_mem hn huv)
  · intro t ht
    have hct := (denote Δ (.modal (.fn c d) n)).upper.carrier t ht
    obtain ⟨q, hq, hqt⟩ := denote_modal_upper_factor hΔ hn ht
    obtain ⟨u, v, hu, hv, huvq⟩ :=
      UpperIdeal.fn_factor hΔ (denote Δ c).lower (denote Δ d).upper hq
    have hu' := hca.1 u hu
    have hv' := hbd.2 v hv
    have hcu := (denote Δ a).lower.carrier u hu'
    have hcv := (denote Δ b).upper.carrier v hv'
    have hsu := (denote Δ a).lower.shaped u hu'
    have hsv := (denote Δ b).upper.shaped v hv'
    have huv : (denote Δ (.fn a b)).upper.mem (.fn u v) :=
      .base ⟨hcu, hcv⟩ ⟨hsu, hsv⟩ ⟨u, v, hu', hv', rfl⟩
    exact (denote Δ (.modal (.fn a b) m)).upper.upper t _ hct
      ((AlgebraSubtype.fn (.refl hsu) (.refl hsv) hmn).trans
        ((AlgebraSubtype.congr huvq (.refl hn)).trans hqt))
      (denote_modal_upper_mem hm huv)

end

end ModalityInference.ComparisonPartialCarrier
