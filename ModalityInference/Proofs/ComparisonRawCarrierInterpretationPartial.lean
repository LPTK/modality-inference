import ModalityInference.Proofs.ComparisonRawCarrierInterpretationStructural

/-! Opaque partial actions preserve literal composition and the inherited
product and sum rules in the capsule-supported ideal interpretation. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonRawCarrierIdeals

noncomputable section
attribute [local instance] Classical.propDecidable

theorem denote_partial_lower_iff {Δ K a m t}
    (hm : ¬Entails Δ (.defined m)) :
    (denote Δ K (.modal a m)).lower.mem t ↔ Derivation Δ K t (.modal a m) := by
  constructor
  · intro h
    simp only [denote, if_neg hm] at h
    exact h.lift _ (.principal _ (.modal a m)) (fun {s} hs _ hshape => by
      obtain ⟨hc, rfl⟩ := hs
      exact .refl hc hshape)
  · intro h
    exact (denote_lower_carrier_iff h.carriers.2 h.shaped.2).mpr h

theorem denote_partial_upper_iff {Δ K a m t}
    (hm : ¬Entails Δ (.defined m)) :
    (denote Δ K (.modal a m)).upper.mem t ↔ Derivation Δ K (.modal a m) t := by
  constructor
  · intro h
    simp only [denote, if_neg hm] at h
    exact h.lift _ (.principal _ (.modal a m)) (fun {s} hs _ hshape => by
      obtain ⟨hc, rfl⟩ := hs
      exact .refl hc hshape)
  · intro h
    exact (denote_upper_carrier_iff h.carriers.1 h.shaped.1).mpr h

theorem Related.prod_partial {Δ K a b c d m}
    (hm : ¬Entails Δ (.defined m))
    (hac : Related Δ K (.modal a m) (.modal c m))
    (hbd : Related Δ K (.modal b m) (.modal d m)) :
    Related Δ K (.modal (.prod a b) m) (.modal (.prod c d) m) := by
  constructor
  · intro t ht
    have h := (denote_partial_lower_iff hm).mp ht
    have hc := carrier_modal_prod.mp h.carriers.2
    have ha := (denote_partial_lower_iff hm).mp
      (hac.1 _ (denote_self hc.1 h.shaped.2.1).1)
    have hb := (denote_partial_lower_iff hm).mp
      (hbd.1 _ (denote_self hc.2 h.shaped.2.2).1)
    exact (denote_partial_lower_iff hm).mpr (h.trans (.prod ha hb))
  · intro t ht
    have h := (denote_partial_upper_iff hm).mp ht
    have hc := carrier_modal_prod.mp h.carriers.1
    have ha := (denote_partial_upper_iff hm).mp
      (hac.2 _ (denote_self hc.1 h.shaped.1.1).2)
    have hb := (denote_partial_upper_iff hm).mp
      (hbd.2 _ (denote_self hc.2 h.shaped.1.2).2)
    exact (denote_partial_upper_iff hm).mpr ((Derivation.prod ha hb).trans h)

theorem Related.sum_partial {Δ K a b c d m}
    (hm : ¬Entails Δ (.defined m))
    (hac : Related Δ K (.modal a m) (.modal c m))
    (hbd : Related Δ K (.modal b m) (.modal d m)) :
    Related Δ K (.modal (.sum a b) m) (.modal (.sum c d) m) := by
  constructor
  · intro t ht
    have h := (denote_partial_lower_iff hm).mp ht
    have hc := carrier_modal_sum.mp h.carriers.2
    have ha := (denote_partial_lower_iff hm).mp
      (hac.1 _ (denote_self hc.1 h.shaped.2.1).1)
    have hb := (denote_partial_lower_iff hm).mp
      (hbd.1 _ (denote_self hc.2 h.shaped.2.2).1)
    exact (denote_partial_lower_iff hm).mpr (h.trans (.sum ha hb))
  · intro t ht
    have h := (denote_partial_upper_iff hm).mp ht
    have hc := carrier_modal_sum.mp h.carriers.1
    have ha := (denote_partial_upper_iff hm).mp
      (hac.2 _ (denote_self hc.1 h.shaped.1.1).2)
    have hb := (denote_partial_upper_iff hm).mp
      (hbd.2 _ (denote_self hc.2 h.shaped.1.2).2)
    exact (denote_partial_upper_iff hm).mpr ((Derivation.sum ha hb).trans h)

theorem Related.identity {Δ K a} : Related Δ K (.modal a .epsilon) a := by
  have hm : Entails Δ (.defined .epsilon) := fun _ _ => rfl
  constructor
  · intro t ht
    obtain ⟨x, hx, htx⟩ := (modal_lower_iff hm).mp ht
    exact (denote Δ K a).lower.lower
      (htx.trans (.identity ((denote Δ K a).lower.carrier hx)
        ((denote Δ K a).lower.shaped hx))) hx
  · intro t ht
    exact (modal_upper_iff hm).mpr ⟨t, ht,
      .identity ((denote Δ K a).upper.carrier ht) ((denote Δ K a).upper.shaped ht)⟩

theorem Related.identityRev {Δ K a} : Related Δ K a (.modal a .epsilon) := by
  have hm : Entails Δ (.defined .epsilon) := fun _ _ => rfl
  constructor
  · intro t ht
    exact (modal_lower_iff hm).mpr ⟨t, ht,
      .identityRev ((denote Δ K a).lower.carrier ht) ((denote Δ K a).lower.shaped ht)⟩
  · intro t ht
    obtain ⟨x, hx, hxt⟩ := (modal_upper_iff hm).mp ht
    exact (denote Δ K a).upper.upper
      ((Derivation.identityRev ((denote Δ K a).upper.carrier hx)
        ((denote Δ K a).upper.shaped hx)).trans hxt) hx

theorem Derivation.compose_right {Δ K a m n t}
    (h : Derivation Δ K t (.modal (.modal a m) n)) :
    Derivation Δ K t (.modal a (.compose m n)) :=
  h.trans (.atom h.carriers.2 (carrier_compose.mpr h.carriers.2) (.compose h.shaped.2))

theorem Derivation.composeRev_right {Δ K a m n t}
    (h : Derivation Δ K t (.modal a (.compose m n))) :
    Derivation Δ K t (.modal (.modal a m) n) :=
  h.trans (.atom h.carriers.2 (carrier_compose.mp h.carriers.2) (.composeRev h.shaped.2))

theorem Derivation.compose_left {Δ K a m n t}
    (h : Derivation Δ K (.modal a (.compose m n)) t) :
    Derivation Δ K (.modal (.modal a m) n) t :=
  (Derivation.atom (carrier_compose.mp h.carriers.1) h.carriers.1 (.compose h.shaped.1)).trans h

theorem Derivation.composeRev_left {Δ K a m n t}
    (h : Derivation Δ K (.modal (.modal a m) n) t) :
    Derivation Δ K (.modal a (.compose m n)) t :=
  (Derivation.atom (carrier_compose.mpr h.carriers.1) h.carriers.1 (.composeRev h.shaped.1)).trans h

theorem denote_compose_lower {Δ K a m n t} :
    (denote Δ K (.modal (.modal a m) n)).lower.mem t ↔
      (denote Δ K (.modal a (.compose m n))).lower.mem t := by
  by_cases hn : Entails Δ (.defined n)
  · by_cases hm : Entails Δ (.defined m)
    · have hmn := Entails.defined_compose_iff.mpr ⟨hm, hn⟩
      rw [modal_lower_iff hn, modal_lower_iff hmn]
      constructor
      · rintro ⟨x, hx, htx⟩
        obtain ⟨y, hy, hxy⟩ := (modal_lower_iff hm).mp hx
        exact ⟨y, hy, (htx.trans (hxy.congr (.refl hn))).compose_right⟩
      · rintro ⟨y, hy, hty⟩
        exact ⟨.modal y m, modal_lower_mem hm hy, hty.composeRev_right⟩
    · have hmn : ¬Entails Δ (.defined (.compose m n)) :=
        fun h => hm (Entails.defined_compose_iff.mp h).1
      rw [modal_lower_iff hn, denote_partial_lower_iff hmn]
      constructor
      · rintro ⟨x, hx, htx⟩
        exact (htx.trans (((denote_partial_lower_iff hm).mp hx).congr (.refl hn))).compose_right
      · intro h
        have h' := h.composeRev_right
        exact ⟨.modal a m,
          (denote_self ((carrier_modal_total hn).mp h'.carriers.2) h'.shaped.2).1, h'⟩
  · have hmn : ¬Entails Δ (.defined (.compose m n)) :=
      fun h => hn (Entails.defined_compose_iff.mp h).2
    rw [denote_partial_lower_iff hn, denote_partial_lower_iff hmn]
    exact ⟨Derivation.compose_right, Derivation.composeRev_right⟩

theorem denote_compose_upper {Δ K a m n t} :
    (denote Δ K (.modal (.modal a m) n)).upper.mem t ↔
      (denote Δ K (.modal a (.compose m n))).upper.mem t := by
  by_cases hn : Entails Δ (.defined n)
  · by_cases hm : Entails Δ (.defined m)
    · have hmn := Entails.defined_compose_iff.mpr ⟨hm, hn⟩
      rw [modal_upper_iff hn, modal_upper_iff hmn]
      constructor
      · rintro ⟨x, hx, hxt⟩
        obtain ⟨y, hy, hyx⟩ := (modal_upper_iff hm).mp hx
        exact ⟨y, hy, ((hyx.congr (.refl hn)).trans hxt).composeRev_left⟩
      · rintro ⟨y, hy, hyt⟩
        exact ⟨.modal y m, modal_upper_mem hm hy, hyt.compose_left⟩
    · have hmn : ¬Entails Δ (.defined (.compose m n)) :=
        fun h => hm (Entails.defined_compose_iff.mp h).1
      rw [modal_upper_iff hn, denote_partial_upper_iff hmn]
      constructor
      · rintro ⟨x, hx, hxt⟩
        exact ((((denote_partial_upper_iff hm).mp hx).congr (.refl hn)).trans hxt).composeRev_left
      · intro h
        have h' := h.compose_left
        exact ⟨.modal a m,
          (denote_self ((carrier_modal_total hn).mp h'.carriers.1) h'.shaped.1).2, h'⟩
  · have hmn : ¬Entails Δ (.defined (.compose m n)) :=
      fun h => hn (Entails.defined_compose_iff.mp h).2
    rw [denote_partial_upper_iff hn, denote_partial_upper_iff hmn]
    exact ⟨Derivation.composeRev_left, Derivation.compose_left⟩

theorem Related.compose {Δ K a m n} :
    Related Δ K (.modal (.modal a m) n) (.modal a (.compose m n)) :=
  ⟨fun _ h => denote_compose_lower.mp h, fun _ h => denote_compose_upper.mpr h⟩

theorem Related.composeRev {Δ K a m n} :
    Related Δ K (.modal a (.compose m n)) (.modal (.modal a m) n) :=
  ⟨fun _ h => denote_compose_lower.mpr h, fun _ h => denote_compose_upper.mp h⟩

end
end ModalityInference.ComparisonRawCarrierRestriction
