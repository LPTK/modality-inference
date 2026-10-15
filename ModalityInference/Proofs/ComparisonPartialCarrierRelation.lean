import ModalityInference.Proofs.ComparisonPartialCarrierInterpretationSoundness
import ModalityInference.Proofs.ComparisonPartialCarrierFactors

namespace ModalityInference.ComparisonPartialCarrier

def Related (Δ : Bounds) (a b : CompareTy) : Prop :=
  (∀ c, (denote Δ a).lower.mem c → (denote Δ b).lower.mem c) ∧
  (∀ c, (denote Δ b).upper.mem c → (denote Δ a).upper.mem c)

theorem Related.refl {Δ : Bounds} (a : CompareTy) : Related Δ a a :=
  ⟨fun _ => id, fun _ => id⟩

theorem Related.trans {Δ : Bounds} {a b c : CompareTy}
    (hab : Related Δ a b) (hbc : Related Δ b c) : Related Δ a c :=
  ⟨fun _ h => hbc.1 _ (hab.1 _ h), fun _ h => hab.2 _ (hbc.2 _ h)⟩

theorem Related.carriers {Δ : Bounds} {a b : CompareTy}
    (ha : Carrier Δ a) (hb : Carrier Δ b) (h : AlgebraSubtype Δ a b) : Related Δ a b := by
  constructor
  · intro c hc
    exact (denote_lower_carrier_iff hb h.wellShaped_right).mpr
      ⟨(denote Δ a).lower.carrier _ hc, ((denote_sound h.wellShaped_left).1 _ hc).trans h⟩
  · intro c hc
    exact (denote_upper_carrier_iff ha h.wellShaped_left).mpr
      ⟨(denote Δ b).upper.carrier _ hc, h.trans ((denote_sound h.wellShaped_right).2 _ hc)⟩

theorem LowerClosure.exists_base {Δ S a} (h : LowerClosure Δ S a) : ∃ b, S b := by
  induction h with
  | base _ _ hS => exact ⟨_, hS⟩
  | lower _ _ _ ih => exact ih
  | join _ _ _ ih _ => exact ih

theorem UpperClosure.exists_base {Δ S a} (h : UpperClosure Δ S a) : ∃ b, S b := by
  induction h with
  | base _ _ hS => exact ⟨_, hS⟩
  | upper _ _ _ ih => exact ih
  | meet _ _ _ ih _ => exact ih

noncomputable section
attribute [local instance] Classical.propDecidable

theorem denote_partial_lower_carrier {Δ : Bounds} {a c : CompareTy} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (h : (denote Δ (.modal a m)).lower.mem c) : Carrier Δ a := by
  simp only [denote, if_neg hm, LowerIdeal.closure] at h
  obtain ⟨_, ha, _⟩ := h.exists_base
  exact ha

theorem denote_partial_upper_carrier {Δ : Bounds} {a c : CompareTy} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (h : (denote Δ (.modal a m)).upper.mem c) : Carrier Δ a := by
  simp only [denote, if_neg hm, UpperIdeal.closure] at h
  obtain ⟨_, ha, _⟩ := h.exists_base
  exact ha

end

end ModalityInference.ComparisonPartialCarrier
