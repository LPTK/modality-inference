import ModalityInference.Proofs.ComparisonPartialCarrierRelation

/-! Introduction and factorization of total modal carrier interpretations. -/

namespace ModalityInference.ComparisonPartialCarrier

noncomputable section

attribute [local instance] Classical.propDecidable

theorem denote_modal_lower_mem {Δ : Bounds} {a b : CompareTy} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hb : (denote Δ a).lower.mem b) :
    (denote Δ (.modal a m)).lower.mem (.modal b m) := by
  simp only [denote, if_pos hm]
  exact .base ((denote Δ a).lower.carrier b hb) ((denote Δ a).lower.shaped b hb) ⟨b, hb, rfl⟩

theorem denote_modal_upper_mem {Δ : Bounds} {a b : CompareTy} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hb : (denote Δ a).upper.mem b) :
    (denote Δ (.modal a m)).upper.mem (.modal b m) := by
  simp only [denote, if_pos hm]
  exact .base ((denote Δ a).upper.carrier b hb) ((denote Δ a).upper.shaped b hb) ⟨b, hb, rfl⟩

theorem denote_modal_lower_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a c : CompareTy} {m : ModExpr} (hm : Entails Δ (.defined m))
    (h : (denote Δ (.modal a m)).lower.mem c) :
    ∃ b, (denote Δ a).lower.mem b ∧ AlgebraSubtype Δ c (.modal b m) := by
  simp only [denote, if_pos hm] at h
  exact LowerIdeal.modal_factor hΔ (denote Δ a).lower (.refl hm) h

theorem denote_modal_upper_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a c : CompareTy} {m : ModExpr} (hm : Entails Δ (.defined m))
    (h : (denote Δ (.modal a m)).upper.mem c) :
    ∃ b, (denote Δ a).upper.mem b ∧ AlgebraSubtype Δ (.modal b m) c := by
  simp only [denote, if_pos hm] at h
  exact UpperIdeal.modal_factor hΔ (denote Δ a).upper (.refl hm) h

end
end ModalityInference.ComparisonPartialCarrier
