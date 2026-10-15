import ModalityInference.Proofs.ComparisonFrozenPeeling

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonBody ComparisonPartialCapsule ComparisonPartialCapsuleScalar

/-- An arbitrary partial action, including compound source images, exposes
the same literal capsule as actual target peeling. Its total suffix remains a
single shared scalar expression. -/
theorem peel_partial_action_equivalent {Δ : Bounds}
    (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (total : ModExpr → Bool)
    (hsound : ∀ n, total n = true → Entails Δ (.defined n))
    {a : CompareTy} {target : Ty} {m : ModExpr}
    (hcomplete : ∀ b n, (peel total target).base = .modal b n →
      Entails Δ (.defined n) → total n = true)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal a m) (.ofTy target) ∨
      AlgebraSubtype Δ (.ofTy target) (.modal a m)) :
    ∃ q, Entails Δ (.defined q) ∧
      AlgebraSubtype Δ (.modal a m) (.modal (.ofTy (peel total target).base) q) ∧
      AlgebraSubtype Δ (.modal (.ofTy (peel total target).base) q) (.modal a m) := by
  have hs : a.WellShaped Δ := h.elim (fun h => h.wellShaped_left) (fun h => h.wellShaped_right)
  obtain ⟨normal⟩ := modal_partial_normal hm hs
  have hf : Frozen Δ normal.token := observe_frozen (.modal a m) (by
    rw [normal.observation]
    exact Set.mem_singleton _)
  have hc : AlgebraSubtype Δ (.modal (.modal normal.token.1 normal.token.2) normal.suffix)
      (.ofTy target) ∨ AlgebraSubtype Δ (.ofTy target)
      (.modal (.modal normal.token.1 normal.token.2) normal.suffix) := by
    rcases h with h | h
    · exact Or.inl ((AlgebraSubtype.shaped normal.backward).trans h)
    · exact Or.inr (h.trans (.shaped normal.forward))
  obtain ⟨b, hb, he⟩ := peel_frozen_stem hΔ hR total hsound hcomplete
    hf.1 hf.2 normal.total hc
  refine ⟨normal.suffix, normal.total, ?_, ?_⟩
  · rw [hb]
    simpa only [CompareTy.ofTy, he] using AlgebraSubtype.shaped normal.forward
  · rw [hb]
    simpa only [CompareTy.ofTy, he] using AlgebraSubtype.shaped normal.backward

end ModalityInference.ComparisonPartialStructuredCapsule
