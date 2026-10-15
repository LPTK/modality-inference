import ModalityInference.Proofs.ComparisonDefinedCoverMonotonicity

/-!
# Shared defined interval covers

A nonempty family of defined lower boundaries chooses one lower approximation
of the witness. It satisfies every lower demand and preserves upper demands
through total actions. The dual statement uses the upper approximation.
-/

namespace ModalityInference.ComparisonDefinedCovers

theorem defined_lower_family_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {w : CompareTy} {lowers uppers : List (CompareTy × ModExpr)} (hne : lowers ≠ [])
    (hl : ∀ p ∈ lowers, p.1.DefinedUnder Δ ∧ AlgebraSubtype Δ p.1 (.modal w p.2))
    (hu : ∀ p ∈ uppers, Entails Δ (.defined p.2) ∧ AlgebraSubtype Δ (.modal w p.2) p.1) :
    ∃ c, normal Δ true w = some c ∧ c.DefinedUnder Δ ∧ AlgebraSubtype Δ c w ∧
      (∀ p ∈ lowers, Entails Δ (.defined p.2) ∧ AlgebraSubtype Δ p.1 (.modal c p.2)) ∧
      ∀ p ∈ uppers, AlgebraSubtype Δ (.modal c p.2) p.1 := by
  cases lowers with
  | nil => exact False.elim (hne rfl)
  | cons p ps =>
    have hp := hl p (by simp)
    obtain ⟨_, c, hc, hcd, hcw, _⟩ := defined_lower_modal_cover hΔ hp.1 hp.2
    refine ⟨c, hc, hcd, hcw, ?_, ?_⟩
    · intro q hq
      have hq' := hl q hq
      obtain ⟨hm, d, hd, _, _, hgoal⟩ := defined_lower_modal_cover hΔ hq'.1 hq'.2
      have heq : c = d := Option.some.inj (hc.symm.trans hd)
      subst d
      exact ⟨hm, hgoal⟩
    · intro q hq
      have hq' := hu q hq
      exact (AlgebraSubtype.congr hcw (.refl hq'.1)).trans hq'.2

theorem defined_upper_family_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {w : CompareTy} {lowers uppers : List (CompareTy × ModExpr)} (hne : uppers ≠ [])
    (hl : ∀ p ∈ lowers, Entails Δ (.defined p.2) ∧ AlgebraSubtype Δ p.1 (.modal w p.2))
    (hu : ∀ p ∈ uppers, p.1.DefinedUnder Δ ∧ AlgebraSubtype Δ (.modal w p.2) p.1) :
    ∃ c, normal Δ false w = some c ∧ c.DefinedUnder Δ ∧ AlgebraSubtype Δ w c ∧
      (∀ p ∈ lowers, AlgebraSubtype Δ p.1 (.modal c p.2)) ∧
      ∀ p ∈ uppers, Entails Δ (.defined p.2) ∧ AlgebraSubtype Δ (.modal c p.2) p.1 := by
  cases uppers with
  | nil => exact False.elim (hne rfl)
  | cons p ps =>
    have hp := hu p (by simp)
    obtain ⟨_, c, hc, hcd, hwc, _⟩ := defined_upper_modal_cover hΔ hp.1 hp.2
    refine ⟨c, hc, hcd, hwc, ?_, ?_⟩
    · intro q hq
      have hq' := hl q hq
      exact hq'.2.trans (.congr hwc (.refl hq'.1))
    · intro q hq
      have hq' := hu q hq
      obtain ⟨hm, d, hd, _, _, hgoal⟩ := defined_upper_modal_cover hΔ hq'.1 hq'.2
      have heq : c = d := Option.some.inj (hc.symm.trans hd)
      subst d
      exact ⟨hm, hgoal⟩

end ModalityInference.ComparisonDefinedCovers
