import ModalityInference.Proofs.ComparisonFrozenContext
import ModalityInference.Proofs.ComparisonPartialStemCancellation
import ModalityInference.Proofs.ComparisonExactMatchingCompleteness

namespace ModalityInference.ComparisonPartialStructuredCapsule

theorem frozen_internal_stem_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a : Ty} {b : CompareTy} {m n q r : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (hn : ¬Entails Δ (.defined n))
    (hmc : Noncompose m) (hnc : Noncompose n)
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal (.ofTy a) m) q) (.modal (.modal b n) r)) :
    b = .ofTy a ∧ n = m := by
  have hpartial : ¬Entails Δ (.defined (.compose n r)) :=
    fun hc => hn (Entails.defined_compose_iff.mp hc).1
  have hp : Public b := partial_context_public_above (a := .modal (.modal a m) q) hΔ hpartial
    (h.trans (.shaped (.compose (a := b) (m := n) (n := r) h.wellShaped_right)))
  obtain ⟨c, rfl⟩ := hp
  obtain ⟨rfl, he⟩ := public_frozen_stem_cancel hΔ hR hm hn hmc hnc hq hr h
  exact ⟨rfl, he.symm⟩

end ModalityInference.ComparisonPartialStructuredCapsule

namespace ModalityInference.ComparisonInstance

open ComparisonPartialStructuredCapsule

/-- An exposed frozen request has one literal solution shared by every
occurrence. The total suffixes constrain its order without altering that
solution, even when the source annotation contains compound expressions. -/
theorem matchType_frozen_suffix_complete (p : Prepared) {source target : Ty} {m n q r : ModExpr}
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hf : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (hm : ¬Entails p.assumptions (.defined (m.subst ms)))
    (hn : ¬Entails p.assumptions (.defined n))
    (hmc : Noncompose (m.subst ms)) (hnc : Noncompose n)
    (hq : Entails p.assumptions (.defined q)) (hr : Entails p.assumptions (.defined r))
    (h : AlgebraSubtype p.assumptions
        (.modal (.modal ((CompareTy.ofTy source).subst ts ms) (m.subst ms)) q)
        (.modal (.modal (.ofTy target) n) r) ∨
      AlgebraSubtype p.assumptions (.modal (.modal (.ofTy target) n) r)
        (.modal (.modal ((CompareTy.ofTy source).subst ts ms) (m.subst ms)) q)) :
    ∃ after, matchType p (.modal source m) (.modal target n) before = some after ∧
      AgreesWith after ts ms := by
  have he : (CompareTy.ofTy source).subst ts ms = .ofTy target ∧ m.subst ms = n := by
    rcases h with h | h
    · exact internal_frozen_stem_cancel hΔ hR hm hn hmc hnc hq hr h
    · exact frozen_internal_stem_cancel hΔ hR hn hm hnc hmc hr hq h
  exact matchType_complete p ht hf ha (congrArg₂ CompareTy.modal he.1 he.2)

structure FrozenRequestHolds (Δ : Bounds) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (request : Ty × Ty) where
  source : Ty
  target : Ty
  sourceMode : ModExpr
  targetMode : ModExpr
  sourceSuffix : ModExpr
  targetSuffix : ModExpr
  source_eq : request.1 = .modal source sourceMode
  target_eq : request.2 = .modal target targetMode
  source_partial : ¬Entails Δ (.defined (sourceMode.subst ms))
  target_partial : ¬Entails Δ (.defined targetMode)
  source_noncompose : Noncompose (sourceMode.subst ms)
  target_noncompose : Noncompose targetMode
  source_total : Entails Δ (.defined sourceSuffix)
  target_total : Entails Δ (.defined targetSuffix)
  comparison :
    AlgebraSubtype Δ
      (.modal (.modal ((CompareTy.ofTy source).subst ts ms) (sourceMode.subst ms)) sourceSuffix)
      (.modal (.modal (.ofTy target) targetMode) targetSuffix) ∨
    AlgebraSubtype Δ (.modal (.modal (.ofTy target) targetMode) targetSuffix)
      (.modal (.modal ((CompareTy.ofTy source).subst ts ms) (sourceMode.subst ms)) sourceSuffix)

/-- Simultaneous matching of finitely many exposed contexts preserves the
same original type and modality images across every shared identifier. -/
theorem matchTypes_frozen_suffix_complete (p : Prepared) (requests : List (Ty × Ty))
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (hh : ∀ request ∈ requests, Nonempty (FrozenRequestHolds p.assumptions ts ms request)) :
    ∃ after, requests.foldlM (fun action request => matchType p request.1 request.2 action) before =
      some after ∧ AgreesWith after ts ms := by
  apply matchTypes_complete p requests ht hm ha
  intro request hr
  obtain ⟨h⟩ := hh request hr
  rw [h.source_eq, h.target_eq]
  have he : (CompareTy.ofTy h.source).subst ts ms = .ofTy h.target ∧
      h.sourceMode.subst ms = h.targetMode := by
    rcases h.comparison with hc | hc
    · exact internal_frozen_stem_cancel hΔ hR h.source_partial h.target_partial
        h.source_noncompose h.target_noncompose h.source_total h.target_total hc
    · exact frozen_internal_stem_cancel hΔ hR h.target_partial h.source_partial
        h.target_noncompose h.source_noncompose h.target_total h.source_total hc
  exact congrArg₂ CompareTy.modal he.1 he.2

end ModalityInference.ComparisonInstance
