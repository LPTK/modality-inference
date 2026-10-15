import ModalityInference.Proofs.ComparisonFrozenContextCompleteness
import ModalityInference.Proofs.ComparisonCapsuleTotality

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonStructuralProjection ComparisonCapsuleIntervals ComparisonBody

theorem partial_suffix_not_defined {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} {m q : ModExpr} (hm : ¬Entails Δ (.defined m))
    (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ (.modal (.modal a m) q) b ∨
      AlgebraSubtype Δ b (.modal (.modal a m) q)) : False := by
  rcases h with h | h
  · have hc := (AlgebraSubtype.composeRev (a := a) (m := m) (n := q)
      h.wellShaped_left).trans h
    exact hm (Entails.defined_compose_iff.mp
      (ComparisonDefinedCovers.defined_upper_modal_cover hΔ hb hc).1).1
  · have hc := h.trans (AlgebraSubtype.compose (a := a) (m := m) (n := q)
      h.wellShaped_right)
    exact hm (Entails.defined_compose_iff.mp
      (ComparisonDefinedCovers.defined_lower_modal_cover hΔ hb hc).1).1

/-- A partial outer action cannot be represented only by annotations inside
the children of a public structural constructor. Its public boundary has an
outer annotation as well. -/
theorem partial_suffix_target_modal {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a : CompareTy} {target : Ty} {m q r : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal a m) q) (.modal (.ofTy target) r) ∨
      AlgebraSubtype Δ (.modal (.ofTy target) r) (.modal (.modal a m) q)) :
    ∃ b n, target = .modal b n := by
  have impossible {kind : Nat} (hk : kind ≠ 0)
      (ht : rootTag (CompareTy.ofTy target).shape = kind)
      (hp : rootType kind (.ofTy target) = rootBase kind) : False := by
    apply partial_suffix_not_defined hΔ hm
      (CompareTy.definedUnder_modal_iff.mpr ⟨rootBase_defined Δ kind, hr⟩)
    rcases h with h | h
    · have ha := (rootTag_equivalent hR h.shape_equivalent).trans ht
      have hh := algebra_rootType hR h hk ha
      simpa only [rootType, hp] using Or.inl hh
    · have hh := algebra_rootType hR h hk ht
      simpa only [rootType, hp] using Or.inr hh
  cases target with
  | modal b n => exact ⟨b, n, rfl⟩
  | var v | unit | credit =>
    exact (partial_suffix_not_defined hΔ hm
      (CompareTy.definedUnder_modal_iff.mpr ⟨by
        intro η hη c hc
        exact (List.not_mem_nil hc).elim, hr⟩) h).elim
  | prod b c => exact (impossible (kind := 3) (by decide) rfl rfl).elim
  | sum b c => exact (impossible (kind := 4) (by decide) rfl rfl).elim
  | fn b c => exact (impossible (kind := 5) (by decide) rfl rfl).elim

/-- Actual target peeling exposes the exact frozen source operand and mode.
The source operand may be any internal comparison type. -/
theorem peel_frozen_stem {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    (total : ModExpr → Bool)
    (hsound : ∀ n, total n = true → Entails Δ (.defined n))
    {a : CompareTy} {target : Ty} {m q : ModExpr}
    (hcomplete : ∀ b n, (peel total target).base = .modal b n →
      Entails Δ (.defined n) → total n = true)
    (hm : ¬Entails Δ (.defined m)) (hn : Noncompose m)
    (hq : Entails Δ (.defined q))
    (h : AlgebraSubtype Δ (.modal (.modal a m) q) (.ofTy target) ∨
      AlgebraSubtype Δ (.ofTy target) (.modal (.modal a m) q)) :
    ∃ b, (peel total target).base = .modal b m ∧ a = .ofTy b := by
  let parsed := peel total target
  let r := ComparisonPartialModes.recompose parsed.labels
  have hr : Entails Δ (.defined r) := recompose_total _
    (fun n hn => hsound n (peelFuel_labels_total total _ target n hn))
  have heq := peel_correct total (fun n hn => Submode.refl (hsound n hn)) target
  have hc : AlgebraSubtype Δ (.modal (.modal a m) q) (.modal (.ofTy parsed.base) r) ∨
      AlgebraSubtype Δ (.modal (.ofTy parsed.base) r) (.modal (.modal a m) q) := by
    rcases h with h | h
    · exact Or.inl (h.trans (.shaped heq.1.to_shaped))
    · exact Or.inr ((AlgebraSubtype.shaped heq.2.to_shaped).trans h)
  obtain ⟨b, n, hb⟩ := partial_suffix_target_modal hΔ hR hm hr hc
  have hstop := peel_stopped total target
  change Stopped total parsed.base at hstop
  rw [hb] at hstop
  have hpartial : ¬Entails Δ (.defined n) := by
    intro hd
    exact Bool.false_ne_true (hstop.2.symm.trans (hcomplete b n hb hd))
  have hexact : a = .ofTy b ∧ m = n := by
    rw [hb] at hc
    rcases hc with hc | hc
    · exact internal_frozen_stem_cancel hΔ hR hm hpartial hn hstop.1.2 hq hr hc
    · have he := frozen_internal_stem_cancel hΔ hR hpartial hm hstop.1.2 hn hr hq hc
      exact he
  exact ⟨b, hexact.2 ▸ hb, hexact.1⟩

end ModalityInference.ComparisonPartialStructuredCapsule

namespace ModalityInference.ComparisonInstance

open ComparisonBody ComparisonPartialStructuredCapsule

/-- A semantic frozen comparison determines the actual target-peeling match,
without guessing the target stem or the internal source image. -/
theorem matchType_peel_frozen_complete (p : Prepared) (total : ModExpr → Bool)
    {source target : Ty} {m q : ModExpr} {before : Substitution}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hf : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (hsound : ∀ n, total n = true → Entails p.assumptions (.defined n))
    (hcomplete : ∀ b n, (peel total target).base = .modal b n →
      Entails p.assumptions (.defined n) → total n = true)
    (hm : ¬Entails p.assumptions (.defined (m.subst ms)))
    (hn : Noncompose (m.subst ms)) (hq : Entails p.assumptions (.defined q))
    (h : AlgebraSubtype p.assumptions
        (.modal (.modal ((CompareTy.ofTy source).subst ts ms) (m.subst ms)) q) (.ofTy target) ∨
      AlgebraSubtype p.assumptions (.ofTy target)
        (.modal (.modal ((CompareTy.ofTy source).subst ts ms) (m.subst ms)) q)) :
    ∃ after, matchType p (.modal source m) (peel total target).base before = some after ∧
      AgreesWith after ts ms := by
  obtain ⟨b, hb, he⟩ := peel_frozen_stem hΔ hR total hsound hcomplete hm hn hq h
  apply matchType_complete p ht hf ha
  rw [hb]
  exact congrArg (fun a => CompareTy.modal a (m.subst ms)) he

end ModalityInference.ComparisonInstance
