import ModalityInference.Proofs.ComparisonRawHeadTrace
import ModalityInference.Proofs.ComparisonFiniteControlProjection
import ModalityInference.Proofs.ComparisonObserverShadowActions

/-! Modal edges of the finite raw trace are equations in the actual diagram.
Supported normalized controls retain their original scalar meaning. -/
namespace ModalityInference.ComparisonRawHeadTrace

open ComparisonRawHeadFiniteOrbits ComparisonFiniteControls ComparisonFiniteControlProjection
  ComparisonRawCarrierSuffix ComparisonObserverShadowActions ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonRelativeCoordinates

noncomputable section

theorem memberPoint_act_equivalent {Δ : Bounds} {sites : List Site} {names : List ModVar}
    {s : Site} (hs : s ∈ sites) (m : Control Δ names) :
    AlgebraSubtype Δ (Point.act m (memberPoint Δ names hs)).term
      (.modal (.ofTy (applyPrefix s.2 s.1)) (expression m)) ∧
    AlgebraSubtype Δ (.modal (.ofTy (applyPrefix s.2 s.1)) (expression m))
      (Point.act m (memberPoint Δ names hs)).term :=
  ⟨(Point.term_act m (memberPoint Δ names hs)).2.trans
      ((memberPoint_equivalent Δ names hs).1.congr (.refl (expression_defined m))),
   ((memberPoint_equivalent Δ names hs).2.congr (.refl (expression_defined m))).trans
      (Point.term_act m (memberPoint Δ names hs)).1⟩

theorem memberPoint_modal {Δ : Bounds} {sites : List Site} {a : Ty} {m : ModExpr}
    (hs : (.modal a m,none) ∈ sites) (hc : (a,(normalize Δ m).literal) ∈ sites) :
    let c := project (context_names Δ sites) (normalize Δ m).control (control_total Δ m)
    Point.act c (memberPoint Δ (modeNames Δ sites) hc) ≤ memberPoint Δ (modeNames Δ sites) hs ∧
      memberPoint Δ (modeNames Δ sites) hs ≤ Point.act c (memberPoint Δ (modeNames Δ sites) hc) := by
  dsimp only
  rw [project_supported (context_names Δ sites) _ _ (control_names hs)]
  have he := expression_encode (normalize Δ m).control (control_total Δ m) (control_names hs)
  have ha := memberPoint_act_equivalent hc
    (encode (normalize Δ m).control (control_total Δ m) (control_names hs))
  have hh := CompareTy.wellShaped_ofTy (applyPrefix (normalize Δ m).literal a) Δ
  have hp := memberPoint_equivalent Δ (modeNames Δ sites) hs
  have hm := modal_none_equivalent Δ a m
  exact ⟨ha.1.trans (((AlgebraSubtype.refl hh).congr he.1).trans (hm.2.trans hp.2)),
    hp.1.trans (hm.1.trans (((AlgebraSubtype.refl hh).congr he.2).trans ha.2))⟩

theorem memberPoint_prefixed_modal {Δ : Bounds} {sites : List Site} {names : List ModVar}
    {a : Ty} {m p : ModExpr} (hs : (.modal a m,some p) ∈ sites)
    (hc : (a,some (.compose m p)) ∈ sites) :
    memberPoint Δ names hc ≤ memberPoint Δ names hs ∧
      memberPoint Δ names hs ≤ memberPoint Δ names hc :=
  ⟨(memberPoint_le_iff Δ names hc hs).mpr (modal_some_equivalent Δ a m p).2,
   (memberPoint_le_iff Δ names hs hc).mpr (modal_some_equivalent Δ a m p).1⟩

variable {Δ : Bounds} {sites : List Site} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {base : Nat} {extra : List (RawRow hn (assign hn (boundary Δ sites) (modeNames Δ sites) base))}
  (R : Realization hn (boundary Δ sites) (modeNames Δ sites) base extra)
  (fallback : ComparisonObserverFiniteRange.Value R.machine)

theorem tag_order_iff {s t : Site} (hs : s ∈ sites) (ht : t ∈ sites) :
    R.interval.Rel (tag fallback Δ sites (modeNames Δ sites) s)
      (tag fallback Δ sites (modeNames Δ sites) t) ↔
      AlgebraSubtype Δ (.ofTy (applyPrefix s.2 s.1)) (.ofTy (applyPrefix t.2 t.1)) := by
  rw [tag_mem fallback Δ _ hs,tag_mem fallback Δ _ ht]
  exact memberPoint_le_iff Δ (modeNames Δ sites) hs ht

theorem modal_orbit {a : Ty} {m : ModExpr} (hs : (.modal a m,none) ∈ sites)
    (hc : (a,(normalize Δ m).literal) ∈ sites) :
    shift mul_mono (project (context_names Δ sites) (normalize Δ m).control (control_total Δ m))
      (R.orbit (tag fallback Δ sites (modeNames Δ sites) (a,(normalize Δ m).literal))) =
      R.orbit (tag fallback Δ sites (modeNames Δ sites) (.modal a m,none)) := by
  rw [tag_mem fallback Δ _ hc,tag_mem fallback Δ _ hs,R.shift_orbit]
  apply le_antisymm
  · exact (R.orbit_le_iff _ _).mpr (memberPoint_modal hs hc).1
  · exact (R.orbit_le_iff _ _).mpr (memberPoint_modal hs hc).2

theorem prefixed_modal_orbit {a : Ty} {m p : ModExpr} (hs : (.modal a m,some p) ∈ sites)
    (hc : (a,some (.compose m p)) ∈ sites) :
    R.orbit (tag fallback Δ sites (modeNames Δ sites) (a,some (.compose m p))) =
      R.orbit (tag fallback Δ sites (modeNames Δ sites) (.modal a m,some p)) := by
  rw [tag_mem fallback Δ _ hc,tag_mem fallback Δ _ hs]
  apply le_antisymm
  · exact (R.orbit_le_iff _ _).mpr (memberPoint_prefixed_modal hs hc).1
  · exact (R.orbit_le_iff _ _).mpr (memberPoint_prefixed_modal hs hc).2

end
end ModalityInference.ComparisonRawHeadTrace
