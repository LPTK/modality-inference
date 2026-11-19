import ModalityInference.Proofs.ComparisonObserverShadowModelAnchors
import ModalityInference.Proofs.ComparisonRawHeadTraceActions
import ModalityInference.Proofs.ComparisonRawHeadTraceRows

/-! The concrete finite shadow model reflects every visited raw endpoint.
Its coverage follows from trace closure, anchor rows, and exact constructor rows. -/
namespace ModalityInference.ComparisonObserverShadowModel

open ComparisonRelativeSyntax ComparisonRelativeCoordinates ComparisonRawHeadFiniteOrbits
  ComparisonFiniteControls ComparisonRawCarrierSuffix ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonObserverShadowActions ComparisonObserverFiniteRange
  ComparisonRawHeadTrace ComparisonRawHeadTraceRows

noncomputable section

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ} {sites : List Site}
  {extra : List (RawRow hn (assign hn (boundary Δ sites) (modeNames Δ sites)
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads sites))))}
  (R : Realization hn (boundary Δ sites) (modeNames Δ sites)
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads sites)) extra)
  (T : Tables R)

def interpretation := T.model (context_names Δ sites) sites (siteTag R)

theorem coverage
    (hrows : ComparisonObserverShadowAnchorRows.rows hn (rawHeads sites) (modeNames Δ sites) ⊆ extra)
    (hclosed : ∀ s ∈ sites, calls Δ s.1 s.2 ⊆ sites) :
    RawCoverage (interpretation R T) (fun m => (R.action m).map)
      (ComparisonRelativeDiagramActions.index_mono R.action R.defined_index R.boundary_index)
      sites (siteTag R) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a
    exact congrArg R.interval.embed (R.map_one a)
  · intro v hs
    exact (orbit_siteTag_defined R hrows hs
      (by simp [applyPrefix,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels])).symm
  · intro hs
    exact (orbit_siteTag_defined R hrows hs
      (by simp [applyPrefix,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels])).symm
  · intro hs
    exact (orbit_siteTag_defined R hrows hs
      (by simp [applyPrefix,TypeExpr.DefinedUnder,TypeExpr.wellFormedBounds,ModeModels])).symm
  · intro a p hs _
    exact rawFrozen_recorded sites (fun s => R.orbit (siteTag R s)) hs
  · intro a m hs
    have hc := hclosed _ hs (modal_none_subset Δ a m (root_mem Δ a (normalize Δ m).literal))
    exact ⟨hc,modal_orbit R (unit R.range) hs hc⟩
  · intro a m p hs
    have hc := hclosed _ hs (modal_some_subset Δ a m p (root_mem Δ a (some (.compose m p))))
    exact ⟨hc,prefixed_modal_orbit R (unit R.range) hs hc⟩
  · intro a b p hs
    have ha := hclosed _ hs ((prod_subsets Δ a b p).1 (root_mem Δ a p))
    have hb := hclosed _ hs ((prod_subsets Δ a b p).2 (root_mem Δ b p))
    refine ⟨ha,hb,?_⟩
    intro m
    rw [siteTag_mem R ha,siteTag_mem R hb,siteTag_mem R hs]
    cases p with
    | none => exact T.prod_boundary (prod_none ha hb hs m)
    | some p => exact ComparisonRawHeadPrefixRows.Entry.boundary (prod_some ha hb hs m)
  · intro a b p hs
    have ha := hclosed _ hs ((sum_subsets Δ a b p).1 (root_mem Δ a p))
    have hb := hclosed _ hs ((sum_subsets Δ a b p).2 (root_mem Δ b p))
    refine ⟨ha,hb,?_⟩
    intro m
    rw [siteTag_mem R ha,siteTag_mem R hb,siteTag_mem R hs]
    cases p with
    | none => exact T.sum_boundary (sum_none ha hb hs m)
    | some p => exact ComparisonRawHeadPrefixRows.Entry.boundary (sum_some ha hb hs m)
  · intro a b hs
    have ha := hclosed _ hs ((fn_subsets Δ a b).1 (root_mem Δ a none))
    have hb := hclosed _ hs ((fn_subsets Δ a b).2 (root_mem Δ b none))
    refine ⟨ha,hb,?_⟩
    intro m
    rw [siteTag_mem R ha,siteTag_mem R hb,siteTag_mem R hs]
    exact T.fn_boundary (fn_none ha hb hs m)

variable
  (hrows : ComparisonObserverShadowAnchorRows.rows hn (rawHeads sites) (modeNames Δ sites) ⊆ extra)
  (hclosed : ∀ s ∈ sites, calls Δ s.1 s.2 ⊆ sites)

include hrows hclosed

theorem denote_raw {a : Ty} {p : Option ModExpr} (ha : (a,p) ∈ sites) :
    (interpretation R T).denote (.ofTy a) p = R.orbit (siteTag R (a,p)) :=
  (coverage R T hrows hclosed).denote ha

theorem raw_related_iff {a b : Ty} (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites) :
    (interpretation R T).Related (.ofTy a) (.ofTy b) ↔ AlgebraSubtype Δ (.ofTy a) (.ofTy b) := by
  change (interpretation R T).denote (.ofTy a) none ≤ (interpretation R T).denote (.ofTy b) none ↔ _
  rw [denote_raw R T hrows hclosed ha,denote_raw R T hrows hclosed hb]
  exact (R.orbit_le_iff _ _).trans (tag_order_iff R (unit R.range) ha hb)

theorem algebra_sound
    (hbounds : ∀ a b, Constraint.sub a b ∈ Δ → (a,none) ∈ sites ∧ (b,none) ∈ sites)
    {a b : CompareTy} (hab : AlgebraSubtype Δ a b) : (interpretation R T).Related a b := by
  apply (T.agreement (context_names Δ sites) sites (siteTag R)).algebra_sound ?_ hab
  intro a b hbound
  obtain ⟨ha,hb⟩ := hbounds a b hbound
  exact (raw_related_iff R T hrows hclosed ha hb).mpr (.shaped (.bound hbound))

end
end ModalityInference.ComparisonObserverShadowModel
