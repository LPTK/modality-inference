import ModalityInference.Proofs.ComparisonCapsuleBodyReplacement

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals ComparisonBody ComparisonPartialCapsule
open ComparisonPartialCapsuleScalar ComparisonPartialCarrier ComparisonInterpolation

/-- The exact projected suffix chosen for one actual mixed group preserves
all carrier bounds and symbolic scalar obligations. Only the actions attached
to these occurrences require totality; other modality images are unrestricted. -/
theorem mixed_binding_replacement_of_actions {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (images : ModVar → ModExpr)
    {b : Binding} (hb : b ∈ mixedBindings p (isTotal known))
    (W : CompareTy) {P : TypeVar → Prop} {Q : ModVar → Prop} (hs : Supports P Q W)
    (hatomic : ∀ r ∈ b.requests, Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (haction : ∀ r ∈ b.requests, Entails p.assumptions (.defined (r.action.subst images)))
    (hholds : ∀ r ∈ b.requests, (r.mapAction images).AlgebraHolds p.assumptions W) :
    ∃ q, Entails p.assumptions (.defined q) ∧ (∀ v ∈ q.vars, Q v) ∧
      ¬W.DefinedUnder p.assumptions ∧
      PreservesBounds p.assumptions W (.modal (.ofTy b.base) q) ∧
      ∀ r ∈ b.requests, Entails p.assumptions ((r.mapAction images).bound (isTotal known) q) := by
  have hp := mixed_binding_plan hb
  have hf := mixed_binding_flags hb
  have hmem : ∀ r ∈ b.requests, r ∈ collect p (isTotal known) :=
    fun r hr => binding_request_mem_collect (List.mem_filter.mp hb).1 hr
  have hpartial : ∀ r ∈ b.requests, ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions :=
    fun r hr => (ComparisonAnnotations.hasPartial_known_true_iff hknown r.endpoint
      (collect_residuals_covered p _ (hmem r hr))).mp (hf.2.2 r hr)
  obtain ⟨a, ha, halower⟩ := hf.1
  obtain ⟨c, hc, hcupper⟩ := hf.2.1
  obtain ⟨sa⟩ := collect_peel_normal hΔ hρ hknown (hmem a ha) (hatomic a ha) (hpartial a ha)
  obtain ⟨sc⟩ := collect_peel_normal hΔ hρ hknown (hmem c hc) (hatomic c hc) (hpartial c hc)
  have hl : AlgebraSubtype p.assumptions (.ofTy a.endpoint) (.modal W (a.action.subst images)) := by
    simpa only [Request.AlgebraHolds, Request.mapAction, halower, if_true] using hholds a ha
  have hu : AlgebraSubtype p.assumptions (.modal W (c.action.subst images)) (.ofTy c.endpoint) := by
    simpa only [Request.AlgebraHolds, Request.mapAction, hcupper, Bool.false_eq_true, if_false] using hholds c hc
  obtain ⟨q, hqproject, hqs, hq, hlo, hup⟩ := mixed_carrier_replacement hΔ hρ
    (Carrier.of_public a.endpoint) (Carrier.of_public c.endpoint) sa.normal sc.normal
    (hatomic a ha) (haction a ha) (haction c hc) hl hu hs
  have hbase : CompareTy.ofTy b.base = .modal sa.normal.token.1 sa.normal.token.2 := by
    rw [← (plan_spec hp).2.2.2.2 a ha]
    exact sa.base_eq
  have hatom : Atomic (sa.normal.token.1.shape.subst ρ) := by
    change Atomic ((.modal (.modal sa.normal.token.1 sa.normal.token.2) sa.normal.suffix : CompareTy).shape.subst ρ)
    rw [← sa.normal.forward.shape_equivalent ρ hρ]
    exact hatomic a ha
  have hfreeze : Frozen p.assumptions sa.normal.token :=
    observe_frozen (.ofTy a.endpoint) (sa.normal.observation ▸ Set.mem_singleton _)
  refine ⟨q, hq, hqs, ?_, ?_, ?_⟩
  · intro hd
    exact hpartial a ha ((Carrier.of_public a.endpoint).defined_of_below hΔ
      (CompareTy.definedUnder_modal_iff.mpr ⟨hd, haction a ha⟩) hl)
  · intro lower endpoint he hh
    rw [hbase]
    cases lower
    · exact hup endpoint he hh
    · exact hlo endpoint he hh
  · intro r hr
    obtain ⟨sr⟩ := collect_peel_normal hΔ hρ hknown (hmem r hr) (hatomic r hr) (hpartial r hr)
    have hbases : CompareTy.modal sr.normal.token.1 sr.normal.token.2 =
        .modal sa.normal.token.1 sa.normal.token.2 := by
      rw [← sr.base_eq]
      change CompareTy.ofTy (r.base (isTotal known)) = _
      rw [(plan_spec hp).2.2.2.2 r hr]
      exact hbase
    have he : sr.normal.token = sa.normal.token :=
      Prod.ext (CompareTy.modal.inj hbases).1 (CompareTy.modal.inj hbases).2
    cases hpol : r.isLower
    · have hrr : AlgebraSubtype p.assumptions (.modal W (r.action.subst images)) (.ofTy r.endpoint) := by
        simpa only [Request.AlgebraHolds, Request.mapAction, hpol, Bool.false_eq_true, if_false] using hholds r hr
      have hh := hrr.trans (.shaped sr.normal.forward)
      rw [he] at hh
      have hscalar := project_upper hΔ hρ hfreeze hatom hqproject (haction r hr) sr.normal.total hh
      simpa only [Request.mapAction, Request.bound, Request.suffix, hpol,
        Bool.false_eq_true, if_false, ← sr.suffix_eq] using hscalar
    · have hrr : AlgebraSubtype p.assumptions (.ofTy r.endpoint) (.modal W (r.action.subst images)) := by
        simpa only [Request.AlgebraHolds, Request.mapAction, hpol, if_true] using hholds r hr
      have hh := (AlgebraSubtype.shaped sr.normal.backward).trans hrr
      rw [he] at hh
      have hscalar := project_lower hΔ hρ hfreeze hatom hqproject (haction r hr) sr.normal.total hh
      simpa only [Request.mapAction, Request.bound, Request.suffix, hpol,
        if_true, ← sr.suffix_eq] using hscalar

end ModalityInference.ComparisonCapsuleContext
