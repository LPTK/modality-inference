import ModalityInference.Proofs.ComparisonCapsuleLocalActions

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonCapsuleIntervals ComparisonPartialCapsule ComparisonInterpolation

/-- A valid mixed atomic name is emitted by the actual finite grouping pass.
The shared input capsule is derived from its comparisons, before a binding is
assumed to exist. -/
theorem mixed_name_complete_local {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (images : ModVar → ModExpr)
    (hlocal : SourceActionsTotal p.assumptions (isTotal known) images p.sourceType)
    (name : Nat) (W : CompareTy) {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hs : Supports P Q W)
    (hatomic : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions)
    (hholds : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      (r.mapAction images).AlgebraHolds p.assumptions W)
    (hlower : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = false) :
    ∃ b ∈ mixedBindings p (isTotal known), b.name = name ∧
      b.requests = (collect p (isTotal known)).filter (fun r => r.name == name) := by
  have hlo := hlower
  obtain ⟨r, hr, _⟩ := hlo
  have hn : name ∈ ((collect p (isTotal known)).map Request.name).dedup := by
    apply List.mem_dedup.mpr
    exact List.mem_map.mpr ⟨r, (List.mem_filter.mp hr).1,
      beq_iff_eq.mp (List.mem_filter.mp hr).2⟩
  have hn' : name ∈ (((collect p (isTotal known)).map Request.name).dedup.zipIdx.map Prod.fst) := by
    simpa only [List.zipIdx_map_fst] using hn
  obtain ⟨⟨key, offset⟩, hz, he⟩ := List.mem_map.mp hn'
  dsimp only at he
  subst key
  obtain ⟨b, _, hp, _, _, _⟩ := plan_complete_mapped_known_supported hΔ hρ hknown
    name (p.nextMode + offset) (collect p (isTotal known)) W images hs hatomic hpartial
    (fun r hr => collect_residuals_covered p _ (List.mem_filter.mp hr).1)
    (fun r hr => collect_action_subst_total p (isTotal known) images hlocal (List.mem_filter.mp hr).1)
    hholds hlower hupper
  have hb : b ∈ bindings p (isTotal known) := List.mem_filterMap.mpr ⟨(name, offset), hz, hp⟩
  have hspec := plan_spec hp
  refine ⟨b, ?_, hspec.1, hspec.2.2.1⟩
  apply List.mem_filter.mpr
  refine ⟨hb, ?_⟩
  simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true', List.all_eq_true, and_assoc]
  rw [hspec.2.2.1]
  refine ⟨hlower, hupper, ?_⟩
  intro r hr
  exact (ComparisonAnnotations.hasPartial_known_true_iff hknown r.endpoint
    (collect_residuals_covered p _ (List.mem_filter.mp hr).1)).mpr (hpartial r hr)

/-- The executable unfrozen selection covers every valid mixed atomic name
that admits replacement in the complete source body. -/
theorem unfrozen_name_complete_local {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (images : ModVar → ModExpr)
    (hlocal : SourceActionsTotal p.assumptions (isTotal known) images p.sourceType)
    (name : Nat) (W : CompareTy) {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hs : Supports P Q W)
    (hatomic : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions)
    (hholds : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      (r.mapAction images).AlgebraHolds p.assumptions W)
    (hlower : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = false)
    (hfree : TypeVar.flex name ∉ frozenTypeSupport (isTotal known) p.sourceType) :
    ∃ b ∈ unfrozenBindings p (isTotal known), b.name = name ∧
      b.requests = (collect p (isTotal known)).filter (fun r => r.name == name) := by
  obtain ⟨b, hb, hn, hr⟩ := mixed_name_complete_local hΔ hρ hknown images hlocal name W hs
    hatomic hpartial hholds hlower hupper
  refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hn, hr⟩
  simp only [hn, decide_eq_true_eq]
  exact hfree

private theorem supports_unrestricted (a : CompareTy) :
    Supports (fun _ => True) (fun _ => True) a := by
  induction a <;> simp_all [Supports]

/-- Actual body admissibility suffices for grouping. A single partial endpoint
in a mixed family forces the complete family into the partial branch. -/
theorem body_unfrozen_name_complete_local {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (original : CompareSubstitution)
    (hlocal : SourceActionsTotal p.assumptions (isTotal known) original.mode p.sourceType)
    (hbody : AlgebraSubtype p.assumptions (original.ty p.sourceType) (.ofTy p.targetType))
    (name : Nat)
    (hatomic : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions)
    (hlower : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = false)
    (hfree : TypeVar.flex name ∉ frozenTypeSupport (isTotal known) p.sourceType) :
    ∃ b ∈ unfrozenBindings p (isTotal known), b.name = name ∧
      b.requests = (collect p (isTotal known)).filter (fun r => r.name == name) := by
  let rs := (collect p (isTotal known)).filter (fun r => r.name == name)
  have hh : ∀ r ∈ rs, (r.mapAction original.mode).AlgebraHolds p.assumptions
      (original.type (.flex name)) := by
    intro r hr
    have hn : r.name = name := beq_iff_eq.mp (List.mem_filter.mp hr).2
    have h := collect_algebra hR (isTotal known) hbody r (List.mem_filter.mp hr).1
    simpa only [hn] using h
  have hm : ∀ r ∈ rs, Entails p.assumptions (.defined (r.action.subst original.mode)) := by
    intro r hr
    exact collect_action_subst_total p (isTotal known) original.mode hlocal (List.mem_filter.mp hr).1
  have hmem (r : Request) (hr : r ∈ rs) : r.mapAction original.mode ∈ rs.map (Request.mapAction original.mode) :=
    List.mem_map.mpr ⟨r, hr, rfl⟩
  have ha : ∀ r ∈ rs, ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions := by
    obtain ⟨lo, hlo, hlp⟩ := hlower
    obtain ⟨up, hup, hupPol⟩ := hupper
    have he := mixed_requests_defined_iff hΔ (rs.map (Request.mapAction original.mode))
      (original.type (.flex name))
      (fun r hr => by obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr; exact hm s hs)
      (fun r hr => by obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr; exact hh s hs)
      (hmem lo hlo) hlp (hmem up hup) hupPol
    obtain ⟨bad, hbad, hp⟩ := hpartial
    intro r hr hd
    exact hp ((he (bad.mapAction original.mode) (hmem bad hbad)).mpr
      ((he (r.mapAction original.mode) (hmem r hr)).mp hd))
  exact unfrozen_name_complete_local hΔ hρ hknown original.mode hlocal name _
    (supports_unrestricted _) hatomic ha hh hlower hupper hfree

end ModalityInference.ComparisonCapsuleContext
