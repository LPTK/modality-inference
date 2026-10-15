import ModalityInference.Proofs.ComparisonCapsuleFrozenSelection
import ModalityInference.Proofs.ComparisonCapsuleBindingActions

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonCapsuleIntervals ComparisonPartialCapsule ComparisonInterpolation
open ComparisonPartialCarrier

/-- A valid mixed atomic name is emitted by the actual finite grouping pass.
The shared input capsule is derived from its comparisons, before a binding is
assumed to exist. -/
theorem mixed_name_complete_of_actions {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (images : ModVar → ModExpr)
    (name : Nat) (W : CompareTy) {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hs : Supports P Q W)
    (hatomic : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions)
    (haction : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      Entails p.assumptions (.defined (r.action.subst images)))
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
    haction
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


/-- A mixed atomic name has an input-relative witness representation without
assuming total modality images. A partial occurrence action retains its exact
literal image; otherwise one planned capsule with a shared total suffix
preserves all carrier bounds and every scalar obligation. -/
theorem mixed_name_normal_form {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    (original : CompareSubstitution)
    (hbody : AlgebraSubtype p.assumptions (original.ty p.sourceType) (.ofTy p.targetType))
    (name : Nat) {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hs : Supports P Q (original.type (.flex name)))
    (hatomic : ∀ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name),
      ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions)
    (hlower : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = true)
    (hupper : ∃ r ∈ (collect p (isTotal known)).filter (fun r => r.name == name), r.isLower = false) :
    original.type (.flex name) ∈ frozenNameCandidates p (isTotal known) name ∨
      ∃ b ∈ mixedBindings p (isTotal known), b.name = name ∧
        ∃ q, Entails p.assumptions (.defined q) ∧ (∀ v ∈ q.vars, Q v) ∧
          ¬(original.type (.flex name)).DefinedUnder p.assumptions ∧
          PreservesBounds p.assumptions (original.type (.flex name)) (.modal (.ofTy b.base) q) ∧
          ∀ r ∈ b.requests, Entails p.assumptions ((r.mapAction original.mode).bound (isTotal known) q) := by
  rcases collected_name_action_dichotomy hΔ hR (isTotal known) original hbody name with haction | hfrozen
  · right
    let rs := (collect p (isTotal known)).filter (fun r => r.name == name)
    have hh : ∀ r ∈ rs, (r.mapAction original.mode).AlgebraHolds p.assumptions
        (original.type (.flex name)) := by
      intro r hr
      have hn : r.name = name := beq_iff_eq.mp (List.mem_filter.mp hr).2
      simpa only [hn] using collect_algebra hR (isTotal known) hbody r (List.mem_filter.mp hr).1
    have hmem (r : Request) (hr : r ∈ rs) : r.mapAction original.mode ∈ rs.map (Request.mapAction original.mode) :=
      List.mem_map.mpr ⟨r, hr, rfl⟩
    have hp : ∀ r ∈ rs, ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions := by
      obtain ⟨lo, hlo, hlp⟩ := hlower
      obtain ⟨up, hup, hupPol⟩ := hupper
      have he := mixed_requests_defined_iff hΔ (rs.map (Request.mapAction original.mode))
        (original.type (.flex name))
        (fun r hr => by obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr; exact haction s hs)
        (fun r hr => by obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr; exact hh s hs)
        (hmem lo hlo) hlp (hmem up hup) hupPol
      obtain ⟨bad, hbad, hp⟩ := hpartial
      intro r hr hd
      exact hp ((he (bad.mapAction original.mode) (hmem bad hbad)).mpr
        ((he (r.mapAction original.mode) (hmem r hr)).mp hd))
    obtain ⟨b, hb, hn, hr⟩ := mixed_name_complete_of_actions hΔ hρ hknown original.mode
      name _ hs hatomic hp haction hh hlower hupper
    obtain ⟨q, hq, hqs, hwp, hpres, hgoals⟩ := mixed_binding_replacement_of_actions
      hΔ hρ hknown original.mode hb _ hs (fun r hm => hatomic r (by simpa only [hr, rs] using hm))
      (fun r hm => haction r (by simpa only [hr, rs] using hm)) (fun r hm => hh r (by simpa only [hr, rs] using hm))
    exact ⟨b, hb, hn, q, hq, hqs, hwp, hpres, hgoals⟩
  · exact Or.inl hfrozen

end ModalityInference.ComparisonCapsuleContext
