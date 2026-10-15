import ModalityInference.Proofs.ComparisonCapsuleLocalActions
import ModalityInference.Proofs.ComparisonCapsuleBindingActions

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals ComparisonBody ComparisonPartialCarrier ComparisonInterpolation
open ComparisonPartialCapsule ComparisonPreparation

/-- A single partial-mode witness is retained while every selected atomic
interval receives one shared suffix. Only traversed source annotations must be
total after that witness's modality substitution. -/
theorem family_replacement_local {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {original : CompareSubstitution} (h : PreparedWitness p original)
    (hlocal : SourceActionsTotal p.assumptions (isTotal known) original.mode p.sourceType)
    (bs : List Binding) (hbs : bs.Sublist (mixedBindings p (isTotal known)))
    (hfrozen : ∀ b ∈ bs, TypeVar.flex b.name ∉ frozenTypes (isTotal known) p.sourceType)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ bs, Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ bs, ∀ r ∈ b.requests,
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    ∃ suffix : Nat → ModExpr,
      (∀ b ∈ bs, ReplacementData p (isTotal known) original Q b (suffix b.fresh)) ∧
      PreparedWitness p (replaceImages original bs suffix) := by
  have hn : (bs.map Binding.fresh).Nodup :=
    (mixedBindings_fresh_nodup p (isTotal known)).sublist (hbs.map _)
  have hname : ∀ b ∈ bs, ∀ r ∈ b.requests, r.name = b.name := by
    intro b hb r hr
    rw [(plan_spec (mixed_binding_plan (hbs.subset hb))).2.2.1] at hr
    exact beq_iff_eq.mp (List.mem_filter.mp hr).2
  have hmem : ∀ b ∈ bs, ∀ r ∈ b.requests, r ∈ collect p (isTotal known) :=
    fun b hb r hr => binding_request_mem_collect (List.mem_filter.mp (hbs.subset hb)).1 hr
  have hholds : ∀ b ∈ bs, ∀ r ∈ b.requests,
      (r.mapAction original.mode).AlgebraHolds p.assumptions (original.type (.flex b.name)) := by
    intro b hb r hr
    have hh := collect_algebra hR (isTotal known) h.2.2.2 r (hmem b hb r hr)
    simpa only [hname b hb r hr] using hh
  obtain ⟨suffix, hdata⟩ := suffix_family hn (R := ReplacementData p (isTotal known) original Q)
    (fun b hb => by
      obtain ⟨q, hq, hqs, hpartial, hp, hg⟩ := mixed_binding_replacement_of_actions hΔ hρ hknown
        original.mode (hbs.subset hb) (original.type (.flex b.name)) (hsupport b hb)
        (hatomic b hb)
        (fun r hr => collect_action_subst_total p (isTotal known) original.mode hlocal (hmem b hb r hr))
        (hholds b hb)
      exact ⟨q, ⟨hq, hqs, hpartial, hp, hg⟩⟩)
  refine ⟨suffix, hdata, ?_⟩
  have hp : ∀ v, PreservesBounds p.assumptions (original.type v)
      ((replaceImages original bs suffix).type v) := by
    intro v
    rcases replaceImages_type_cases original bs suffix v with he | ⟨b, hb, rfl, he⟩
    · rw [he]
      exact .refl _ _
    · rw [he]
      exact (hdata b hb).preserves
  have hfixed : ∀ v, (original.type v).DefinedUnder p.assumptions →
      (replaceImages original bs suffix).type v = original.type v := by
    intro v hd
    rcases replaceImages_type_cases original bs suffix v with he | ⟨b, hb, rfl, _⟩
    · exact he
    · exact False.elim ((hdata b hb).partialImage hd)
  have hfree : ∀ v ∈ frozenTypes (isTotal known) p.sourceType,
      (replaceImages original bs suffix).type v = original.type v := by
    intro v hv
    rcases replaceImages_type_cases original bs suffix v with he | ⟨b, hb, rfl, _⟩
    · exact he
    · exact False.elim (hfrozen b hb hv)
  refine ⟨replaceImages_domainsAbove h.1 bs suffix ?_,
    replaceImages_wellShaped h.2.1 bs suffix,
    bounds_replacement h.2.2.1 hfixed (fun _ _ => rfl), ?_⟩
  · intro b hb
    obtain ⟨r, hr, _⟩ := (mixed_binding_flags (hbs.subset hb)).1
    have hal := (collect_support p _ (hmem b hb r hr)).1
    rw [hname b hb r hr] at hal
    simp only [ComparisonInstance.typeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hal
    exact hal.1
  · exact body_replacement_local hΔ (isTotal known) hlocal
      (Carrier.of_public p.targetType) h.2.2.2 (fun v _ => hp v) hfree

theorem unfrozen_family_replacement_local {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {original : CompareSubstitution} (h : PreparedWitness p original)
    (hlocal : SourceActionsTotal p.assumptions (isTotal known) original.mode p.sourceType)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ unfrozenBindings p (isTotal known), Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ unfrozenBindings p (isTotal known), ∀ r ∈ b.requests,
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    ∃ suffix : Nat → ModExpr,
      (∀ b ∈ unfrozenBindings p (isTotal known),
        ReplacementData p (isTotal known) original Q b (suffix b.fresh)) ∧
      PreparedWitness p (replaceImages original (unfrozenBindings p (isTotal known)) suffix) := by
  apply family_replacement_local hΔ hR hρ hknown h hlocal _ (List.filter_sublist) _ hsupport hatomic
  intro b hb
  exact of_decide_eq_true (List.mem_filter.mp hb).2

/-- Every atomic mixed group selected outside frozen source contexts admits
one joint public parameterization. The original guarded constraints and body
are retained in the resulting algebraic scheme comparison. -/
theorem unfrozen_parameterized_subsumes_local (source target : Scheme)
    {ρ : TypeVar → ComparisonShape}
    (hR : Residual (SchemePreparation.prepare [] source target).assumptions)
    (hρ : ComparisonShape.Models (SchemePreparation.prepare [] source target).assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel (SchemePreparation.prepare [] source target).assumptions
      (ComparisonAnnotations.expressions (SchemePreparation.prepare [] source target).sourceType ++
        ComparisonAnnotations.expressions (SchemePreparation.prepare [] source target).targetType) = .success known)
    {original : CompareSubstitution}
    (h : PreparedWitness (SchemePreparation.prepare [] source target) original)
    (hlocal : SourceActionsTotal (SchemePreparation.prepare [] source target).assumptions
      (isTotal known) original.mode (SchemePreparation.prepare [] source target).sourceType)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ unfrozenBindings (SchemePreparation.prepare [] source target) (isTotal known),
      ComparisonInterpolation.Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ unfrozenBindings (SchemePreparation.prepare [] source target) (isTotal known),
      ∀ r ∈ b.requests, ComparisonPartialCapsule.Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    let p := SchemePreparation.prepare [] source target
    let bs := unfrozenBindings p (isTotal known)
    AlgebraSubsumes []
      (ComparisonParameterization.source p (symbolic bs) (bs.map Binding.fresh) (goals (isTotal known) bs))
      (ComparisonParameterization.target p target) := by
  obtain ⟨suffix, hdata, hnew⟩ := unfrozen_family_replacement_local
    (SchemePreparation.prepared_typeBoundsDefined source target) hR hρ hknown h hlocal hsupport hatomic
  apply parameterized_subsumes source target hdata h hnew
  intro b hb
  exact (List.mem_filter.mp (List.mem_filter.mp hb).1).1

end ModalityInference.ComparisonCapsuleContext
