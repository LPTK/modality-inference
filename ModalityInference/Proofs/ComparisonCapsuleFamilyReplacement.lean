import ModalityInference.Proofs.ComparisonCapsuleBindingReplacement
import ModalityInference.Proofs.ComparisonPreparationComplete

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals ComparisonBody ComparisonPartialCarrier ComparisonInterpolation
open ComparisonPartialCapsule ComparisonPreparation

/-- Simultaneously replace the selected type images; the shared source
modality action and every unselected image are retained. -/
def replaceImages (original : CompareSubstitution) (bs : List Binding)
    (suffix : Nat → ModExpr) : CompareSubstitution :=
  { types := bs.map (fun b => (b.name, CompareTy.modal (.ofTy b.base) (suffix b.fresh))) ++ original.types
    modes := original.modes }

private theorem lookup_entry {α : Type} {entries : List (Nat × α)} {n : Nat} {a : α}
    (h : entries.lookup n = some a) : (n, a) ∈ entries := by
  obtain ⟨left, right, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  exact List.mem_append_right _ List.mem_cons_self

theorem replaceImages_type_cases (original : CompareSubstitution) (bs : List Binding)
    (suffix : Nat → ModExpr) (v : TypeVar) :
    (replaceImages original bs suffix).type v = original.type v ∨
      ∃ b ∈ bs, v = .flex b.name ∧
        (replaceImages original bs suffix).type v = .modal (.ofTy b.base) (suffix b.fresh) := by
  cases v with
  | rigid n => exact Or.inl rfl
  | flex n =>
    cases he : (bs.map (fun b => (b.name, CompareTy.modal (.ofTy b.base) (suffix b.fresh)))).lookup n with
    | none =>
      exact Or.inl (by simp only [replaceImages, CompareSubstitution.type, List.lookup_append, he,
        Option.none_or])
    | some a =>
      obtain ⟨b, hb, hpair⟩ := List.mem_map.mp (lookup_entry he)
      have hn := (Prod.mk.inj hpair).1
      have ht := (Prod.mk.inj hpair).2
      refine Or.inr ⟨b, hb, congrArg TypeVar.flex hn.symm, ?_⟩
      simp only [replaceImages, CompareSubstitution.type, List.lookup_append, he,
        Option.some_or, Option.getD_some, ht]

theorem replaceImages_wellShaped {Δ : Bounds} {original : CompareSubstitution}
    (h : original.WellShaped Δ) (bs : List Binding) (suffix : Nat → ModExpr) :
    (replaceImages original bs suffix).WellShaped Δ := by
  intro entry he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp he
    exact CompareTy.wellShaped_ofTy b.base Δ
  · exact h entry he

theorem replaceImages_domainsAbove {original : CompareSubstitution} {nt nm : Nat}
    (h : original.DomainsAbove nt nm) (bs : List Binding) (suffix : Nat → ModExpr)
    (hkeys : ∀ b ∈ bs, nt ≤ b.name) :
    (replaceImages original bs suffix).DomainsAbove nt nm := by
  refine ⟨?_, h.2⟩
  intro entry he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
    exact hkeys b hb
  · exact h.1 entry he

structure ReplacementData (p : Prepared) (total : ModExpr → Bool)
    (original : CompareSubstitution) (Q : ModVar → Prop) (b : Binding) (q : ModExpr) : Prop where
  suffixTotal : Entails p.assumptions (.defined q)
  support : ∀ v ∈ q.vars, Q v
  partialImage : ¬(original.type (.flex b.name)).DefinedUnder p.assumptions
  preserves : PreservesBounds p.assumptions (original.type (.flex b.name)) (.modal (.ofTy b.base) q)
  goals : ∀ r ∈ b.requests, Entails p.assumptions ((r.mapAction original.mode).bound total q)

/-- A finite family of actual capsule plans preserves the complete prepared
witness, including all guarded source bounds, once its frozen keys are retained. -/
theorem family_replacement {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {original : CompareSubstitution} (h : PreparedWitness p original)
    (hi : ComparisonModeRestriction.Fixed p.assumptions original.mode)
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
      obtain ⟨q, hq, hqs, hpartial, hp, hg⟩ := mixed_binding_replacement hΔ hρ hknown
        original.mode hi (hbs.subset hb) (original.type (.flex b.name)) (hsupport b hb)
        (hatomic b hb) (hholds b hb)
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
  · exact body_replacement hΔ (isTotal known)
      (fun m hm => hi.defined (isTotal_defined (knownTotal_sound hknown) hm))
      (Carrier.of_public p.targetType) h.2.2.2 (fun v _ => hp v) hfree

/-- A deterministic partition leaves all frozen images for literal context
matching and selects the remaining mixed capsule groups. -/
def unfrozenBindings (p : Prepared) (total : ModExpr → Bool) : List Binding :=
  (mixedBindings p total).filter fun b => decide (TypeVar.flex b.name ∉ frozenTypes total p.sourceType)

theorem unfrozen_family_replacement {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {original : CompareSubstitution} (h : PreparedWitness p original)
    (hi : ComparisonModeRestriction.Fixed p.assumptions original.mode)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ unfrozenBindings p (isTotal known), Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ unfrozenBindings p (isTotal known), ∀ r ∈ b.requests,
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    ∃ suffix : Nat → ModExpr,
      (∀ b ∈ unfrozenBindings p (isTotal known),
        ReplacementData p (isTotal known) original Q b (suffix b.fresh)) ∧
      PreparedWitness p (replaceImages original (unfrozenBindings p (isTotal known)) suffix) := by
  apply family_replacement hΔ hR hρ hknown h hi _ (List.filter_sublist) _ hsupport hatomic
  intro b hb
  exact of_decide_eq_true (List.mem_filter.mp hb).2

end ModalityInference.ComparisonCapsuleContext
