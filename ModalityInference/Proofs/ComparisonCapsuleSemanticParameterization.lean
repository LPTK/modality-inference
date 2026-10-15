import ModalityInference.Proofs.ComparisonCapsuleFrozenBody
import ModalityInference.Proofs.ComparisonCapsuleBindingActions
import ModalityInference.Proofs.ComparisonCapsuleParameterization

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonCapsuleIntervals ComparisonPartialCarrier ComparisonInterpolation
open ComparisonPartialCapsule ComparisonPreparation

noncomputable section
open Classical

theorem requests_name_support (p : Prepared) (total : ModExpr → Bool)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    {r : Request} (hr : r ∈ requests p total fuel lower source target sm tm) :
    TypeVar.flex r.name ∈ source.typeVars := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    cases source with
    | modal a m =>
      simp only [requests] at hr
      split at hr
      · exact ih lower a target (.compose m sm) tm hr
      · simp at hr
    | var v =>
      cases v with
      | flex n =>
        simp only [requests] at hr
        split at hr
        · cases List.mem_singleton.mp hr; exact Finset.mem_singleton_self _
        · simp at hr
      | rigid n =>
        cases target <;> simp only [requests] at hr
        all_goals try simp at hr
        exact ih _ _ _ _ _ hr
    | unit | credit =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      exact ih _ _ _ _ _ hr
    | prod a b | sum a b | fn a b =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal c m => exact ih _ _ _ _ _ hr
      all_goals
        rcases hr with hr | hr
        · exact Finset.mem_union_left _ (ih _ _ _ _ _ hr)
        · exact Finset.mem_union_right _ (ih _ _ _ _ _ hr)

/-- A name outside all instantiated frozen ancestors has total accumulated
actions at every collected occurrence, including across function resets. -/
theorem requests_action_total_unfrozen {Δ : Bounds} (p : Prepared) (total : ModExpr → Bool)
    (images : ModVar → ModExpr)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    (hsm : Entails Δ (.defined (sm.subst images)))
    {r : Request} (hr : r ∈ requests p total fuel lower source target sm tm)
    (hf : TypeVar.flex r.name ∉
      frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst images)))) source) :
    Entails Δ (.defined (r.action.subst images)) := by
  classical
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    cases source with
    | modal a m =>
      simp only [requests] at hr
      split at hr
      · by_cases hm : Entails Δ (.defined (m.subst images))
        · simp only [frozenTypeSupport, hm, decide_true, if_true] at hf
          exact ih lower a target (.compose m sm) tm
            (Entails.defined_compose_iff.mpr ⟨hm, hsm⟩) hr hf
        · simp only [frozenTypeSupport, hm, decide_false, Bool.false_eq_true, if_false] at hf
          exact False.elim (hf (requests_name_support p total _ _ _ _ _ _ hr))
      · simp at hr
    | var v =>
      cases v with
      | flex n =>
        simp only [requests] at hr
        split at hr
        · cases List.mem_singleton.mp hr; exact hsm
        · simp at hr
      | rigid n =>
        cases target <;> simp only [requests] at hr
        all_goals try simp at hr
        exact ih _ _ _ _ _ hsm hr hf
    | unit | credit =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      exact ih _ _ _ _ _ hsm hr hf
    | prod a b | sum a b | fn a b =>
      have ha : TypeVar.flex r.name ∉
          frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst images)))) a :=
        fun h => hf (Finset.mem_union_left _ h)
      have hb : TypeVar.flex r.name ∉
          frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst images)))) b :=
        fun h => hf (Finset.mem_union_right _ h)
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal c m => exact ih _ _ _ _ _ hsm hr hf
      all_goals
        rcases hr with hr | hr
        · exact ih _ _ _ _ _ (by first | exact hsm | exact fun _ _ => rfl) hr ha
        · exact ih _ _ _ _ _ (by first | exact hsm | exact fun _ _ => rfl) hr hb

theorem collect_action_total_unfrozen {Δ : Bounds} (p : Prepared) (total : ModExpr → Bool)
    (images : ModVar → ModExpr) {r : Request} (hr : r ∈ collect p total)
    (hf : TypeVar.flex r.name ∉
      frozenTypeSupport (fun m => decide (Entails Δ (.defined (m.subst images)))) p.sourceType) :
    Entails Δ (.defined (r.action.subst images)) :=
  requests_action_total_unfrozen p total images _ false p.sourceType p.targetType
    .epsilon .epsilon (fun _ _ => rfl) hr hf

/-- The semantic partition retains exactly the mixed groups enclosed by a
partial instantiated source annotation. It is a witness normal form, rather
than an additional executable choice procedure. -/
def semanticUnfrozenBindings (p : Prepared) (total : ModExpr → Bool)
    (images : ModVar → ModExpr) : List Binding :=
  (mixedBindings p total).filter fun b => decide (TypeVar.flex b.name ∉
    frozenTypeSupport (fun m => decide (Entails p.assumptions (.defined (m.subst images)))) p.sourceType)

/-- A simultaneous replacement of all selected mixed atomic intervals
preserves the complete guarded witness. Only semantic frozen keys are retained;
the other original modality images may remain partial. -/
theorem family_replacement_semantic {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {original : CompareSubstitution} (h : PreparedWitness p original)
    (bs : List Binding) (hbs : bs.Sublist (mixedBindings p (isTotal known)))
    (hfrozen : ∀ b ∈ bs, TypeVar.flex b.name ∉
      frozenTypeSupport (fun m => decide (Entails p.assumptions
        (.defined (m.subst original.mode)))) p.sourceType)
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
        (fun r hr => collect_action_total_unfrozen p (isTotal known) original.mode
          (hmem b hb r hr) (by simpa only [hname b hb r hr] using hfrozen b hb))
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
  have hfree : ∀ v ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst original.mode)))) p.sourceType,
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
  · exact body_replacement_semantic hΔ original.type (replaceImages original bs suffix).type
      original.mode h.2.2.2 (fun v _ => hp v) hfree

/-- The whole family has one shared witness: semantic frozen groups retain
literal input images, and every other atomic mixed group receives one suffix. -/
theorem semantic_family_normal_form {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {original : CompareSubstitution} (h : PreparedWitness p original)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ semanticUnfrozenBindings p (isTotal known) original.mode,
      Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ semanticUnfrozenBindings p (isTotal known) original.mode,
      ∀ r ∈ b.requests, Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    ∃ suffix : Nat → ModExpr,
      (∀ b ∈ semanticUnfrozenBindings p (isTotal known) original.mode,
        ReplacementData p (isTotal known) original Q b (suffix b.fresh)) ∧
      PreparedWitness p (replaceImages original
        (semanticUnfrozenBindings p (isTotal known) original.mode) suffix) ∧
      (∀ b ∈ mixedBindings p (isTotal known),
        b ∉ semanticUnfrozenBindings p (isTotal known) original.mode →
        original.type (.flex b.name) ∈ bodyFrozenTypeCandidates p.sourceType p.targetType) := by
  obtain ⟨suffix, hdata, hw⟩ := family_replacement_semantic hΔ hR hρ hknown h _
    List.filter_sublist (fun b hb => of_decide_eq_true (List.mem_filter.mp hb).2) hsupport hatomic
  refine ⟨suffix, hdata, hw, ?_⟩
  intro b hb hn
  have hf : TypeVar.flex b.name ∈ frozenTypeSupport (fun m => decide (Entails p.assumptions
      (.defined (m.subst original.mode)))) p.sourceType := by
    by_contra hf
    exact hn (List.mem_filter.mpr ⟨hb, by simpa only [decide_eq_true_eq] using hf⟩)
  exact body_semantic_frozen_type_images hΔ hR original.type original.mode h.2.2.2 _ hf

/-- The arbitrary original mode witness and every suffix are instantiated
together in the actual derived source scheme, retaining all written guards. -/
theorem semantic_parameterized_subsumes (source target : Scheme)
    {ρ : TypeVar → ComparisonShape}
    (hR : Residual (SchemePreparation.prepare [] source target).assumptions)
    (hρ : ComparisonShape.Models (SchemePreparation.prepare [] source target).assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel (SchemePreparation.prepare [] source target).assumptions
      (ComparisonAnnotations.expressions (SchemePreparation.prepare [] source target).sourceType ++
        ComparisonAnnotations.expressions (SchemePreparation.prepare [] source target).targetType) = .success known)
    {original : CompareSubstitution}
    (h : PreparedWitness (SchemePreparation.prepare [] source target) original)
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (hsupport : ∀ b ∈ semanticUnfrozenBindings (SchemePreparation.prepare [] source target)
      (isTotal known) original.mode, Supports P Q (original.type (.flex b.name)))
    (hatomic : ∀ b ∈ semanticUnfrozenBindings (SchemePreparation.prepare [] source target)
      (isTotal known) original.mode, ∀ r ∈ b.requests,
      Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ)) :
    let p := SchemePreparation.prepare [] source target
    let bs := semanticUnfrozenBindings p (isTotal known) original.mode
    AlgebraSubsumes []
      (ComparisonParameterization.source p (symbolic bs) (bs.map Binding.fresh) (goals (isTotal known) bs))
      (ComparisonParameterization.target p target) := by
  obtain ⟨suffix, hdata, hnew, _⟩ := semantic_family_normal_form
    (SchemePreparation.prepared_typeBoundsDefined source target) hR hρ hknown h hsupport hatomic
  apply parameterized_subsumes source target hdata h hnew
  intro b hb
  exact (List.mem_filter.mp (List.mem_filter.mp hb).1).1

end

end ModalityInference.ComparisonCapsuleContext
