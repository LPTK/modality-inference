import ModalityInference.Proofs.ComparisonPropagationComposition
import ModalityInference.Proofs.ComparisonPreparedBounds
import ModalityInference.Proofs.ComparisonContextSupport
import ModalityInference.Proofs.ComparisonEliminationSupport

namespace ModalityInference

namespace ComparisonInterpolation

theorem ofTy_type_support {P : TypeVar → Prop} (t : Ty)
    (h : ∀ v ∈ t.typeVars, P v) : Supports P (fun _ => True) (CompareTy.ofTy t) := by
  induction t <;> simp_all [Supports, CompareTy.ofTy, TypeExpr.typeVars, or_imp, forall_and]

end ComparisonInterpolation

namespace CompareSubstitution

theorem type_fixed_of_keys (images : List (Nat × CompareTy)) (v : TypeVar)
    (h : ∀ entry ∈ images, v ≠ .flex entry.1) :
    ({ types := images } : CompareSubstitution).type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    have hn : images.lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      exact bne_iff_ne.mpr (fun hname => h entry he (congrArg TypeVar.flex hname))
    simp only [type, hn, Option.getD_none]

theorem type_append_right (left right : List (Nat × CompareTy)) (v : TypeVar)
    (h : ∀ entry ∈ left, v ≠ .flex entry.1) :
    ({ types := left ++ right } : CompareSubstitution).type v =
      ({ types := right } : CompareSubstitution).type v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    have hn : left.lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      exact bne_iff_ne.mpr (fun hname => h entry he (congrArg TypeVar.flex hname))
    simp only [type, List.lookup_append, hn, Option.or]

end CompareSubstitution

namespace ComparisonReduction

theorem prepare_partial_lookup {fuel p templates bare known shared result}
    (h : prepare fuel p templates bare known shared = .success result) :
    ∀ entry ∈ result.partialTypes, result.partialTypes.lookup entry.1 = some entry.2 := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · intro entry he
    rw [run_partialTypes h] at he ⊢
    obtain ⟨name, hn, rfl⟩ := List.mem_map.mp he
    exact lookup_map_self _ _ hn
  · contradiction
  · contradiction

theorem prepare_partial_type_support {fuel p templates bare known shared result}
    {P : TypeVar → Prop}
    (h : prepare fuel p templates bare known shared = .success result)
    (hp : PinnedHolds bare P (initial (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType) p.targetType)) :
    ∀ entry ∈ result.partialTypes,
      ComparisonInterpolation.Supports P (fun _ => True) entry.2 := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · next first hfirst =>
    have hp' := run_pinnedHolds hfirst (fun _ hn => hn) hp
    intro entry he
    rw [run_partialTypes h] at he
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp he
    exact ComparisonPartial.image_support fun b hb =>
      ComparisonInterpolation.ofTy_type_support b.endpoint (hp'.2 b hb).2
  · contradiction
  · contradiction

theorem partial_image_equations {fuel p templates bare known shared result}
    {P : TypeVar → Prop} (extra : List (Nat × CompareTy)) (modes : Substitution)
    (h : prepare fuel p templates bare known shared = .success result)
    (hp : PinnedHolds bare P (initial (templates.substitution.bounds p.sourceBounds)
      (templates.substitution.ty p.sourceType) p.targetType))
    (hf : ∀ v, P v →
      (ComparisonElimination.imageAction (result.partialTypes ++ extra) modes).type v = .var v) :
    let action := ComparisonElimination.imageAction (result.partialTypes ++ extra) modes
    ∀ entry ∈ result.partialTypes,
      action.type (.flex entry.1) = entry.2.subst action.type action.mode := by
  dsimp only
  intro entry he
  rw [ComparisonElimination.imageAction_type]
  have hl := prepare_partial_lookup h entry he
  simp only [CompareSubstitution.type, List.lookup_append, hl, Option.or,
    Option.getD_some]
  exact ((prepare_partial_type_support h hp entry he).subst_congr hf (fun _ _ => rfl)).symm

end ComparisonReduction

end ModalityInference

namespace ModalityInference.ComparisonChecker

/-- Removing generated leaf bindings from the returned action preserves every
input identifier. Template images already contain their reconstructed leaves. -/
theorem assembled_type_eq (templates : Substitution) (intervals leaves : List (Nat × CompareTy))
    (modes : Substitution)
    (hdisjoint : ∀ entry ∈ templates.types, entry.1 ∉ intervals.map Prod.fst)
    (himages : ∀ entry ∈ templates.types, ∀ v ∈ entry.2.typeVars,
      ∀ pair ∈ intervals, v ≠ .flex pair.1)
    (v : TypeVar) (hv : ∀ entry ∈ leaves, v ≠ .flex entry.1) :
    (ComparisonExactContext.finish templates
      (ComparisonElimination.imageAction (intervals ++ leaves) modes)).type v =
    (ComparisonElimination.imageAction (intervals ++ templates.types.map
      (fun (name, t) => (name, ({ types := leaves } : CompareSubstitution).ty t))) modes).type v := by
  rw [ComparisonExactContext.finish_type, ComparisonElimination.imageAction_type]
  cases v with
  | rigid n => rfl
  | flex n =>
    cases he : templates.types.lookup n with
    | none =>
      have hl : leaves.lookup n = none := List.lookup_eq_none_iff.mpr (by
        intro pair hp
        exact bne_iff_ne.mpr (fun heq => hv pair hp (congrArg TypeVar.flex heq)))
      simp only [Substitution.type, he, Option.getD_none]
      change (ComparisonElimination.imageAction (intervals ++ leaves) modes).type (.flex n) = _
      rw [ComparisonElimination.imageAction_type]
      apply congrArg (CompareTy.subst CompareTy.var modes.mode)
      simp only [CompareSubstitution.type, List.lookup_append, lookup_map_values, he,
        Option.map_none, hl]
    | some t =>
      obtain ⟨front, back, hlist, _⟩ := List.lookup_eq_some_iff.mp he
      have hmem : (n, t) ∈ templates.types := by simp [hlist]
      have hp : intervals.lookup n = none := List.lookup_eq_none_iff.mpr (by
        intro pair hpair
        exact bne_iff_ne.mpr (fun heq => hdisjoint (n, t) hmem
          (List.mem_map.mpr ⟨pair, hpair, heq.symm⟩)))
      simp only [Substitution.type, he, Option.getD_some, ComparisonElimination.imageAction_ty,
        CompareSubstitution.type, List.lookup_append, lookup_map_values, hp, Option.or,
        Option.map_some, Option.getD_some]
      apply congrArg (CompareTy.subst CompareTy.var modes.mode)
      apply CompareSubstitution.ty_congr_on
      · intro w hw
        exact CompareSubstitution.type_append_right intervals leaves w (himages (n, t) hmem w hw)
      · intro _ _; rfl

end ModalityInference.ComparisonChecker
