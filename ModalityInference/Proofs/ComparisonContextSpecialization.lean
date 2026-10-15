import ModalityInference.Proofs.ComparisonFrozenContextCompleteness
import ModalityInference.Proofs.ComparisonPropagationComposition

namespace ModalityInference.ComparisonInstance

private theorem lookup_entry {α : Type} {entries : List (Nat × α)} {name : Nat} {image : α}
    (h : entries.lookup name = some image) : (name, image) ∈ entries := by
  obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  exact List.mem_append_right _ List.mem_cons_self

theorem AgreesWith.finish_type {p : Prepared} {before : Substitution} {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before) (ha : AgreesWith before σ.type σ.mode)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v) (v : TypeVar) :
    (ComparisonExactContext.finish before σ).type v = σ.type v := by
  rw [ComparisonExactContext.finish_type]
  cases v with
  | rigid n => rfl
  | flex n =>
    cases hl : before.types.lookup n with
    | none => simp only [Substitution.type, hl, Option.getD_none, CompareSubstitution.ty,
        CompareTy.ofTy, CompareTy.subst]
    | some image =>
      have he := lookup_entry hl
      have hf := hs.1 n image he
      have hi := ComparisonAbsorption.instantiate_congr image
        (fun v hv => ht v (hf.2.1 v hv)) (fun v hv => hm v (hf.2.2 v hv))
      simp only [ComparisonAbsorption.instantiate, CompareTy.subst_id] at hi
      simpa only [Substitution.type, hl, Option.getD_some, CompareSubstitution.ty, hi] using
        (ha.types (n, image) he).symm

theorem AgreesWith.finish_mode {p : Prepared} {before : Substitution} {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before) (ha : AgreesWith before σ.type σ.mode)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v) (v : ModVar) :
    (ComparisonExactContext.finish before σ).mode v = σ.mode v := by
  rw [ComparisonExactContext.finish_mode]
  cases v with
  | rigid n => rfl
  | flex n =>
    cases hl : before.modes.lookup n with
    | none => simp only [Substitution.mode, hl, Option.getD_none, ModExpr.subst]
    | some image =>
      have he := lookup_entry hl
      have hf := hs.2 n image he
      have hi := ModExpr.subst_congr image (fun v hv => hm v (hf.2 v hv))
      simp only [ModExpr.subst_id] at hi
      simpa only [Substitution.mode, hl, Option.getD_some, hi] using (ha.modes (n, image) he).symm

/-- Specializing forced literal images leaves the original shared witness
unchanged, including partial images and all written source guards. -/
theorem AgreesWith.rewrite_ty {p : Prepared} {before : Substitution} {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before) (ha : AgreesWith before σ.type σ.mode)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v) (t : Ty) :
    σ.ty (before.ty t) = σ.ty t := by
  rw [← ComparisonExactContext.finish_ty]
  exact CompareSubstitution.ty_congr_on _ _ t
    (fun v _ => ha.finish_type hs ht hm v) (fun v _ => ha.finish_mode hs hm v)

theorem AgreesWith.rewrite_bounds {p : Prepared} {before : Substitution} {σ : CompareSubstitution}
    (hs : ComparisonExactContext.Scoped p before) (ha : AgreesWith before σ.type σ.mode)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v) (Δ : Bounds) (cs : Bounds) :
    AlgebraEntailsAll Δ (σ.bounds (before.bounds cs)) ↔ AlgebraEntailsAll Δ (σ.bounds cs) := by
  rw [← ComparisonExactContext.finish_bounds]
  exact CompareSubstitution.algebra_bounds_congr _ _ cs
    (fun _ _ v _ => ha.finish_type hs ht hm v) (fun _ _ v _ => ha.finish_mode hs hm v)

theorem FrozenRequestHolds.exact {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr} {request : Ty × Ty}
    (h : FrozenRequestHolds Δ ts ms request) :
    (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2 := by
  rw [h.source_eq, h.target_eq]
  have he : (CompareTy.ofTy h.source).subst ts ms = .ofTy h.target ∧
      h.sourceMode.subst ms = h.targetMode := by
    rcases h.comparison with hc | hc
    · exact ComparisonPartialStructuredCapsule.internal_frozen_stem_cancel hΔ hR
        h.source_partial h.target_partial h.source_noncompose h.target_noncompose
        h.source_total h.target_total hc
    · exact ComparisonPartialStructuredCapsule.frozen_internal_stem_cancel hΔ hR
        h.target_partial h.source_partial h.target_noncompose h.source_noncompose
        h.target_total h.source_total hc
  exact congrArg₂ CompareTy.modal he.1 he.2

end ModalityInference.ComparisonInstance

namespace ModalityInference.ComparisonFrozenContext

open ComparisonInstance

theorem independent_agreesWith {p : Prepared} {total : ModExpr → Bool}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (hh : ∀ request ∈ collect p total,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    AgreesWith (independent p total) ts ms := by
  apply ComparisonContext.solvePriorityComponents_property _ _ _ _ _
    (fun action => AgreesWith action ts ms)
    (fun request : Request => (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2)
    (AgreesWith.empty ts ms) hh
  intro request hreq before after ha hmatch
  obtain ⟨selected, hselected, hselectedAgrees⟩ := matchType_complete p ht hm ha hreq
  have he : selected = after := Option.some.inj (hselected.symm.trans hmatch)
  exact he ▸ hselectedAgrees

theorem prepare_agreesWith {p : Prepared} {total : ModExpr → Bool} {before : Substitution}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hp : prepare p total = some before)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (hh : ∀ request ∈ collect p total,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    AgreesWith before ts ms := (prepare_spec hp).2.1 ▸ independent_agreesWith ht hm hh

theorem prepare_preserves_witness {p : Prepared} {total : ModExpr → Bool}
    {before : Substitution} {σ : CompareSubstitution}
    (hp : prepare p total = some before)
    (ht : ∀ v, typeAllowed p v = false → σ.type v = .var v)
    (hm : ∀ v, modeAllowed p v = false → σ.mode v = .var v)
    (hh : ∀ request ∈ collect p total,
      Nonempty (FrozenRequestHolds p.assumptions σ.type σ.mode request))
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (hb : AlgebraEntailsAll p.assumptions (σ.bounds p.sourceBounds))
    (hbody : AlgebraSubtype p.assumptions (σ.ty p.sourceType) (.ofTy p.targetType)) :
    AlgebraEntailsAll p.assumptions (σ.bounds (before.bounds p.sourceBounds)) ∧
      AlgebraSubtype p.assumptions (σ.ty (before.ty p.sourceType)) (.ofTy p.targetType) := by
  have ha := prepare_agreesWith hp ht hm (fun request hr => by
    obtain ⟨h⟩ := hh request hr
    exact h.exact hΔ hR)
  have hs := prepare_scoped hp
  exact ⟨(ha.rewrite_bounds hs ht hm p.assumptions p.sourceBounds).mpr hb,
    (ha.rewrite_ty hs ht hm p.sourceType).symm ▸ hbody⟩

end ModalityInference.ComparisonFrozenContext
