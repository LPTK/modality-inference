import ModalityInference.ComparisonAnnotations
import ModalityInference.Proofs.ComparisonPartialModes
import ModalityInference.Proofs.ComparisonExactContext

/-! Scope and exact reconstruction of the partial-annotation prepass. -/
namespace ModalityInference.ComparisonAnnotations

theorem normalizeOuterFuel_modeVars (fuel : Nat) (t : Ty) :
    (ComparisonPartialModes.normalizeOuterFuel fuel t).modVars ⊆ t.modVars := by
  induction fuel generalizing t with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    cases t <;> try exact Finset.Subset.refl _
    next a m =>
      cases m <;> simp only [ComparisonPartialModes.normalizeOuterFuel]
      case compose m n =>
        simpa only [TypeExpr.modVars, ModExpr.vars, Finset.union_assoc] using
          ih (.modal (.modal a m) n)
      all_goals
        split
        · exact (ih a).trans (Finset.subset_union_left)
        · exact Finset.Subset.refl _

theorem dropIdentity_modeVars {t a : Ty} (h : ComparisonBody.dropIdentity t = some a) :
    a.modVars ⊆ t.modVars := by
  cases t <;> simp only [ComparisonBody.dropIdentity] at h <;> try contradiction
  split at h
  · cases h; exact Finset.subset_union_left
  · contradiction

theorem stripSharedDirect_modeVars {total : ModExpr → Bool} {left right a b : Ty}
    (h : ComparisonBody.stripSharedDirect total left right = some (a, b)) :
    a.modVars ⊆ left.modVars ∧ b.modVars ⊆ right.modVars := by
  cases hl : ComparisonBody.dropIdentity left with
  | some t =>
    simp only [ComparisonBody.stripSharedDirect, hl] at h
    cases h
    exact ⟨dropIdentity_modeVars hl, Finset.Subset.refl _⟩
  | none =>
    cases hr : ComparisonBody.dropIdentity right with
    | some t =>
      simp only [ComparisonBody.stripSharedDirect, hl, hr] at h
      cases h
      exact ⟨Finset.Subset.refl _, dropIdentity_modeVars hr⟩
    | none =>
      cases left <;> cases right <;>
        simp only [ComparisonBody.stripSharedDirect, hl, hr] at h <;> try contradiction
      split at h
      · cases h; exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩
      · contradiction

theorem stripShared_modeVars {total : ModExpr → Bool} {left right a b : Ty}
    (h : ComparisonBody.stripShared total left right = some (a, b)) :
    a.modVars ⊆ left.modVars ∧ b.modVars ⊆ right.modVars := by
  cases hd : ComparisonBody.stripSharedDirect total left right with
  | some pair =>
    simp only [ComparisonBody.stripShared, hd] at h
    exact stripSharedDirect_modeVars (hd.trans h)
  | none =>
    simp only [ComparisonBody.stripShared, hd] at h
    have hl := normalizeOuterFuel_modeVars (ComparisonPartialModes.modalitySize left) left
    have hr := normalizeOuterFuel_modeVars (ComparisonPartialModes.modalitySize right) right
    cases hn : ComparisonBody.stripSharedDirect total (ComparisonPartialModes.normalizeOuter left)
        (ComparisonPartialModes.normalizeOuter right) <;> simp only [hn] at h
    · split at h
      · contradiction
      · cases h; exact ⟨hl, hr⟩
    · have hs := stripSharedDirect_modeVars (hn.trans h)
      exact ⟨hs.1.trans hl, hs.2.trans hr⟩

theorem requests_support {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {indices : List Nat} (fuel : Nat) {reversed : Bool} {source target : Ty}
    {r : ComparisonPartialModes.Request}
    (hr : r ∈ requests p total indices fuel reversed source target) :
    r.target.vars ⊆ target.modVars := by
  induction fuel generalizing reversed source target with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    simp only [requests] at hr
    split at hr
    · split at hr
      · split at hr
        all_goals split at hr
        all_goals simp only [List.mem_singleton, List.not_mem_nil] at hr
        all_goals cases hr
        · exact Finset.subset_union_right
        · exact Finset.empty_subset _
      · simp at hr
    · split at hr
      · rename_i a b hs
        exact (ih hr).trans (stripShared_modeVars hs).2
      · split at hr
        all_goals try simp only [List.not_mem_nil] at hr
        all_goals rcases List.mem_append.mp hr with hr | hr
        all_goals first
          | exact (ih hr).trans Finset.subset_union_left
          | exact (ih hr).trans Finset.subset_union_right

theorem prepare_domain {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {name : Nat} (h : name ∈ (prepare p total).images.map Prod.fst) :
    name ∈ ComparisonPartialModes.eligible p := by
  exact (List.mem_filter.mp (ComparisonPartialModes.adapt_domain_subset h)).1

theorem prepare_bounds_fixed (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    (prepare p total).substitution.bounds p.sourceBounds = p.sourceBounds := by
  apply ComparisonPartialModes.adapt_bounds_fixed
  intro name hn c hc
  exact ComparisonPartialModes.eligible_avoids_bounds (List.mem_filter.mp hn).1 hc

theorem prepare_support {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {P : ModVar → Prop}
    (hf : ∀ n, p.nextMode ≤ n → n < (prepare p total).nextMode → P (.flex n))
    (ht : ∀ v ∈ p.targetType.modVars, P v)
    {entry : Nat × ModExpr} (he : entry ∈ (prepare p total).images) :
    ∀ v ∈ entry.2.vars, P v := by
  apply ComparisonPartialModes.adapt_support hf _ he
  intro r hr v hv
  exact ht v (requests_support _ hr hv)

theorem prepare_scoped {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    (ht : ∀ v ∈ p.targetType.modVars, ComparisonInstance.modeAllowed p v = false) :
    ComparisonExactContext.Scoped p (prepare p total).substitution := by
  constructor
  · simp [ComparisonPartialModes.Result.substitution]
  · intro name image hi
    have hn := ComparisonPartialModes.mem_eligible.mp
      (prepare_domain (List.mem_map.mpr ⟨(name, image), hi, rfl⟩))
    refine ⟨?_, prepare_support (P := fun v => ComparisonInstance.modeAllowed p v = false)
      (fun n hn _ => ?_) ht hi⟩
    · simp only [List.mem_range'] at hn
      simp [ComparisonInstance.modeAllowed]
      omega
    · simp [ComparisonInstance.modeAllowed]
      omega

theorem prepare_type (p : SchemePreparation.Prepared) (total : ModExpr → Bool)
    (v : TypeVar) : (prepare p total).substitution.type v = .var v := by
  cases v <;> rfl

theorem prepare_fixed {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    (v : ModVar) (hv : ComparisonInstance.modeAllowed p v = false) :
    (prepare p total).substitution.mode v = .var v := by
  cases v with
  | rigid => rfl
  | flex name =>
    apply Substitution.mode_fresh
    intro hn
    have hr := (ComparisonPartialModes.mem_eligible.mp (prepare_domain hn)).1
    simp only [List.mem_range'] at hr
    simp [ComparisonInstance.modeAllowed] at hv
    omega

theorem prepare_finish_bounds (p : SchemePreparation.Prepared) (total : ModExpr → Bool)
    (after : CompareSubstitution) :
    (ComparisonExactContext.finish (prepare p total).substitution after).bounds p.sourceBounds =
      after.bounds p.sourceBounds := by
  rw [ComparisonExactContext.finish_bounds, prepare_bounds_fixed]

theorem prepare_finish_body (p : SchemePreparation.Prepared) (total : ModExpr → Bool)
    (after : CompareSubstitution) :
    (ComparisonExactContext.finish (prepare p total).substitution after).ty p.sourceType =
      after.ty ((prepare p total).substitution.ty p.sourceType) :=
  ComparisonExactContext.finish_ty _ _ _

end ModalityInference.ComparisonAnnotations
