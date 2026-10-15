import ModalityInference.Proofs.ComparisonSkeletonShapeRealizer

namespace ModalityInference.ComparisonSkeletonCoordinates

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeleton ComparisonShapeSolver

theorem ty_shape_realized {Δ : Bounds} (σ : CompareSubstitution) (t : Ty)
    (θ ρ : TypeVar → ComparisonShape)
    (ht : ∀ v ∈ t.typeVars, ComparisonShape.Equivalent Δ (σ.type v).shape ((θ v).subst ρ)) :
    ComparisonShape.Equivalent Δ (σ.ty t).shape (((ComparisonShape.ofTy t).subst θ).subst ρ) := by
  intro η hη
  rw [σ.ty_shape, subst_comp, subst_comp, subst_comp]
  apply subst_congr
  intro v hv
  simpa only [subst_comp] using ht v ((mem_vars_ofTy t v).mp hv) η hη

/-- Rebasing is simultaneous across a whole public type expression. In
particular, repeated occurrences use one replacement image, including under
contravariant function domains and arbitrary total modality expressions. -/
theorem rebase_ty {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ)
    (θ : TypeVar → ComparisonShape) (σ τ : CompareSubstitution)
    (hs : σ.WellShaped Δ) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, ComparisonShape.Equivalent Δ (σ.type v).shape ((θ v).subst ρ))
    (hm : ∀ v ∈ t.modVars, τ.mode v = σ.mode v)
    (hi : ∀ v, ∀ hv : v ∈ t.typeVars, ∀ hd : (σ.type v).DefinedUnder Δ,
      let image := (rebase hΔ p ρ hρ (θ v) (σ.type v) (hs.type v) hd (ht v hv)).reify
      AlgebraSubtype Δ image (τ.type v) ∧ AlgebraSubtype Δ (τ.type v) image)
    (hd : (σ.ty t).DefinedUnder Δ) :
    let image := (rebase hΔ p ρ hρ ((ComparisonShape.ofTy t).subst θ) (σ.ty t)
      (hs.ty t) hd (ty_shape_realized σ t θ ρ ht)).reify
    AlgebraSubtype Δ image (τ.ty t) ∧ AlgebraSubtype Δ (τ.ty t) image := by
  induction t with
  | var v => exact hi v (by simp [TypeExpr.typeVars]) hd
  | unit => exact ⟨.identity trivial, .identityRev trivial⟩
  | credit => exact ⟨.identity trivial, .identityRev trivial⟩
  | prod a b iha ihb =>
    have h₁ := iha (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))
      (fun v hv => hi v (Finset.mem_union_left _ hv))
      (CompareTy.definedUnder_prod_iff.mp hd).1
    have h₂ := ihb (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))
      (fun v hv => hi v (Finset.mem_union_right _ hv))
      (CompareTy.definedUnder_prod_iff.mp hd).2
    have he := Scalar.submode (Scalar.refl (Scalar.identity (Δ := Δ)))
    have hτ : (τ.ty (.prod a b)).WellShaped Δ :=
      ⟨h₁.1.wellShaped_right, h₂.1.wellShaped_right⟩
    exact ⟨(AlgebraSubtype.prod (.congr h₁.1 he) (.congr h₂.1 he)).trans (.identity hτ),
      (AlgebraSubtype.identityRev hτ).trans (.prod (.congr h₁.2 he) (.congr h₂.2 he))⟩
  | sum a b iha ihb =>
    have h₁ := iha (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))
      (fun v hv => hi v (Finset.mem_union_left _ hv))
      (CompareTy.definedUnder_sum_iff.mp hd).1
    have h₂ := ihb (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))
      (fun v hv => hi v (Finset.mem_union_right _ hv))
      (CompareTy.definedUnder_sum_iff.mp hd).2
    have he := Scalar.submode (Scalar.refl (Scalar.identity (Δ := Δ)))
    have hτ : (τ.ty (.sum a b)).WellShaped Δ :=
      ⟨h₁.1.wellShaped_right, h₂.1.wellShaped_right⟩
    exact ⟨(AlgebraSubtype.sum (.congr h₁.1 he) (.congr h₂.1 he)).trans (.identity hτ),
      (AlgebraSubtype.identityRev hτ).trans (.sum (.congr h₁.2 he) (.congr h₂.2 he))⟩
  | fn a b iha ihb =>
    have h₁ := iha (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))
      (fun v hv => hi v (Finset.mem_union_left _ hv))
      (CompareTy.definedUnder_fn_iff.mp hd).1
    have h₂ := ihb (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))
      (fun v hv => hi v (Finset.mem_union_right _ hv))
      (CompareTy.definedUnder_fn_iff.mp hd).2
    have he := Scalar.future_submode (Scalar.future_refl (Scalar.identity (Δ := Δ)))
    have hτ : (τ.ty (.fn a b)).WellShaped Δ :=
      ⟨h₁.1.wellShaped_right, h₂.1.wellShaped_right⟩
    exact ⟨(AlgebraSubtype.fn h₁.2 h₂.1 he).trans (.identity hτ),
      (AlgebraSubtype.identityRev hτ).trans (.fn h₁.1 h₂.2 he)⟩
  | modal a m ih =>
    have ha := (CompareTy.definedUnder_modal_iff.mp hd).1
    have hmode := (CompareTy.definedUnder_modal_iff.mp hd).2
    let mode := GuardedMode.ofDefined (m.subst σ.mode) hmode
    let tree := rebase hΔ p ρ hρ ((ComparisonShape.ofTy a).subst θ) (σ.ty a)
      (hs.ty a) ha (ty_shape_realized σ a θ ρ ht)
    have hn := rebase_modal hΔ p ρ hρ ((ComparisonShape.ofTy a).subst θ) (σ.ty a)
      (hs.ty a) ha (ty_shape_realized σ a θ ρ ht) mode
    have hc := Tree.reify_modal tree mode
    have hh := ih ht (fun v hv => hm v (Finset.mem_union_left _ hv)) hi ha
    have he := Scalar.submode (Scalar.refl mode)
    have hms : m.subst τ.mode = m.subst σ.mode :=
      m.subst_congr (fun v hv => hm v (Finset.mem_union_right _ hv))
    dsimp only [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst]
    rw [hms]
    exact ⟨(Tree.reify_le hn.1).trans (hc.1.trans (.congr hh.1 he)),
      (AlgebraSubtype.congr hh.2 he).trans (hc.2.trans (Tree.reify_le hn.2))⟩

end ModalityInference.ComparisonSkeletonCoordinates
