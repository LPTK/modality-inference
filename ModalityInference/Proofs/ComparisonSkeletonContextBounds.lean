import ModalityInference.Proofs.ComparisonSkeletonContext

namespace ModalityInference.ComparisonSkeletonCoordinates

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeleton ComparisonShapeSolver

structure Rebased {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ)
    (θ : TypeVar → ComparisonShape) (σ τ : CompareSubstitution) (types : Finset TypeVar) where
  shaped : σ.WellShaped Δ
  realized : ∀ v ∈ types, ComparisonShape.Equivalent Δ (σ.type v).shape ((θ v).subst ρ)
  images : ∀ v, ∀ hv : v ∈ types, ∀ hd : (σ.type v).DefinedUnder Δ,
    τ.type v = (rebase hΔ p ρ hρ (θ v) (σ.type v) (shaped.type v) hd (realized v hv)).reify
  modes : ∀ v, τ.mode v = σ.mode v

theorem rebase_reify_shape_congr {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ)
    (s t : ComparisonShape) (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (es : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (et : ComparisonShape.Equivalent Δ a.shape (t.subst ρ)) (he : s = t) :
    (rebase hΔ p ρ hρ s a hs hd es).reify = (rebase hΔ p ρ hρ t a hs hd et).reify := by
  subst t
  rfl

namespace Rebased

variable {Δ : Bounds} {hΔ : Residual Δ} {p : SchemePreparation.Prepared}
    {ρ : TypeVar → ComparisonShape} {hρ : Fixes (sourceAllowed p) ρ}
    {θ : TypeVar → ComparisonShape} {σ τ : CompareSubstitution} {types : Finset TypeVar}
    (h : Rebased hΔ p ρ hρ θ σ τ types)

include h

theorem ty_equivalent (t : Ty) (ht : t.typeVars ⊆ types) (hd : (σ.ty t).DefinedUnder Δ) :
    let tree := rebase hΔ p ρ hρ ((ComparisonShape.ofTy t).subst θ) (σ.ty t)
      (h.shaped.ty t) hd (ty_shape_realized σ t θ ρ (fun v hv => h.realized v (ht hv)))
    AlgebraSubtype Δ tree.reify (τ.ty t) ∧ AlgebraSubtype Δ (τ.ty t) tree.reify := by
  apply rebase_ty hΔ p ρ hρ θ σ τ h.shaped t
    (fun v hv => h.realized v (ht hv)) (fun v _ => h.modes v)
  intro v hv hd
  rw [h.images v (ht hv) hd]
  exact ⟨.refl (Tree.reify_shaped _), .refl (Tree.reify_shaped _)⟩

theorem type_defined {v : TypeVar} (hv : v ∈ types) (hd : (σ.type v).DefinedUnder Δ) :
    (τ.type v).DefinedUnder Δ := by
  rw [h.images v hv hd]
  exact Tree.reify_defined _

theorem ty_defined (t : Ty) (ht : t.typeVars ⊆ types) (hd : (σ.ty t).DefinedUnder Δ) :
    (τ.ty t).DefinedUnder Δ := by
  induction t with
  | var v => exact h.type_defined (ht (by simp [TypeExpr.typeVars])) hd
  | unit | credit => exact hd
  | prod a b iha ihb =>
    exact CompareTy.definedUnder_prod_iff.mpr
      ⟨iha (fun v hv => ht (Finset.mem_union_left _ hv)) (CompareTy.definedUnder_prod_iff.mp hd).1,
       ihb (fun v hv => ht (Finset.mem_union_right _ hv)) (CompareTy.definedUnder_prod_iff.mp hd).2⟩
  | sum a b iha ihb =>
    exact CompareTy.definedUnder_sum_iff.mpr
      ⟨iha (fun v hv => ht (Finset.mem_union_left _ hv)) (CompareTy.definedUnder_sum_iff.mp hd).1,
       ihb (fun v hv => ht (Finset.mem_union_right _ hv)) (CompareTy.definedUnder_sum_iff.mp hd).2⟩
  | fn a b iha ihb =>
    exact CompareTy.definedUnder_fn_iff.mpr
      ⟨iha (fun v hv => ht (Finset.mem_union_left _ hv)) (CompareTy.definedUnder_fn_iff.mp hd).1,
       ihb (fun v hv => ht (Finset.mem_union_right _ hv)) (CompareTy.definedUnder_fn_iff.mp hd).2⟩
  | modal a m ih =>
    refine CompareTy.definedUnder_modal_iff.mpr ⟨ih ht (CompareTy.definedUnder_modal_iff.mp hd).1, ?_⟩
    have he := m.subst_congr (fun v _ => h.modes v)
    rw [he]
    exact (CompareTy.definedUnder_modal_iff.mp hd).2

theorem subtype {a b : Ty} (ha : a.typeVars ⊆ types) (hb : b.typeVars ⊆ types)
    (hshape : (ComparisonShape.ofTy a).subst θ = (ComparisonShape.ofTy b).subst θ)
    (hda : (σ.ty a).DefinedUnder Δ) (hdb : (σ.ty b).DefinedUnder Δ)
    (hab : AlgebraSubtype Δ (σ.ty a) (σ.ty b)) : AlgebraSubtype Δ (τ.ty a) (τ.ty b) := by
  have ea := ty_shape_realized σ a θ ρ (fun v hv => h.realized v (ha hv))
  have eb := ty_shape_realized σ b θ ρ (fun v hv => h.realized v (hb hv))
  have eb' : ComparisonShape.Equivalent Δ (σ.ty b).shape
      (((ComparisonShape.ofTy a).subst θ).subst ρ) := hshape.symm ▸ eb
  have hn := Tree.reify_le (rebase_le hΔ p ρ hρ hda hdb hab ea eb')
  rw [rebase_reify_shape_congr hΔ p ρ hρ _ _ (σ.ty b) _ hdb eb' eb hshape] at hn
  exact (h.ty_equivalent a ha hda).2.trans (hn.trans (h.ty_equivalent b hb hdb).1)

theorem sub {a b : Ty} (ha : a.typeVars ⊆ types) (hb : b.typeVars ⊆ types)
    (hshape : (ComparisonShape.ofTy a).subst θ = (ComparisonShape.ofTy b).subst θ)
    (hab : AlgebraEntails Δ (.sub (σ.ty a) (σ.ty b))) :
    AlgebraEntails Δ (.sub (τ.ty a) (τ.ty b)) :=
  ⟨h.subtype ha hb hshape hab.2.1 hab.2.2 hab.1,
    h.ty_defined a ha hab.2.1, h.ty_defined b hb hab.2.2⟩

theorem constraint (c : Constraint) (ht : c.typeVars ⊆ types)
    (hshape : ComparisonShapeSolver.Models (ComparisonShape.pairs [c]) θ)
    (hc : AlgebraEntails Δ (σ.constraint c)) : AlgebraEntails Δ (τ.constraint c) := by
  cases c with
  | sub a b =>
    exact h.sub (fun v hv => ht (Finset.mem_union_left _ hv))
      (fun v hv => ht (Finset.mem_union_right _ hv)) (hshape (ComparisonShape.ofTy a, ComparisonShape.ofTy b)
        (by simp [ComparisonShape.pairs])) hc
  | equiv a b =>
    have ha : a.typeVars ⊆ types := fun _ hv => ht (Finset.mem_union_left _ hv)
    have hb : b.typeVars ⊆ types := fun _ hv => ht (Finset.mem_union_right _ hv)
    have he := hshape (ComparisonShape.ofTy a, ComparisonShape.ofTy b) (by simp [ComparisonShape.pairs])
    exact ⟨h.subtype ha hb he hc.2.2.1 hc.2.2.2 hc.1,
      h.subtype hb ha he.symm hc.2.2.2 hc.2.2.1 hc.2.1,
      h.ty_defined a ha hc.2.2.1, h.ty_defined b hb hc.2.2.2⟩
  | equal v a =>
    have ha : a.typeVars ⊆ types := fun w hw => ht (Finset.mem_insert_of_mem hw)
    have hv : (TypeExpr.var v : Ty).typeVars ⊆ types := by
      intro w hw
      simp only [TypeExpr.typeVars, Finset.mem_singleton] at hw
      subst w
      exact ht (Finset.mem_insert_self _ _)
    have he := hshape (ComparisonShape.var v, ComparisonShape.ofTy a) (by simp [ComparisonShape.pairs])
    rw [σ.algebra_equal_iff] at hc
    rw [τ.algebra_equal_iff]
    exact ⟨h.sub hv ha he hc.1, h.sub ha hv he.symm hc.2⟩
  | mode m n =>
    have hm := m.subst_congr (fun v _ => h.modes v)
    have hn := n.subst_congr (fun v _ => h.modes v)
    simpa only [CompareSubstitution.constraint, hm, hn] using hc
  | defined m =>
    have hm := m.subst_congr (fun v _ => h.modes v)
    simpa only [CompareSubstitution.constraint, hm] using hc

theorem bounds (cs : Bounds) (ht : cs.typeVars ⊆ types)
    (hshape : ComparisonShapeSolver.Models (ComparisonShape.pairs cs) θ)
    (hc : AlgebraEntailsAll Δ (σ.bounds cs)) : AlgebraEntailsAll Δ (τ.bounds cs) := by
  intro out hout
  obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hout
  apply h.constraint c (fun v hv => ht ((cs.mem_typeVars_iff v).mpr ⟨c, hc', hv⟩))
  · intro pair hp
    apply hshape pair
    simp only [ComparisonShape.pairs, List.flatMap_singleton] at hp
    exact List.mem_flatMap.mpr ⟨c, hc', hp⟩
  · exact hc _ (List.mem_map.mpr ⟨c, hc', rfl⟩)

/-- The normalized shared witness preserves a defined body comparison while
fixing its public target. Source obligations and body definedness remain separate. -/
theorem body {source target : Ty} (ht : source.typeVars ⊆ types)
    (hf : FixedShape p ((ComparisonShape.ofTy source).subst θ))
    (hs : (σ.ty source).DefinedUnder Δ) (hd : (CompareTy.ofTy target).DefinedUnder Δ)
    (hab : AlgebraSubtype Δ (σ.ty source) (.ofTy target)) :
    AlgebraSubtype Δ (τ.ty source) (.ofTy target) := by
  have ea := ty_shape_realized σ source θ ρ (fun v hv => h.realized v (ht hv))
  have eb := hab.shape_equivalent.symm.trans ea
  have hn := Tree.reify_le (rebase_le hΔ p ρ hρ hs hd hab ea eb)
  exact (h.ty_equivalent source ht hs).2.trans (hn.trans
    (rebase_public_at hΔ p ρ hρ target hd _ hf eb).1)

end Rebased

end ModalityInference.ComparisonSkeletonCoordinates
