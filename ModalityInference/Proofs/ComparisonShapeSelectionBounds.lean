import ModalityInference.Proofs.ComparisonShapeSelectionContext

/-! One selected shape witness preserves every guarded source obligation.
The comparison body is retained literally when its resolved template has an
input anchor, without imposing additional conditions on its public target. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonAlgebra ComparisonShapeSolver ComparisonSkeletonCoordinates

structure Selected {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (θ : TypeVar → ComparisonShape) (σ τ : CompareSubstitution) (types : Finset TypeVar) where
  shaped : σ.WellShaped Δ
  realized : ∀ v ∈ types, ComparisonShape.Equivalent Δ (σ.type v).shape ((θ v).subst ρ)
  images : ∀ v, ∀ hv : v ∈ types, ∀ hd : (σ.type v).DefinedUnder Δ,
    τ.type v = Cut.templateType choices ρ (θ v) (valid (θ v))
      (σ.type v) (shaped.type v) hd (realized v hv)
  modes : ∀ v, τ.mode v = σ.mode v

theorem Cut.templateType_shape_congr {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (s t : ComparisonShape) (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (es : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (et : ComparisonShape.Equivalent Δ a.shape (t.subst ρ)) (he : s = t) :
    Cut.templateType choices ρ s (valid s) a hs hd es =
      Cut.templateType choices ρ t (valid t) a hs hd et := by
  subst t
  rfl

namespace Selected

variable {Δ : Bounds} {φ : TypeVar → ComparisonShape} {choices : List ComparisonShape}
    {ρ θ : TypeVar → ComparisonShape}
    {valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ}
    {σ τ : CompareSubstitution} {types : Finset TypeVar}
    (h : Selected choices ρ valid θ σ τ types)

include h

theorem ty_equivalent (t : Ty) (ht : t.typeVars ⊆ types) (hd : (σ.ty t).DefinedUnder Δ) :
    let image := Cut.templateType choices ρ ((ComparisonShape.ofTy t).subst θ)
      (valid ((ComparisonShape.ofTy t).subst θ)) (σ.ty t) (h.shaped.ty t) hd
      (ty_shape_realized σ t θ ρ (fun v hv => h.realized v (ht hv)))
    AlgebraSubtype Δ image (τ.ty t) ∧ AlgebraSubtype Δ (τ.ty t) image :=
  selected_ty choices ρ θ valid σ τ h.shaped t
    (fun v hv => h.realized v (ht hv)) (fun v _ => h.modes v)
    (fun v hv => h.images v (ht hv)) hd

theorem ty_eq_of_retained (t : Ty) (ht : t.typeVars ⊆ types) (hd : (σ.ty t).DefinedUnder Δ)
    (hr : retained choices ρ ((ComparisonShape.ofTy t).subst θ) = true) : τ.ty t = σ.ty t :=
  selected_ty_eq_of_retained choices ρ θ valid σ τ h.shaped t
    (fun v hv => h.realized v (ht hv)) (fun v _ => h.modes v)
    (fun v hv => h.images v (ht hv)) hd hr

theorem type_defined {v : TypeVar} (hv : v ∈ types) (hd : (σ.type v).DefinedUnder Δ) :
    (τ.type v).DefinedUnder Δ := by
  rw [h.images v hv hd]
  exact Cut.templateType_defined _ _ _ _ _ _ _ _

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

theorem type_shaped {v : TypeVar} (hv : v ∈ types) (hd : (σ.type v).DefinedUnder Δ) :
    (τ.type v).WellShaped Δ := by
  rw [h.images v hv hd]
  exact Cut.templateType_shaped _ _ _ _ _ _ _ _

theorem type_shape {v : TypeVar} (hv : v ∈ types) (hd : (σ.type v).DefinedUnder Δ) :
    ComparisonShape.Equivalent Δ (τ.type v).shape ((θ v).subst (choose choices ρ)) := by
  rw [h.images v hv hd]
  exact Cut.templateType_shape _ _ _ _ _ _ _ _

theorem ty_shaped (t : Ty) (ht : t.typeVars ⊆ types) (hd : (σ.ty t).DefinedUnder Δ) :
    (τ.ty t).WellShaped Δ := (h.ty_equivalent t ht hd).1.wellShaped_right

theorem subtype {a b : Ty} (ha : a.typeVars ⊆ types) (hb : b.typeVars ⊆ types)
    (hshape : (ComparisonShape.ofTy a).subst θ = (ComparisonShape.ofTy b).subst θ)
    (hda : (σ.ty a).DefinedUnder Δ) (hdb : (σ.ty b).DefinedUnder Δ)
    (hab : AlgebraSubtype Δ (σ.ty a) (σ.ty b)) : AlgebraSubtype Δ (τ.ty a) (τ.ty b) := by
  have ea := ty_shape_realized σ a θ ρ (fun v hv => h.realized v (ha hv))
  have eb := ty_shape_realized σ b θ ρ (fun v hv => h.realized v (hb hv))
  have eb' : ComparisonShape.Equivalent Δ (σ.ty b).shape
      (((ComparisonShape.ofTy a).subst θ).subst ρ) := hshape.symm ▸ eb
  have hn := Cut.templateType_mono choices ρ ((ComparisonShape.ofTy a).subst θ)
    (valid ((ComparisonShape.ofTy a).subst θ)) hab hda hdb ea eb'
  rw [Cut.templateType_shape_congr choices ρ valid _ _ (σ.ty b) _ hdb eb' eb hshape] at hn
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

/-- Retained body templates preserve the original comparison without any
additional condition on the public target. -/
theorem body {source target : Ty} (ht : source.typeVars ⊆ types)
    (hr : retained choices ρ ((ComparisonShape.ofTy source).subst θ) = true)
    (hs : (σ.ty source).DefinedUnder Δ)
    (hab : AlgebraSubtype Δ (σ.ty source) (.ofTy target)) :
    AlgebraSubtype Δ (τ.ty source) (.ofTy target) := by
  rw [h.ty_eq_of_retained source ht hs hr]
  exact hab

end Selected

end ModalityInference.ComparisonShapeRetraction
