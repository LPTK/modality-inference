import ModalityInference.Proofs.ComparisonShapeSelection
import ModalityInference.Proofs.ComparisonShapeRetractionSyntax
import ModalityInference.Proofs.ComparisonSkeletonContext
import ModalityInference.Proofs.ComparisonPropagationComposition

/-! Source expressions commute with one simultaneous choice of shape cuts.
Retained templates preserve the instantiated syntax literally; other templates
preserve algebraic comparisons with a shared replacement at every occurrence. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonAlgebra ComparisonShapeSolver ComparisonSkeletonCoordinates

def Cut.templateType {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) : CompareTy :=
  ((Cut.ofTemplate choices ρ s).retract hc ⟨a, hs, hd,
    by simpa only [Cut.ofTemplate_source] using he⟩).type

theorem Cut.templateType_shaped {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) :
    (Cut.templateType choices ρ s hc a hs hd he).WellShaped Δ :=
  ((Cut.ofTemplate choices ρ s).retract hc ⟨a, hs, hd,
    by simpa only [Cut.ofTemplate_source] using he⟩).shaped

theorem Cut.templateType_defined {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) :
    (Cut.templateType choices ρ s hc a hs hd he).DefinedUnder Δ :=
  ((Cut.ofTemplate choices ρ s).retract hc ⟨a, hs, hd,
    by simpa only [Cut.ofTemplate_source] using he⟩).defined

theorem Cut.templateType_shape {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) :
    ComparisonShape.Equivalent Δ (Cut.templateType choices ρ s hc a hs hd he).shape
      (s.subst (choose choices ρ)) := by
  simpa only [Cut.ofTemplate_target] using
    ((Cut.ofTemplate choices ρ s).retract hc ⟨a, hs, hd,
      by simpa only [Cut.ofTemplate_source] using he⟩).shape_eq

theorem Cut.retract_type_of_keep {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    {c : Cut} (hc : c.Valid Δ φ) (a : Carrier Δ c.source) {s : ComparisonShape}
    (h : c = .keep s) : (c.retract hc a).type = a.type := by
  subst c
  rfl

theorem Cut.retract_type_congr {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    {c d : Cut} (hc : c.Valid Δ φ) (hd : d.Valid Δ φ)
    (a : Carrier Δ c.source) (b : Carrier Δ d.source)
    (he : c = d) (hab : a.type = b.type) : (c.retract hc a).type = (d.retract hd b).type := by
  subst d
  have hab' : a = b := by cases a; cases b; cases hab; rfl
  subst b
  rfl

theorem Cut.templateType_of_retained {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (hr : retained choices ρ s = true) : Cut.templateType choices ρ s hc a hs hd he = a := by
  apply Cut.retract_type_of_keep
  rw [Cut.ofTemplate.eq_def, hr]
  rfl

theorem retained_image {choices : List ComparisonShape} {ρ θ : TypeVar → ComparisonShape}
    {t : Ty} (hr : retained choices ρ ((ComparisonShape.ofTy t).subst θ) = true)
    {v : TypeVar} (hv : v ∈ t.typeVars) : retained choices ρ (θ v) = true := by
  apply retained_iff.mpr
  intro w hw
  apply retained_iff.mp hr w
  exact (mem_vars_subst (ComparisonShape.ofTy t) θ w).mpr
    ⟨v, (mem_vars_ofTy t v).mpr hv, hw⟩

/-- If the whole template is retained, simultaneous replacement leaves the
instantiated public type literally unchanged. -/
theorem selected_ty_eq_of_retained {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ θ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (σ τ : CompareSubstitution) (hs : σ.WellShaped Δ) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, ComparisonShape.Equivalent Δ (σ.type v).shape ((θ v).subst ρ))
    (hm : ∀ v ∈ t.modVars, τ.mode v = σ.mode v)
    (hi : ∀ v, ∀ hv : v ∈ t.typeVars, ∀ hd : (σ.type v).DefinedUnder Δ,
      τ.type v = Cut.templateType choices ρ (θ v) (valid (θ v))
        (σ.type v) (hs.type v) hd (ht v hv))
    (hd : (σ.ty t).DefinedUnder Δ)
    (hr : retained choices ρ ((ComparisonShape.ofTy t).subst θ) = true) : τ.ty t = σ.ty t := by
  apply CompareSubstitution.ty_congr_on
  · intro v hv
    rw [hi v hv (CompareTy.defined_ofTy_subst_types hd v hv)]
    exact Cut.templateType_of_retained _ _ _ _ _ _ _ _ (retained_image hr hv)
  · exact hm


theorem Cut.templateType_prod {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (s t : ComparisonShape) (a b : CompareTy)
    (ha : a.WellShaped Δ) (hb : b.WellShaped Δ)
    (hda : a.DefinedUnder Δ) (hdb : b.DefinedUnder Δ)
    (ea : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (eb : ComparisonShape.Equivalent Δ b.shape (t.subst ρ)) :
    let left := Cut.templateType choices ρ (.prod s t) (valid (.prod s t)) (.prod a b)
      ⟨ha, hb⟩ (CompareTy.definedUnder_prod_iff.mpr ⟨hda, hdb⟩)
      (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ])
    let right := CompareTy.prod
      (Cut.templateType choices ρ s (valid s) a ha hda ea)
      (Cut.templateType choices ρ t (valid t) b hb hdb eb)
    AlgebraSubtype Δ left right ∧ AlgebraSubtype Δ right left := by
  dsimp only
  by_cases hr : retained choices ρ (.prod s t) = true
  · have hrs : retained choices ρ s = true ∧ retained choices ρ t = true := by
      simpa [retained, ComparisonShape.vars] using hr
    rw [Cut.templateType_of_retained _ _ _ _ _ _ _ _ hr,
      Cut.templateType_of_retained _ _ _ _ _ _ _ _ hrs.1,
      Cut.templateType_of_retained _ _ _ _ _ _ _ _ hrs.2]
    exact ⟨.refl ⟨ha, hb⟩, .refl ⟨ha, hb⟩⟩
  · let ca := Cut.ofTemplate choices ρ s
    let cb := Cut.ofTemplate choices ρ t
    have he : Cut.ofTemplate choices ρ (.prod s t) = .prod ca cb := by
      rw [Cut.ofTemplate.eq_def, if_neg hr]
    have hc : (Cut.prod ca cb).Valid Δ φ := he ▸ valid (.prod s t)
    let ac : Carrier Δ ca.source := ⟨a, ha, hda, by simpa only [ca, Cut.ofTemplate_source] using ea⟩
    let bc : Carrier Δ cb.source := ⟨b, hb, hdb, by simpa only [cb, Cut.ofTemplate_source] using eb⟩
    have hx := Cut.retract_type_congr (valid (.prod s t)) hc
      (⟨.prod a b, ⟨ha, hb⟩, CompareTy.definedUnder_prod_iff.mpr ⟨hda, hdb⟩,
        by simpa only [Cut.ofTemplate_source] using
          (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ])⟩)
      (barePair false ac bc) he rfl
    change Cut.templateType choices ρ (.prod s t) (valid (.prod s t)) (.prod a b)
      ⟨ha, hb⟩ (CompareTy.definedUnder_prod_iff.mpr ⟨hda, hdb⟩)
      (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ]) = _ at hx
    rw [hx]
    exact Cut.retract_prod ca cb hc ac bc

theorem Cut.templateType_sum {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (s t : ComparisonShape) (a b : CompareTy)
    (ha : a.WellShaped Δ) (hb : b.WellShaped Δ)
    (hda : a.DefinedUnder Δ) (hdb : b.DefinedUnder Δ)
    (ea : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (eb : ComparisonShape.Equivalent Δ b.shape (t.subst ρ)) :
    let left := Cut.templateType choices ρ (.sum s t) (valid (.sum s t)) (.sum a b)
      ⟨ha, hb⟩ (CompareTy.definedUnder_sum_iff.mpr ⟨hda, hdb⟩)
      (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ])
    let right := CompareTy.sum
      (Cut.templateType choices ρ s (valid s) a ha hda ea)
      (Cut.templateType choices ρ t (valid t) b hb hdb eb)
    AlgebraSubtype Δ left right ∧ AlgebraSubtype Δ right left := by
  dsimp only
  by_cases hr : retained choices ρ (.sum s t) = true
  · have hrs : retained choices ρ s = true ∧ retained choices ρ t = true := by
      simpa [retained, ComparisonShape.vars] using hr
    rw [Cut.templateType_of_retained _ _ _ _ _ _ _ _ hr,
      Cut.templateType_of_retained _ _ _ _ _ _ _ _ hrs.1,
      Cut.templateType_of_retained _ _ _ _ _ _ _ _ hrs.2]
    exact ⟨.refl ⟨ha, hb⟩, .refl ⟨ha, hb⟩⟩
  · let ca := Cut.ofTemplate choices ρ s
    let cb := Cut.ofTemplate choices ρ t
    have he : Cut.ofTemplate choices ρ (.sum s t) = .sum ca cb := by
      rw [Cut.ofTemplate.eq_def, if_neg hr]
    have hc : (Cut.sum ca cb).Valid Δ φ := he ▸ valid (.sum s t)
    let ac : Carrier Δ ca.source := ⟨a, ha, hda, by simpa only [ca, Cut.ofTemplate_source] using ea⟩
    let bc : Carrier Δ cb.source := ⟨b, hb, hdb, by simpa only [cb, Cut.ofTemplate_source] using eb⟩
    have hx := Cut.retract_type_congr (valid (.sum s t)) hc
      (⟨.sum a b, ⟨ha, hb⟩, CompareTy.definedUnder_sum_iff.mpr ⟨hda, hdb⟩,
        by simpa only [Cut.ofTemplate_source] using
          (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ])⟩)
      (barePair true ac bc) he rfl
    change Cut.templateType choices ρ (.sum s t) (valid (.sum s t)) (.sum a b)
      ⟨ha, hb⟩ (CompareTy.definedUnder_sum_iff.mpr ⟨hda, hdb⟩)
      (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ]) = _ at hx
    rw [hx]
    exact Cut.retract_sum ca cb hc ac bc


theorem Cut.templateType_fn {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (s t : ComparisonShape) (a b : CompareTy)
    (ha : a.WellShaped Δ) (hb : b.WellShaped Δ)
    (hda : a.DefinedUnder Δ) (hdb : b.DefinedUnder Δ)
    (ea : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (eb : ComparisonShape.Equivalent Δ b.shape (t.subst ρ)) :
    let left := Cut.templateType choices ρ (.fn s t) (valid (.fn s t)) (.fn a b)
      ⟨ha, hb⟩ (CompareTy.definedUnder_fn_iff.mpr ⟨hda, hdb⟩)
      (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ])
    let right := CompareTy.fn
      (Cut.templateType choices ρ s (valid s) a ha hda ea)
      (Cut.templateType choices ρ t (valid t) b hb hdb eb)
    AlgebraSubtype Δ left right ∧ AlgebraSubtype Δ right left := by
  dsimp only
  by_cases hr : retained choices ρ (.fn s t) = true
  · have hrs : retained choices ρ s = true ∧ retained choices ρ t = true := by
      simpa [retained, ComparisonShape.vars] using hr
    rw [Cut.templateType_of_retained _ _ _ _ _ _ _ _ hr,
      Cut.templateType_of_retained _ _ _ _ _ _ _ _ hrs.1,
      Cut.templateType_of_retained _ _ _ _ _ _ _ _ hrs.2]
    exact ⟨.refl ⟨ha, hb⟩, .refl ⟨ha, hb⟩⟩
  · let ca := Cut.ofTemplate choices ρ s
    let cb := Cut.ofTemplate choices ρ t
    have he : Cut.ofTemplate choices ρ (.fn s t) = .fn ca cb := by
      rw [Cut.ofTemplate.eq_def, if_neg hr]
    have hc : (Cut.fn ca cb).Valid Δ φ := he ▸ valid (.fn s t)
    let ac : Carrier Δ ca.source := ⟨a, ha, hda, by simpa only [ca, Cut.ofTemplate_source] using ea⟩
    let bc : Carrier Δ cb.source := ⟨b, hb, hdb, by simpa only [cb, Cut.ofTemplate_source] using eb⟩
    have hx := Cut.retract_type_congr (valid (.fn s t)) hc
      (⟨.fn a b, ⟨ha, hb⟩, CompareTy.definedUnder_fn_iff.mpr ⟨hda, hdb⟩,
        by simpa only [Cut.ofTemplate_source] using
          (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ])⟩)
      (bareFunction ac bc) he rfl
    change Cut.templateType choices ρ (.fn s t) (valid (.fn s t)) (.fn a b)
      ⟨ha, hb⟩ (CompareTy.definedUnder_fn_iff.mpr ⟨hda, hdb⟩)
      (fun ψ hψ => by simp only [CompareTy.shape, ComparisonShape.subst, ea ψ hψ, eb ψ hψ]) = _ at hx
    rw [hx]
    exact Cut.retract_fn ca cb hc ac bc



theorem Cut.templateType_modal {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) (m : ModExpr) (hm : DefinedMode Δ m) :
    let acted := Cut.templateType choices ρ s hc (.modal a m) hs
      (CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩) he
    let plain := CompareTy.modal (Cut.templateType choices ρ s hc a hs hd he) m
    AlgebraSubtype Δ acted plain ∧ AlgebraSubtype Δ plain acted :=
  Cut.retract_modal (Cut.ofTemplate choices ρ s) hc
    ⟨a, hs, hd, by simpa only [Cut.ofTemplate_source] using he⟩ (GuardedMode.ofDefined m hm)

theorem Cut.templateType_mono {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (ea : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (eb : ComparisonShape.Equivalent Δ b.shape (s.subst ρ)) :
    AlgebraSubtype Δ (Cut.templateType choices ρ s hc a h.wellShaped_left ha ea)
      (Cut.templateType choices ρ s hc b h.wellShaped_right hb eb) :=
  Cut.retract_mono (Cut.ofTemplate choices ρ s) hc
    (a := ⟨a, h.wellShaped_left, ha, by simpa only [Cut.ofTemplate_source] using ea⟩)
    (b := ⟨b, h.wellShaped_right, hb, by simpa only [Cut.ofTemplate_source] using eb⟩) h


/-- One replacement image is used at every occurrence of a source parameter.
The induced cut commutes with a whole public type, including function variance. -/
theorem selected_ty {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (choices : List ComparisonShape) (ρ θ : TypeVar → ComparisonShape)
    (valid : ∀ s, (Cut.ofTemplate choices ρ s).Valid Δ φ)
    (σ τ : CompareSubstitution) (hs : σ.WellShaped Δ) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, ComparisonShape.Equivalent Δ (σ.type v).shape ((θ v).subst ρ))
    (hm : ∀ v ∈ t.modVars, τ.mode v = σ.mode v)
    (hi : ∀ v, ∀ hv : v ∈ t.typeVars, ∀ hd : (σ.type v).DefinedUnder Δ,
      τ.type v = Cut.templateType choices ρ (θ v) (valid (θ v))
        (σ.type v) (hs.type v) hd (ht v hv))
    (hd : (σ.ty t).DefinedUnder Δ) :
    let image := Cut.templateType choices ρ ((ComparisonShape.ofTy t).subst θ)
      (valid ((ComparisonShape.ofTy t).subst θ)) (σ.ty t) (hs.ty t) hd
      (ty_shape_realized σ t θ ρ ht)
    AlgebraSubtype Δ image (τ.ty t) ∧ AlgebraSubtype Δ (τ.ty t) image := by
  induction t with
  | var v =>
    have he := hi v (by simp [TypeExpr.typeVars]) hd
    change AlgebraSubtype Δ _ (τ.type v) ∧ AlgebraSubtype Δ (τ.type v) _
    rw [he]
    exact ⟨.refl (Cut.templateType_shaped _ _ _ _ _ _ _ _),
      .refl (Cut.templateType_shaped _ _ _ _ _ _ _ _)⟩
  | unit =>
    dsimp only
    rw [Cut.templateType_of_retained _ _ _ _ _ _ _ _ rfl]
    exact ⟨.refl trivial, .refl trivial⟩
  | credit =>
    dsimp only
    rw [Cut.templateType_of_retained _ _ _ _ _ _ _ _ rfl]
    exact ⟨.refl trivial, .refl trivial⟩
  | prod a b iha ihb =>
    have ha := (CompareTy.definedUnder_prod_iff.mp hd).1
    have hb := (CompareTy.definedUnder_prod_iff.mp hd).2
    have hta := fun v hv => ht v (Finset.mem_union_left _ hv)
    have htb := fun v hv => ht v (Finset.mem_union_right _ hv)
    have h₁ := iha hta (fun v hv => hm v (Finset.mem_union_left _ hv))
      (fun v hv => hi v (Finset.mem_union_left _ hv)) ha
    have h₂ := ihb htb (fun v hv => hm v (Finset.mem_union_right _ hv))
      (fun v hv => hi v (Finset.mem_union_right _ hv)) hb
    have hp := Cut.templateType_prod choices ρ valid ((ComparisonShape.ofTy a).subst θ)
      ((ComparisonShape.ofTy b).subst θ) (σ.ty a) (σ.ty b) (hs.ty a) (hs.ty b) ha hb
      (ty_shape_realized σ a θ ρ hta) (ty_shape_realized σ b θ ρ htb)
    exact ⟨hp.1.trans (ComparisonDefinedCovers.prod_congr h₁.1 h₂.1),
      (ComparisonDefinedCovers.prod_congr h₁.2 h₂.2).trans hp.2⟩
  | sum a b iha ihb =>
    have ha := (CompareTy.definedUnder_sum_iff.mp hd).1
    have hb := (CompareTy.definedUnder_sum_iff.mp hd).2
    have hta := fun v hv => ht v (Finset.mem_union_left _ hv)
    have htb := fun v hv => ht v (Finset.mem_union_right _ hv)
    have h₁ := iha hta (fun v hv => hm v (Finset.mem_union_left _ hv))
      (fun v hv => hi v (Finset.mem_union_left _ hv)) ha
    have h₂ := ihb htb (fun v hv => hm v (Finset.mem_union_right _ hv))
      (fun v hv => hi v (Finset.mem_union_right _ hv)) hb
    have hp := Cut.templateType_sum choices ρ valid ((ComparisonShape.ofTy a).subst θ)
      ((ComparisonShape.ofTy b).subst θ) (σ.ty a) (σ.ty b) (hs.ty a) (hs.ty b) ha hb
      (ty_shape_realized σ a θ ρ hta) (ty_shape_realized σ b θ ρ htb)
    exact ⟨hp.1.trans (ComparisonDefinedCovers.sum_congr h₁.1 h₂.1),
      (ComparisonDefinedCovers.sum_congr h₁.2 h₂.2).trans hp.2⟩
  | fn a b iha ihb =>
    have ha := (CompareTy.definedUnder_fn_iff.mp hd).1
    have hb := (CompareTy.definedUnder_fn_iff.mp hd).2
    have hta := fun v hv => ht v (Finset.mem_union_left _ hv)
    have htb := fun v hv => ht v (Finset.mem_union_right _ hv)
    have h₁ := iha hta (fun v hv => hm v (Finset.mem_union_left _ hv))
      (fun v hv => hi v (Finset.mem_union_left _ hv)) ha
    have h₂ := ihb htb (fun v hv => hm v (Finset.mem_union_right _ hv))
      (fun v hv => hi v (Finset.mem_union_right _ hv)) hb
    have hp := Cut.templateType_fn choices ρ valid ((ComparisonShape.ofTy a).subst θ)
      ((ComparisonShape.ofTy b).subst θ) (σ.ty a) (σ.ty b) (hs.ty a) (hs.ty b) ha hb
      (ty_shape_realized σ a θ ρ hta) (ty_shape_realized σ b θ ρ htb)
    exact ⟨hp.1.trans (ComparisonDefinedCovers.fn_congr h₁.2 h₂.1),
      (ComparisonDefinedCovers.fn_congr h₁.1 h₂.2).trans hp.2⟩
  | modal a m ih =>
    have ha := (CompareTy.definedUnder_modal_iff.mp hd).1
    have hmode := (CompareTy.definedUnder_modal_iff.mp hd).2
    have hp := Cut.templateType_modal choices ρ ((ComparisonShape.ofTy a).subst θ)
      (valid ((ComparisonShape.ofTy a).subst θ)) (σ.ty a) (hs.ty a) ha
      (ty_shape_realized σ a θ ρ ht) (m.subst σ.mode) hmode
    have hh := ih ht (fun v hv => hm v (Finset.mem_union_left _ hv)) hi ha
    have hms : m.subst τ.mode = m.subst σ.mode :=
      m.subst_congr (fun v hv => hm v (Finset.mem_union_right _ hv))
    dsimp only [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst]
    rw [hms]
    exact ⟨hp.1.trans (.congr hh.1 (.refl hmode)),
      (AlgebraSubtype.congr hh.2 (.refl hmode)).trans hp.2⟩

end ModalityInference.ComparisonShapeRetraction
