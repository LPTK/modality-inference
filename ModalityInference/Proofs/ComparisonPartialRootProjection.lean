import ModalityInference.Proofs.ComparisonRootProjection

namespace ModalityInference.ComparisonStructuralProjection

open ComparisonAlgebra

/-- Retain the function-root affinity rule while erasing its children. -/
def rootBase (kind : Nat) : CompareTy :=
  if kind = 5 then .fn .unit .unit else .unit

/-- A root coordinate retaining exact partial actions and lattice nodes. -/
def rootType (kind : Nat) : CompareTy → CompareTy
  | .modal a m => .modal (rootType kind a) m
  | .join a b => .join (rootType kind a) (rootType kind b)
  | .meet a b => .meet (rootType kind a) (rootType kind b)
  | _ => rootBase kind

 theorem rootBase_shaped (Δ : Bounds) (kind : Nat) : (rootBase kind).WellShaped Δ := by
  unfold rootBase
  split <;> trivial

 theorem rootBase_defined (Δ : Bounds) (kind : Nat) : (rootBase kind).DefinedUnder Δ := by
  unfold rootBase
  split <;> intro η hη c hc <;> exact (List.not_mem_nil hc).elim

 theorem rootType_shape (kind : Nat) (a : CompareTy) :
    (rootType kind a).shape = (rootBase kind).shape := by
  induction a <;> first | rfl | assumption

 theorem rootType_shaped (Δ : Bounds) (kind : Nat) (a : CompareTy) :
    (rootType kind a).WellShaped Δ := by
  induction a with
  | modal a m ih => exact ih
  | join a b ia ib | meet a b ia ib =>
    exact ⟨ia, ib, by rw [rootType_shape, rootType_shape]; exact .refl⟩
  | _ => exact rootBase_shaped Δ kind

 theorem rootType_defined {Δ : Bounds} (kind : Nat) {a : CompareTy}
    (hd : a.DefinedUnder Δ) : (rootType kind a).DefinedUnder Δ := by
  induction a with
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp hd
    exact CompareTy.definedUnder_modal_iff.mpr ⟨ih hh.1, hh.2⟩
  | join a b ia ib =>
    have hh := CompareTy.definedUnder_join_iff.mp hd
    exact CompareTy.definedUnder_join_iff.mpr ⟨ia hh.1, ib hh.2⟩
  | meet a b ia ib =>
    have hh := CompareTy.definedUnder_meet_iff.mp hd
    exact CompareTy.definedUnder_meet_iff.mpr ⟨ia hh.1, ib hh.2⟩
  | _ => exact rootBase_defined Δ kind

 theorem rootType_compatible {Δ : Bounds} (kind : Nat) {a b : CompareTy}
    (h : Compatible Δ a b) : Compatible Δ (rootType kind a) (rootType kind b) :=
  ⟨⟨rootType_shaped Δ kind a, rootType_shaped Δ kind b,
      by rw [rootType_shape, rootType_shape]; exact .refl⟩,
    rootType_defined kind h.2.1, rootType_defined kind h.2.2⟩

@[simp] theorem rootType_typeOp (kind : Nat) (p : Bool) (a b : CompareTy) :
    rootType kind (typeOp p a b) = typeOp p (rootType kind a) (rootType kind b) := by
  cases p <;> rfl

 theorem typeOp_self {Δ : Bounds} (a : CompareTy) (ha : a.WellShaped Δ) (p : Bool) :
    AlgebraSubtype Δ (typeOp p a a) a ∧ AlgebraSubtype Δ a (typeOp p a a) := by
  cases p
  · exact ⟨.shaped (.meetLeft ⟨ha, ha, .refl⟩), .meetGreatest (.refl ha) (.refl ha)⟩
  · exact ⟨.joinLeast (.refl ha) (.refl ha), .shaped (.joinLeft ⟨ha, ha, .refl⟩)⟩

 theorem rootType_equation {Δ : Bounds} (kind : Nat) {a b : CompareTy}
    (h : Equation Δ a b) :
    AlgebraSubtype Δ (rootType kind a) (rootType kind b) ∧
      AlgebraSubtype Δ (rootType kind b) (rootType kind a) := by
  cases h with
  | distrib p hab hac =>
    simp only [rootType_typeOp]
    exact ⟨.equation (.distrib p (rootType_compatible kind hab) (rootType_compatible kind hac)),
      .equationRev (.distrib p (rootType_compatible kind hab) (rootType_compatible kind hac))⟩
  | modal p hab hm =>
    simp only [rootType, rootType_typeOp]
    exact ⟨.equation (.modal p (rootType_compatible kind hab) hm),
      .equationRev (.modal p (rootType_compatible kind hab) hm)⟩
  | scalar p ha hd hm hn =>
    simp only [rootType, rootType_typeOp]
    exact ⟨.equation (.scalar p (rootType_shaped Δ kind _) (rootType_defined kind hd) hm hn),
      .equationRev (.scalar p (rootType_shaped Δ kind _) (rootType_defined kind hd) hm hn)⟩
  | prod p hac hbd | sum p hac hbd | fn p hac hbd =>
    simpa only [rootType_typeOp, rootType] using typeOp_self (rootBase kind) (rootBase_shaped Δ kind) p

 theorem shaped_rootType {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) {kind : Nat} (hk : kind ≠ 0) (ha : rootTag a.shape = kind) :
    AlgebraSubtype Δ (rootType kind a) (rootType kind b) := by
  induction h with
  | refl hs => exact .refl (rootType_shaped Δ kind _)
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ ((rootTag_equivalent hΔ h₁.shape_equivalent).symm.trans ha))
  | bound hb =>
    obtain ⟨x, y, m, n, hx, hy⟩ := List.forall_iff_forall_mem.mp hΔ _ hb
    rw [CompareTy.shape_ofTy, ← TypeExpr.outer_comparisonShape _, hx] at ha
    exact False.elim (hk ha.symm)
  | identity hs => exact .identity (rootType_shaped Δ kind _)
  | identityRev hs => exact .identityRev (rootType_shaped Δ kind _)
  | compose hs => exact .shaped (.compose (rootType_shaped Δ kind _))
  | composeRev hs => exact .shaped (.composeRev (rootType_shaped Δ kind _))
  | congr h hm ih => exact .congr (ih ha) hm
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ =>
    exact .refl (rootBase_shaped Δ kind)
  | fn hca hbd hm ih₁ ih₂ =>
    have he : kind = 5 := ha.symm
    subst kind
    exact .fn (.refl trivial) (.refl trivial) hm
  | @joinLeft a b hs => exact .shaped (.joinLeft (rootType_shaped Δ kind (.join a b)))
  | @joinRight a b hs => exact .shaped (.joinRight (rootType_shaped Δ kind (.join a b)))
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ (h₁.shape_equivalent.trans h₂.shape_equivalent.symm)).symm.trans ha
    exact .joinLeast (ih₁ ha) (ih₂ hb)
  | @meetLeft a b hs => exact .shaped (.meetLeft (rootType_shaped Δ kind (.meet a b)))
  | @meetRight a b hs => exact .shaped (.meetRight (rootType_shaped Δ kind (.meet a b)))
  | meetGreatest h₁ h₂ ih₁ ih₂ => exact .meetGreatest (ih₁ ha) (ih₂ ha)

/-- The complete root context is monotone even when endpoints and intermediate
annotations are partial. No action is distributed or duplicated. -/
 theorem algebra_rootType {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) {kind : Nat} (hk : kind ≠ 0) (ha : rootTag a.shape = kind) :
    AlgebraSubtype Δ (rootType kind a) (rootType kind b) := by
  induction h with
  | shaped h => exact shaped_rootType hΔ h hk ha
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ ((rootTag_equivalent hΔ h₁.shape_equivalent).symm.trans ha))
  | equation h => exact (rootType_equation kind h).1
  | equationRev h => exact (rootType_equation kind h).2
  | congr h hm ih => exact .congr (ih ha) hm
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ => exact .refl (rootBase_shaped Δ kind)
  | fn hca hbd hm ih₁ ih₂ =>
    have he : kind = 5 := ha.symm
    subst kind
    exact .fn (.refl trivial) (.refl trivial) hm
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ (h₁.shape_equivalent.trans h₂.shape_equivalent.symm)).symm.trans ha
    exact .joinLeast (ih₁ ha) (ih₂ hb)
  | meetGreatest h₁ h₂ ih₁ ih₂ => exact .meetGreatest (ih₁ ha) (ih₂ ha)
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ h₁.shape_equivalent).trans ha
    exact .clamp (rootType_compatible kind hba) (rootType_compatible kind hat) hm (ih₁ hb) (ih₂ ha)
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ h₁.shape_equivalent).trans ha
    exact .clampRev (rootType_compatible kind hba) (rootType_compatible kind hat) hm (ih₁ hb) (ih₂ ha)

end ModalityInference.ComparisonStructuralProjection
