import ModalityInference.Proofs.ComparisonSkeletonForest

namespace ModalityInference.ComparisonSkeletonCoordinates

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeleton ComparisonShapeSolver

namespace Scalar

def absorbing {Δ : Bounds} : GuardedMode Δ where
  expression := .const Mode.absorbing
  value _ := Mode.absorbing
  eval _ _ := rfl

theorem absorbing_compose {Δ : Bounds} (m : GuardedMode Δ) :
    equivalent (absorbing (Δ := Δ)) (compose absorbing m) := by
  constructor <;> intro η hη
  all_goals simp only [absorbing, compose, Mode.compose, Mode.absorbing, Bool.false_and]
  all_goals exact Mode.le_refl _

end Scalar

def rebaseVariable {Δ : Bounds} (v : TypeVar) : (allowed : Bool) →
    (a : CompareTy) → a.WellShaped Δ → a.DefinedUnder Δ →
    (allowed = false → ComparisonShape.Equivalent Δ a.shape (.var v)) →
    Tree Δ (if allowed then .unit else .var v)
  | true, _, _, _, _ => .unit Scalar.absorbing
  | false, a, hs, hd, he => .atom ⟨a, hs, hd, he rfl⟩

theorem rebaseVariable_le {Δ : Bounds} (v : TypeVar) (allowed : Bool)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a b)
    (ea : allowed = false → ComparisonShape.Equivalent Δ a.shape (.var v))
    (eb : allowed = false → ComparisonShape.Equivalent Δ b.shape (.var v)) :
    Tree.Le (rebaseVariable v allowed a h.wellShaped_left ha ea)
      (rebaseVariable v allowed b h.wellShaped_right hb eb) := by
  cases allowed
  · exact h
  · exact Scalar.refl _

/-- Retraction at a symbolic template shape. Unconstrained shape parameters
use a unit coordinate with absorbing action; fixed shape classes retain their
actual opaque comparison types. -/
def rebase {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ) :
    (s : ComparisonShape) → (a : CompareTy) → a.WellShaped Δ → a.DefinedUnder Δ →
      ComparisonShape.Equivalent Δ a.shape (s.subst ρ) → Tree Δ (defaultShape p s)
  | .var v, a, hs, hd, he => rebaseVariable v (sourceAllowed p v) a hs hd
      (fun hf => by simpa only [ComparisonShape.subst, hρ v hf] using he)
  | .unit, a, _, hd, _ => .unit (rootGuarded a hd)
  | .credit, a, _, hd, _ => .credit (rootGuarded a hd)
  | .prod s t, a, hs, hd, he =>
    let hr := Normalization.pairRoot hΔ hs false he
    let hh := Normalization.pairShapes hr he
    .prod (rebase hΔ p ρ hρ s (pairChild false a) (pairChild_shaped hr hs false)
        (pairChild_defined hr hd false) hh.1)
      (rebase hΔ p ρ hρ t (pairChild true a) (pairChild_shaped hr hs true)
        (pairChild_defined hr hd true) hh.2) (rootGuarded a hd)
  | .sum s t, a, hs, hd, he =>
    let hr := Normalization.pairRoot hΔ hs true he
    let hh := Normalization.pairShapes hr he
    .sum (rebase hΔ p ρ hρ s (pairChild false a) (pairChild_shaped hr hs false)
        (pairChild_defined hr hd false) hh.1)
      (rebase hΔ p ρ hρ t (pairChild true a) (pairChild_shaped hr hs true)
        (pairChild_defined hr hd true) hh.2) (rootGuarded a hd)
  | .fn s t, a, hs, hd, he =>
    let hr := Normalization.fnRoot hΔ hs he
    let hh := Normalization.fnShapes hr he
    .fn (rebase hΔ p ρ hρ s (fnChild true a) (fnChild_shaped hr hs true)
        (fnChild_defined hr hd true) hh.1)
      (rebase hΔ p ρ hρ t (fnChild false a) (fnChild_shaped hr hs false)
        (fnChild_defined hr hd false) hh.2) (rootGuarded a hd)

/-- Defaulting unconstrained shape parameters preserves comparisons between
arbitrary defined witnesses, independent of their original concrete shapes. -/
theorem rebase_le {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ)
    {s : ComparisonShape} {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a b) (ea : ComparisonShape.Equivalent Δ a.shape (s.subst ρ))
    (eb : ComparisonShape.Equivalent Δ b.shape (s.subst ρ)) :
    Tree.Le (rebase hΔ p ρ hρ s a h.wellShaped_left ha ea)
      (rebase hΔ p ρ hρ s b h.wellShaped_right hb eb) := by
  induction s generalizing a b with
  | var v => exact rebaseVariable_le v (sourceAllowed p v) ha hb h _ _
  | unit =>
    apply rootGuarded_le hΔ h ha hb
    all_goals rw [rootTag_equivalent hΔ ea]
    all_goals simp only [ComparisonShape.subst, rootTag]; decide
  | credit =>
    apply rootGuarded_le hΔ h ha hb
    all_goals rw [rootTag_equivalent hΔ ea]
    all_goals simp only [ComparisonShape.subst, rootTag]; decide
  | prod s t ih₁ ih₂ | sum s t ih₁ ih₂ =>
    dsimp only [rebase, Tree.Le]
    refine ⟨?_, ?_, ?_⟩
    · apply ih₁
      first
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left false ea) false
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left true ea) false
    · apply ih₂
      first
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left false ea) true
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left true ea) true
    · apply rootGuarded_le hΔ h ha hb
      all_goals rw [rootTag_equivalent hΔ ea]
      all_goals simp only [ComparisonShape.subst, rootTag]; decide
  | fn s t ih₁ ih₂ =>
    dsimp only [rebase, Tree.Le]
    refine ⟨?_, ?_, ?_⟩
    · apply ih₁
      exact algebra_fnChild hΔ h (Normalization.fnRoot hΔ h.wellShaped_left ea) true
    · apply ih₂
      exact algebra_fnChild hΔ h (Normalization.fnRoot hΔ h.wellShaped_left ea) false
    · exact rootGuarded_futureLe hΔ h ha hb (rootTag_equivalent hΔ ea)


theorem rebaseVariable_modal {Δ : Bounds} (v : TypeVar) (allowed : Bool)
    (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : allowed = false → ComparisonShape.Equivalent Δ a.shape (.var v)) (m : GuardedMode Δ) :
    Tree.Equivalent
      (rebaseVariable v allowed (.modal a m.expression) hs
        (CompareTy.definedUnder_modal_iff.mpr ⟨hd, m.defined⟩) he)
      (Tree.modal m (rebaseVariable v allowed a hs hd he)) := by
  cases allowed
  · exact ⟨AlgebraSubtype.refl hs, AlgebraSubtype.refl hs⟩
  · exact Scalar.absorbing_compose m

theorem rebase_modal {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ) (s : ComparisonShape)
    (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) (m : GuardedMode Δ) :
    Tree.Equivalent
      (rebase hΔ p ρ hρ s (.modal a m.expression) hs
        (CompareTy.definedUnder_modal_iff.mpr ⟨hd, m.defined⟩) he)
      (Tree.modal m (rebase hΔ p ρ hρ s a hs hd he)) := by
  induction s generalizing a with
  | var v => exact rebaseVariable_modal v (sourceAllowed p v) a hs hd _ m
  | unit | credit => exact rootGuarded_modal a hd m
  | prod s t ih₁ ih₂ =>
    have hp := Normalization.pairRoot hΔ hs false he
    have hl := ih₁ (pairChild false a) (pairChild_shaped hp hs false)
      (pairChild_defined hp hd false) (Normalization.pairShapes hp he).1
    have hr := ih₂ (pairChild true a) (pairChild_shaped hp hs true)
      (pairChild_defined hp hd true) (Normalization.pairShapes hp he).2
    exact ⟨⟨hl.1, hr.1, (rootGuarded_modal a hd m).1⟩,
      ⟨hl.2, hr.2, (rootGuarded_modal a hd m).2⟩⟩
  | sum s t ih₁ ih₂ =>
    have hp := Normalization.pairRoot hΔ hs true he
    have hl := ih₁ (pairChild false a) (pairChild_shaped hp hs false)
      (pairChild_defined hp hd false) (Normalization.pairShapes hp he).1
    have hr := ih₂ (pairChild true a) (pairChild_shaped hp hs true)
      (pairChild_defined hp hd true) (Normalization.pairShapes hp he).2
    exact ⟨⟨hl.1, hr.1, (rootGuarded_modal a hd m).1⟩,
      ⟨hl.2, hr.2, (rootGuarded_modal a hd m).2⟩⟩
  | fn s t ih₁ ih₂ =>
    exact ⟨⟨Tree.Le.refl _, Tree.Le.refl _, (rootGuarded_modal_future a hd m).1⟩,
      ⟨Tree.Le.refl _, Tree.Le.refl _, (rootGuarded_modal_future a hd m).2⟩⟩

theorem shape_subst_fixed {p : SchemePreparation.Prepared} {ρ : TypeVar → ComparisonShape}
    (hρ : Fixes (sourceAllowed p) ρ) {s : ComparisonShape} (hf : FixedShape p s) :
    s.subst ρ = s := by
  induction s with
  | var v => exact hρ v hf
  | unit | credit => rfl
  | prod a b ih₁ ih₂ | sum a b ih₁ ih₂ | fn a b ih₁ ih₂ =>
    simp only [ComparisonShape.subst, ih₁ hf.1, ih₂ hf.2]

theorem rebaseVariable_fixed_reify {Δ : Bounds} (v : TypeVar) (allowed : Bool)
    (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : allowed = false → ComparisonShape.Equivalent Δ a.shape (.var v))
    (hf : allowed = false) : (rebaseVariable v allowed a hs hd he).reify = a := by
  cases allowed
  · rfl
  · contradiction

/-- On fixed shapes, rebasing is exactly the already verified defined
retraction; it changes neither symbolic coordinates nor opaque images. -/
theorem rebase_fixed_reify {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ) (s : ComparisonShape)
    (hf : FixedShape p s) (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) :
    (rebase hΔ p ρ hρ s a hs hd he).reify =
      (normalize hΔ s a hs hd ((shape_subst_fixed hρ hf) ▸ he)).reify := by
  induction s generalizing a with
  | var v =>
    exact rebaseVariable_fixed_reify v (sourceAllowed p v) a hs hd _ hf
  | unit | credit => rfl
  | prod s t ih₁ ih₂ | sum s t ih₁ ih₂ | fn s t ih₁ ih₂ =>
    dsimp only [rebase, normalize, Tree.reify]
    congr 2
    · apply ih₁ hf.1
    · apply ih₂ hf.2


theorem fixedShape_of_vars {p : SchemePreparation.Prepared} {s : ComparisonShape}
    (hf : ∀ v ∈ s.vars, sourceAllowed p v = false) : FixedShape p s := by
  induction s <;> simp_all [FixedShape, ComparisonShape.vars]

theorem rebase_public_correct {Δ : Bounds} (hΔ : Residual Δ) (p : SchemePreparation.Prepared)
    (ρ : TypeVar → ComparisonShape) (hρ : Fixes (sourceAllowed p) ρ) (a : Ty)
    (ha : (CompareTy.ofTy a).DefinedUnder Δ)
    (hf : FixedShape p (ComparisonShape.ofTy a)) :
    let tree := rebase hΔ p ρ hρ (ComparisonShape.ofTy a) (.ofTy a)
      (CompareTy.wellShaped_ofTy a Δ) ha
      (by rw [CompareTy.shape_ofTy, shape_subst_fixed hρ hf]; exact .refl)
    AlgebraSubtype Δ tree.reify (.ofTy a) ∧ AlgebraSubtype Δ (.ofTy a) tree.reify := by
  dsimp only
  rw [rebase_fixed_reify hΔ p ρ hρ _ hf]
  exact normalize_public_correct hΔ a ha

end ModalityInference.ComparisonSkeletonCoordinates
