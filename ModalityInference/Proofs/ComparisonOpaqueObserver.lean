import ModalityInference.Proofs.ComparisonRootProjection
import ModalityInference.Proofs.ComparisonControls

namespace ModalityInference.ComparisonOpaqueObserver

open ComparisonControls ComparisonAlgebra

def Below (a b : Bool) : Prop := a = true → b = true

def applyMode : Coordinate → Bool → Mode → Bool
  | .unaffected, a, _ => a
  | .locality, a, m => a && m.isLocal
  | .affinity, a, m => a && m.once
  | .uniqueness, a, m => a || !m.unique

def blend (p a b : Bool) : Bool := if p then a || b else a && b

def value (c : Coordinate) (η : ModVar → Mode) (heads : TypeVar → Bool) : CompareTy → Bool
  | .var v => heads v
  | .modal a m => applyMode c (value c η heads a) (m.complete η)
  | .join a b => value c η heads a || value c η heads b
  | .meet a b => value c η heads a && value c η heads b
  | _ => false

@[simp] theorem value_typeOp (c : Coordinate) (η : ModVar → Mode)
    (heads : TypeVar → Bool) (p : Bool) (a b : CompareTy) :
    value c η heads (typeOp p a b) = blend p (value c η heads a) (value c η heads b) := by
  cases p <;> rfl

theorem below_refl (a : Bool) : Below a a := fun h => h

theorem below_trans {a b c : Bool} (h : Below a b) (k : Below b c) : Below a c := fun ha => k (h ha)

theorem applyMode_mono (c : Coordinate) {a b : Bool} {m n : Mode}
    (hab : Below a b) (hmn : m.le n = true) : Below (applyMode c a m) (applyMode c b n) := by
  have hm := (Mode.le_iff _ _).mp hmn
  cases c <;> cases ha : a <;> cases hb : b <;>
    cases hu : m.unique <;> cases hv : n.unique <;> simp_all [Below, applyMode]

theorem applyMode_submode {Δ : Bounds} {c : Coordinate} {η : ModVar → Mode}
    (hη : c = .unaffected ∨ ModeModels Δ η) {a b : Bool} {m n : ModExpr}
    (hab : Below a b) (hmn : Submode Δ m n) :
    Below (applyMode c a (m.complete η)) (applyMode c b (n.complete η)) := by
  rcases hη with rfl | hη
  · exact hab
  · exact applyMode_mono c hab (ComparisonStructuralProjection.submode_complete_modes hmn hη)

@[simp] theorem applyMode_identity (c : Coordinate) (a : Bool) :
    applyMode c a Mode.identity = a := by cases c <;> simp [applyMode, Mode.identity]

@[simp] theorem applyMode_compose (c : Coordinate) (a : Bool) (m n : Mode) :
    applyMode c (applyMode c a m) n = applyMode c a (m.compose n) := by
  cases c <;> simp [applyMode, Mode.compose, Bool.and_assoc, Bool.or_assoc]

theorem applyMode_blend (c : Coordinate) (p a b : Bool) (m : Mode) :
    applyMode c (blend p a b) m = blend p (applyMode c a m) (applyMode c b m) := by
  cases a <;> cases b <;> cases c <;> cases p <;> simp [applyMode, blend]

theorem applyMode_scalar (c : Coordinate) (p a : Bool) (m n : Mode) :
    applyMode c a (ComparisonLattice.Profile.blendMode p m n) =
      blend p (applyMode c a m) (applyMode c a n) := by
  cases a <;> cases c <;> cases p <;>
    simp [applyMode, blend, ComparisonLattice.Profile.blendMode, Mode.meet, Mode.join]

theorem applyMode_clamp (c : Coordinate) {b a t : Bool} (m : Mode)
    (hba : Below b a) (hat : Below a t) :
    applyMode c a m = ((a || applyMode c b m) && applyMode c t m) := by
  cases b <;> cases a <;> cases t <;> cases c <;> simp_all [Below, applyMode]

/-- Every algebraic equation has its expected Boolean coordinate interpretation
at an opaque shape. Structural equations cannot inhabit this shape. -/
theorem equation {Δ : Bounds} {φ : TypeVar → ComparisonShape} {s : TypeVar}
    {a b : CompareTy} (h : Equation Δ a b)
    (ha : a.shape.subst φ = .var s) (c : Coordinate)
    (η : ModVar → Mode) (heads : TypeVar → Bool) :
    value c η heads a = value c η heads b := by
  cases h with
  | distrib p hab hac =>
    cases p <;> apply Bool.eq_iff_iff.mpr <;>
      simp [typeOp, value, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
  | modal p hab hm =>
    simpa only [value, value_typeOp] using applyMode_blend c p _ _ _
  | scalar p hs hd hm hn =>
    simpa only [value, value_typeOp, ComparisonStructuralProjection.complete_modeOp] using
      applyMode_scalar c p _ _ _
  | prod p hab hcd | sum p hab hcd | fn p hab hcd =>
    simp [shape_typeOp, CompareTy.shape, ComparisonShape.subst] at ha

/-- Declared constraints are required only at the selected opaque shape; values
at structural shapes and unrelated declared classes are irrelevant. -/
def Assumptions (Δ : Bounds) (φ : TypeVar → ComparisonShape) (s : TypeVar)
    (c : Coordinate) (η : ModVar → Mode) (heads : TypeVar → Bool) : Prop :=
  ∀ a b, .sub a b ∈ Δ → (ComparisonShape.ofTy a).subst φ = .var s →
    Below (value c η heads (.ofTy a)) (value c η heads (.ofTy b))

theorem shaped {Δ : Bounds} {φ : TypeVar → ComparisonShape} {s : TypeVar}
    (hφ : ComparisonShape.Models Δ φ) {c : Coordinate} {η : ModVar → Mode}
    {heads : TypeVar → Bool} (hη : c = .unaffected ∨ ModeModels Δ η) (hΔ : Assumptions Δ φ s c η heads)
    {a b : CompareTy} (h : ShapedSubtype Δ a b) (ha : a.shape.subst φ = .var s) :
    Below (value c η heads a) (value c η heads b) := by
  induction h with
  | refl hs => exact below_refl _
  | trans h₁ h₂ ih₁ ih₂ =>
    exact below_trans (ih₁ ha) (ih₂ ((h₁.shape_equivalent φ hφ).symm.trans ha))
  | bound hb => exact hΔ _ _ hb (by simpa only [CompareTy.shape_ofTy] using ha)
  | identity hs | identityRev hs =>
    simp only [value, ModExpr.complete, ModExpr.epsilon, applyMode_identity]
    exact below_refl _
  | compose hs | composeRev hs =>
    simp only [value, ModExpr.complete, applyMode_compose]
    exact below_refl _
  | congr h hm ih =>
    exact applyMode_submode hη (ih ha) hm
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ | fn h₁ h₂ hm ih₁ ih₂ =>
    simp [CompareTy.shape, ComparisonShape.subst] at ha
  | joinLeft hs | joinRight hs | meetLeft hs | meetRight hs =>
    simp [value, Below, Bool.or_eq_true, Bool.and_eq_true] <;> tauto
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := (h₂.shape_equivalent φ hφ).trans (h₁.shape_equivalent φ hφ).symm |>.trans ha
    simp only [value, Below, Bool.or_eq_true]
    exact fun hh => hh.elim (ih₁ ha) (ih₂ hb)
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    simp only [value, Below, Bool.and_eq_true]
    exact fun hh => ⟨ih₁ ha hh, ih₂ ha hh⟩

/-- Opaque Boolean coordinates preserve arbitrary derivations, including partial
intermediate terms. Total completion is used only for their interpretation. -/
theorem algebra {Δ : Bounds} {φ : TypeVar → ComparisonShape} {s : TypeVar}
    (hφ : ComparisonShape.Models Δ φ) {c : Coordinate} {η : ModVar → Mode}
    {heads : TypeVar → Bool} (hη : c = .unaffected ∨ ModeModels Δ η) (hΔ : Assumptions Δ φ s c η heads)
    {a b : CompareTy} (h : AlgebraSubtype Δ a b) (ha : a.shape.subst φ = .var s) :
    Below (value c η heads a) (value c η heads b) := by
  induction h with
  | shaped h => exact shaped hφ hη hΔ h ha
  | trans h₁ h₂ ih₁ ih₂ =>
    exact below_trans (ih₁ ha) (ih₂ ((h₁.shape_equivalent φ hφ).symm.trans ha))
  | equation h => exact (equation h ha c η heads) ▸ below_refl _
  | equationRev h =>
    have hh : _ := equation h (by simpa only [h.shape_eq] using ha) c η heads
    exact hh ▸ below_refl _
  | congr h hm ih =>
    exact applyMode_submode hη (ih ha) hm
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ | fn h₁ h₂ hm ih₁ ih₂ =>
    simp [CompareTy.shape, ComparisonShape.subst] at ha
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := (h₂.shape_equivalent φ hφ).trans (h₁.shape_equivalent φ hφ).symm |>.trans ha
    simp only [value, Below, Bool.or_eq_true]
    exact fun hh => hh.elim (ih₁ ha) (ih₂ hb)
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    simp only [value, Below, Bool.and_eq_true]
    exact fun hh => ⟨ih₁ ha hh, ih₂ ha hh⟩
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hb := (h₁.shape_equivalent φ hφ).trans ha
    have hh := applyMode_clamp c (m := m.complete η) (ih₁ hb) (ih₂ ha)
    simp only [value, hh]
    exact below_refl _

end ModalityInference.ComparisonOpaqueObserver
