import ModalityInference.Proofs.ComparisonRootProjection
import ModalityInference.Proofs.ComparisonUnanchoredProjection

/-! Scalar root coordinates remain monotone at an unanchored resolved shape.
Declared edges at other shapes are retained, and every intermediate annotation
is interpreted under the same modality valuation. -/
namespace ModalityInference.ComparisonUnanchoredRoot

open ComparisonAlgebra ComparisonLattice ComparisonStructuralProjection
  ComparisonUnanchoredProjection

theorem shaped_rootValue {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) (he : a.shape.subst ρ = s)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    rootOrder (rootTag s) (rootValue η a) (rootValue η b) := by
  induction h with
  | refl hs => exact rootOrder_refl _ _
  | trans h₁ h₂ ih₁ ih₂ =>
    exact rootOrder_trans (ih₁ he) (ih₂ ((h₁.shape_equivalent ρ hz.models).symm.trans he))
  | bound hb => exact False.elim (hz.bounds hb he)
  | identity hs | identityRev hs =>
    simpa only [rootValue, rootExpr, ModExpr.complete, ModExpr.epsilon, Mode.compose_identity] using
      rootOrder_refl (rootTag s) (rootValue η _)
  | compose hs | composeRev hs =>
    simp only [rootValue, rootExpr, ModExpr.complete, Mode.compose_assoc]
    exact rootOrder_refl _ _
  | congr h hm ih => exact rootOrder_compose (ih he) (submode_complete_modes hm hη)
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ => exact rootOrder_refl _ _
  | fn hca hbd hm ih₁ ih₂ =>
    have hk : rootTag s = 5 := by rw [← he]; rfl
    simpa only [rootOrder, hk, if_true, rootValue, rootExpr, ModExpr.complete,
      ModExpr.epsilon, ModExpr.top, Mode.identity_compose, Mode.compose_assoc, Mode.compose_self] using
      Mode.compose_le_right Mode.top (submode_complete_modes hm hη)
  | joinLeft hs => exact ((rootOrder_universal (rootTag s) true _ _ _).mp (rootOrder_refl _ _)).1
  | joinRight hs => exact ((rootOrder_universal (rootTag s) true _ _ _).mp (rootOrder_refl _ _)).2
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := ((h₁.shape_equivalent.trans h₂.shape_equivalent.symm) ρ hz.models).symm.trans he
    exact (rootOrder_universal (rootTag s) true _ _ _).mpr ⟨ih₁ he, ih₂ hb⟩
  | meetLeft hs => exact ((rootOrder_universal (rootTag s) false _ _ _).mp (rootOrder_refl _ _)).1
  | meetRight hs => exact ((rootOrder_universal (rootTag s) false _ _ _).mp (rootOrder_refl _ _)).2
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    exact (rootOrder_universal (rootTag s) false _ _ _).mpr ⟨ih₁ he, ih₂ he⟩

theorem algebra_rootValue {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (he : a.shape.subst ρ = s)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    rootOrder (rootTag s) (rootValue η a) (rootValue η b) := by
  induction h with
  | shaped h => exact shaped_rootValue hz h he hη
  | trans h₁ h₂ ih₁ ih₂ =>
    exact rootOrder_trans (ih₁ he) (ih₂ ((h₁.shape_equivalent ρ hz.models).symm.trans he))
  | equation h | equationRev h => rw [rootValue_equation h η]; exact rootOrder_refl _ _
  | congr h hm ih => exact rootOrder_compose (ih he) (submode_complete_modes hm hη)
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ => exact rootOrder_refl _ _
  | fn hca hbd hm ih₁ ih₂ =>
    have hk : rootTag s = 5 := by rw [← he]; rfl
    simpa only [rootOrder, hk, if_true, rootValue, rootExpr, ModExpr.complete,
      ModExpr.epsilon, ModExpr.top, Mode.identity_compose, Mode.compose_assoc, Mode.compose_self] using
      Mode.compose_le_right Mode.top (submode_complete_modes hm hη)
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have heb := ((h₁.shape_equivalent.trans h₂.shape_equivalent.symm) ρ hz.models).symm.trans he
    exact (rootOrder_universal _ true _ _ _).mpr ⟨ih₁ he, ih₂ heb⟩
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    exact (rootOrder_universal _ false _ _ _).mpr ⟨ih₁ he, ih₂ he⟩
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have heb := (h₁.shape_equivalent ρ hz.models).trans he
    exact (rootOrder_clamp (ih₁ heb) (ih₂ he) (m.complete η)).1
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have heb := (h₁.shape_equivalent ρ hz.models).trans he
    exact (rootOrder_clamp (ih₁ heb) (ih₂ he) (m.complete η)).2

theorem rootGuarded_le {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (he : a.shape.subst ρ = s)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) (hfn : rootTag s ≠ 5) :
    ComparisonSkeletonCoordinates.Scalar.le (rootGuarded a ha) (rootGuarded b hb) := by
  intro η hη
  have hh := algebra_rootValue hz h he hη
  simpa only [rootOrder, hfn, if_false] using hh

theorem rootGuarded_futureLe {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (he : a.shape.subst ρ = s)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) (hfn : rootTag s = 5) :
    ComparisonSkeletonCoordinates.Scalar.futureLe (rootGuarded a ha) (rootGuarded b hb) := by
  intro η hη
  have hh := algebra_rootValue hz h he hη
  simpa only [rootOrder, hfn, if_true] using hh

end ModalityInference.ComparisonUnanchoredRoot
