import ModalityInference.Proofs.ComparisonProductProjection
import ModalityInference.Proofs.ComparisonAlgebraSoundness
import ModalityInference.Proofs.ComparisonSkeletonCoordinates

namespace ModalityInference.ComparisonStructuralProjection

open ComparisonAlgebra ComparisonLattice

def rootTag : ComparisonShape → Nat
  | .var _ => 0
  | .unit => 1
  | .credit => 2
  | .prod _ _ => 3
  | .sum _ _ => 4
  | .fn _ _ => 5

def constantShapes (s : ComparisonShape) (_ : TypeVar) : ComparisonShape := s

theorem residual_constantShapes {Δ : Bounds} (hΔ : Residual Δ) (s : ComparisonShape) :
    ComparisonShape.Models Δ (constantShapes s) := by
  intro p hp
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hp
  have hh := List.forall_iff_forall_mem.mp hΔ c hc
  cases c <;> simp only [List.mem_singleton, List.not_mem_nil] at hp
  all_goals try contradiction
  case sub a b =>
    subst p
    obtain ⟨x, y, m, n, hx, hy⟩ := hh
    rw [← TypeExpr.outer_comparisonShape a, ← TypeExpr.outer_comparisonShape b, hx, hy]
    rfl

theorem rootTag_equivalent {Δ : Bounds} (hΔ : Residual Δ) {a b : ComparisonShape}
    (h : ComparisonShape.Equivalent Δ a b) : rootTag a = rootTag b := by
  have hu := congrArg rootTag (h (constantShapes .unit) (residual_constantShapes hΔ .unit))
  have hc := congrArg rootTag (h (constantShapes .credit) (residual_constantShapes hΔ .credit))
  cases a <;> cases b <;> simp_all [rootTag, ComparisonShape.subst, constantShapes]

def rootExpr : CompareTy → ModExpr
  | .modal a m => .compose (rootExpr a) m
  | .join a b => .join (rootExpr a) (rootExpr b)
  | .meet a b => .meet (rootExpr a) (rootExpr b)
  | _ => .epsilon

@[simp] theorem rootExpr_typeOp (p : Bool) (a b : CompareTy) :
    rootExpr (typeOp p a b) = modeOp p (rootExpr a) (rootExpr b) := by cases p <;> rfl

theorem rootExpr_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) :
    Entails Δ (.defined (rootExpr a)) := by
  induction a with
  | modal a m ih =>
    exact Entails.defined_compose_iff.mpr
      ⟨ih (CompareTy.definedUnder_modal_iff.mp h).1, (CompareTy.definedUnder_modal_iff.mp h).2⟩
  | join a b ih₁ ih₂ =>
    exact ComparisonDefinedCovers.modeOp_defined true
      (ih₁ (CompareTy.definedUnder_join_iff.mp h).1)
      (ih₂ (CompareTy.definedUnder_join_iff.mp h).2)
  | meet a b ih₁ ih₂ =>
    exact ComparisonDefinedCovers.modeOp_defined false
      (ih₁ (CompareTy.definedUnder_meet_iff.mp h).1)
      (ih₂ (CompareTy.definedUnder_meet_iff.mp h).2)
  | var | unit | credit | prod | sum | fn => exact fun _ _ => rfl

def rootValue (η : ModVar → Mode) (a : CompareTy) : Mode := (rootExpr a).complete η

def rootOrder (kind : Nat) (a b : Mode) : Prop :=
  if kind = 5 then (a.compose Mode.top).le (b.compose Mode.top) = true else a.le b = true

theorem rootOrder_refl (kind : Nat) (a : Mode) : rootOrder kind a a := by
  unfold rootOrder
  split <;> exact Mode.le_refl _

theorem rootOrder_trans {kind : Nat} {a b c : Mode}
    (hab : rootOrder kind a b) (hbc : rootOrder kind b c) : rootOrder kind a c := by
  by_cases hk : kind = 5 <;> simp only [rootOrder, hk, if_true, if_false] at *
  all_goals exact Mode.le_trans hab hbc


theorem future_compose_swap (a m : Mode) :
    (a.compose m).compose Mode.top = (a.compose Mode.top).compose m := by
  rw [Mode.compose_assoc, Mode.compose_comm m Mode.top, ← Mode.compose_assoc]

theorem rootOrder_compose {kind : Nat} {a b m n : Mode}
    (hab : rootOrder kind a b) (hmn : m.le n = true) :
    rootOrder kind (a.compose m) (b.compose n) := by
  by_cases hk : kind = 5 <;> simp only [rootOrder, hk, if_true, if_false] at *
  · simpa only [future_compose_swap] using
      Mode.le_trans (Mode.compose_le_right m hab) (Mode.compose_le_left (b.compose Mode.top) hmn)
  · exact Mode.le_trans (Mode.compose_le_right m hab) (Mode.compose_le_left b hmn)

theorem rootOrder_universal (kind : Nat) (p : Bool) (a b c : Mode) :
    if p then rootOrder kind (Profile.blendMode p a b) c ↔ rootOrder kind a c ∧ rootOrder kind b c
    else rootOrder kind c (Profile.blendMode p a b) ↔ rootOrder kind c a ∧ rootOrder kind c b := by
  by_cases hk : kind = 5 <;>
    simp only [rootOrder, hk, if_true, if_false, ← Profile.blendMode_compose]
  all_goals cases p <;> simp only [Profile.blendMode, Bool.false_eq_true, if_false, if_true,
    mode_join_le, mode_le_meet]

theorem rootOrder_clamp {kind : Nat} {b a t : Mode}
    (hba : rootOrder kind b a) (hat : rootOrder kind a t) (m : Mode) :
    rootOrder kind (a.compose m) ((a.join (b.compose m)).meet (t.compose m)) ∧
      rootOrder kind ((a.join (b.compose m)).meet (t.compose m)) (a.compose m) := by
  by_cases hk : kind = 5 <;> simp only [rootOrder, hk, if_true, if_false] at *
  · have hh := mode_clamp hba hat m
    have he : ((a.join (b.compose m)).meet (t.compose m)).compose Mode.top =
        (a.compose m).compose Mode.top := by
      change (Profile.blendMode false (Profile.blendMode true a (b.compose m))
        (t.compose m)).compose Mode.top = (a.compose m).compose Mode.top
      rw [← Profile.blendMode_compose, ← Profile.blendMode_compose]
      simpa only [future_compose_swap] using hh
    rw [he]
    exact ⟨Mode.le_refl _, Mode.le_refl _⟩
  · rw [mode_clamp hba hat m]
    exact ⟨Mode.le_refl _, Mode.le_refl _⟩

@[simp] theorem rootValue_typeOp (η : ModVar → Mode) (p : Bool) (a b : CompareTy) :
    rootValue η (typeOp p a b) = Profile.blendMode p (rootValue η a) (rootValue η b) := by
  cases p <;> rfl

@[simp] theorem rootValue_modal (η : ModVar → Mode) (a : CompareTy) (m : ModExpr) :
    rootValue η (.modal a m) = (rootValue η a).compose (m.complete η) := rfl

@[simp] theorem complete_modeOp (η : ModVar → Mode) (p : Bool) (m n : ModExpr) :
    (modeOp p m n).complete η = Profile.blendMode p (m.complete η) (n.complete η) := by
  cases p <;> rfl

theorem rootValue_equation {Δ : Bounds} {a b : CompareTy} (h : Equation Δ a b)
    (η : ModVar → Mode) : rootValue η a = rootValue η b := by
  cases h with
  | distrib p hab hac =>
    simp only [rootValue_typeOp]
    exact Profile.blendMode_distrib _ _ _ _
  | modal p hab hm =>
    simp only [rootValue_modal, rootValue_typeOp]
    exact (Profile.blendMode_compose _ _ _ _).symm
  | scalar p ha hd hm hn =>
    simp only [rootValue_modal, rootValue_typeOp, complete_modeOp]
    exact (Profile.blendMode_compose_right _ _ _ _).symm
  | prod p hac hbd | sum p hac hbd | fn p hac hbd =>
    simp only [rootValue_typeOp]
    exact Profile.blendMode_self p Mode.identity


theorem submode_complete_modes {Δ : Bounds} {m n : ModExpr} (h : Submode Δ m n)
    {η : ModVar → Mode} (hη : ModeModels Δ η) : (m.complete η).le (n.complete η) = true := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h.denote hη
  simpa only [ModExpr.complete_of_eval hx, ModExpr.complete_of_eval hy] using hxy

theorem shaped_rootValue {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) {kind : Nat} (hk : kind ≠ 0) (ha : rootTag a.shape = kind)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    rootOrder kind (rootValue η a) (rootValue η b) := by
  induction h with
  | refl hs => exact rootOrder_refl _ _
  | trans h₁ h₂ ih₁ ih₂ =>
    exact rootOrder_trans (ih₁ ha) (ih₂ ((rootTag_equivalent hΔ h₁.shape_equivalent).symm.trans ha))
  | bound hb =>
    obtain ⟨x, y, m, n, hx, hy⟩ := List.forall_iff_forall_mem.mp hΔ _ hb
    rw [CompareTy.shape_ofTy, ← TypeExpr.outer_comparisonShape _, hx] at ha
    exact False.elim (hk ha.symm)
  | identity hs | identityRev hs =>
    simpa only [rootValue, rootExpr, ModExpr.complete, ModExpr.epsilon, Mode.compose_identity] using
      rootOrder_refl kind (rootValue η _)
  | compose hs | composeRev hs =>
    simp only [rootValue, rootExpr, ModExpr.complete, Mode.compose_assoc]
    exact rootOrder_refl _ _
  | congr h hm ih => exact rootOrder_compose (ih ha) (submode_complete_modes hm hη)
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ => exact rootOrder_refl _ _
  | fn hca hbd hm ih₁ ih₂ =>
    have hh := submode_complete_modes hm hη
    have he : kind = 5 := ha.symm
    subst kind
    simpa only [rootOrder, if_true, rootValue, rootExpr, ModExpr.complete,
      ModExpr.epsilon, ModExpr.top, Mode.identity_compose, Mode.compose_assoc, Mode.compose_self] using
      Mode.compose_le_right Mode.top hh
  | joinLeft hs => exact ((rootOrder_universal kind true _ _ _).mp (rootOrder_refl _ _)).1
  | joinRight hs => exact ((rootOrder_universal kind true _ _ _).mp (rootOrder_refl _ _)).2
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ (h₁.shape_equivalent.trans h₂.shape_equivalent.symm)).symm.trans ha
    exact (rootOrder_universal kind true _ _ _).mpr ⟨ih₁ ha, ih₂ hb⟩
  | meetLeft hs => exact ((rootOrder_universal kind false _ _ _).mp (rootOrder_refl _ _)).1
  | meetRight hs => exact ((rootOrder_universal kind false _ _ _).mp (rootOrder_refl _ _)).2
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    exact (rootOrder_universal kind false _ _ _).mpr ⟨ih₁ ha, ih₂ ha⟩

/-- Structural scalar coordinates are monotone through all algebraic
intermediates. Completion is used only to interpret partial intermediate
annotations; defined endpoints retain their ordinary evaluations. -/
theorem algebra_rootValue {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) {kind : Nat} (hk : kind ≠ 0) (ha : rootTag a.shape = kind)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    rootOrder kind (rootValue η a) (rootValue η b) := by
  induction h with
  | shaped h => exact shaped_rootValue hΔ h hk ha hη
  | trans h₁ h₂ ih₁ ih₂ =>
    exact rootOrder_trans (ih₁ ha) (ih₂ ((rootTag_equivalent hΔ h₁.shape_equivalent).symm.trans ha))
  | equation h => rw [rootValue_equation h η]; exact rootOrder_refl _ _
  | equationRev h => rw [rootValue_equation h η]; exact rootOrder_refl _ _
  | congr h hm ih => exact rootOrder_compose (ih ha) (submode_complete_modes hm hη)
  | prod h₁ h₂ ih₁ ih₂ | sum h₁ h₂ ih₁ ih₂ => exact rootOrder_refl _ _
  | fn hca hbd hm ih₁ ih₂ =>
    have hh := submode_complete_modes hm hη
    have he : kind = 5 := ha.symm
    subst kind
    simpa only [rootOrder, if_true, rootValue, rootExpr, ModExpr.complete,
      ModExpr.epsilon, ModExpr.top, Mode.identity_compose, Mode.compose_assoc, Mode.compose_self] using
      Mode.compose_le_right Mode.top hh
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ (h₁.shape_equivalent.trans h₂.shape_equivalent.symm)).symm.trans ha
    exact (rootOrder_universal kind true _ _ _).mpr ⟨ih₁ ha, ih₂ hb⟩
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    exact (rootOrder_universal kind false _ _ _).mpr ⟨ih₁ ha, ih₂ ha⟩
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ h₁.shape_equivalent).trans ha
    exact (rootOrder_clamp (ih₁ hb) (ih₂ ha) (m.complete η)).1
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have hb := (rootTag_equivalent hΔ h₁.shape_equivalent).trans ha
    exact (rootOrder_clamp (ih₁ hb) (ih₂ ha) (m.complete η)).2


/-- The constructor coordinate is an explicit modality expression from the
input type; its semantic value uses completion only to avoid choice. -/
def rootGuarded {Δ : Bounds} (a : CompareTy) (ha : a.DefinedUnder Δ) : GuardedMode Δ where
  expression := rootExpr a
  value η := rootValue η a
  eval η hη := by
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (rootExpr_defined ha η hη)
    simpa only [rootValue, ModExpr.complete_of_eval hm] using hm

theorem rootGuarded_le {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hne : rootTag a.shape ≠ 0) (hfn : rootTag a.shape ≠ 5) :
    ComparisonSkeletonCoordinates.Scalar.le (rootGuarded a ha) (rootGuarded b hb) := by
  intro η hη
  have hh := algebra_rootValue hΔ h hne rfl hη
  simpa only [rootOrder, hfn, if_false] using hh

theorem rootGuarded_futureLe {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hfn : rootTag a.shape = 5) :
    ComparisonSkeletonCoordinates.Scalar.futureLe (rootGuarded a ha) (rootGuarded b hb) := by
  intro η hη
  exact algebra_rootValue hΔ h (by decide : 5 ≠ 0) hfn hη

end ModalityInference.ComparisonStructuralProjection
