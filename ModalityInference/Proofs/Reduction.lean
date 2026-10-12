import ModalityInference.Proofs.GroundOrder
import ModalityInference.Constraints

/-! Local constraint decomposition preserves precisely the ground solutions,
including definedness of partial modality expressions. -/
namespace ModalityInference

theorem Mode.leftResidual_le_iff (a b c : Mode) :
    (∃ r, a.leftResidual b = some r ∧ r.le c = true) ↔ a.le (b.compose c) = true := by
  simp only [Mode.leftResidual]
  split <;> simp_all [Mode.le_iff, Mode.compose, Bool.and_eq_true, Bool.or_eq_true]
  all_goals simp_all only [Bool.eq_false_iff]; tauto

theorem Mode.le_rightResidual_iff (a b c : Mode) :
    (∃ r, b.rightResidual c = some r ∧ a.le r = true) ↔ (a.compose b).le c = true := by
  simp only [Mode.rightResidual]
  split <;> simp_all [Mode.le_iff, Mode.compose, Bool.and_eq_true, Bool.or_eq_true]
  all_goals simp_all only [Bool.eq_false_iff]; tauto

set_option maxHeartbeats 500000 in
theorem ConstraintReduction.groundModels {cs ds ρ} (h : ConstraintReduction cs ds) :
    GroundModels ρ cs ↔ GroundModels ρ ds := by
  induction h
  case pair a b c d l r | sum a b c d l r | fn a b c d l r =>
    simp only [GroundModels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
    cases ha : a.realize ρ <;> simp [GroundSatisfies, TypeExpr.realize, ha]
    cases b.realize ρ <;> simp
    cases c.realize ρ <;> simp
    cases d.realize ρ <;> simp
    cases hl : l.eval (some ∘ ρ.modes) <;> simp [ModExpr.Below, hl]
    cases hr : r.eval (some ∘ ρ.modes) <;>
      simp [ModExpr.eval, ModExpr.top, hr, GroundTy.modal, Mode.identity_compose,
        ← GroundOrder.iff_subtype, and_left_comm, and_comm]
  case unit l r | credit l r =>
    cases hl : l.eval (some ∘ ρ.modes) <;> cases hr : r.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, TypeExpr.realize, ModExpr.Below, ModExpr.eval,
        hl, hr, GroundTy.modal, ← GroundOrder.iff_subtype]
  case sub a b c =>
    cases ha : a.eval (some ∘ ρ.modes) <;> cases hb : b.eval (some ∘ ρ.modes) <;>
      cases hc : c.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, ModExpr.Below, ModExpr.WellFormed, ModExpr.eval,
        ha, hb, hc]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨by simp [hx], (Mode.leftResidual_le_iff _ _ _).mp ⟨x, hx, h⟩⟩,
      fun h => (Mode.leftResidual_le_iff _ _ _).mpr h.2⟩
  case imp a b c =>
    cases ha : a.eval (some ∘ ρ.modes) <;> cases hb : b.eval (some ∘ ρ.modes) <;>
      cases hc : c.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, ModExpr.Below, ModExpr.WellFormed, ModExpr.eval,
        ha, hb, hc]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨by simp [hx], (Mode.le_rightResidual_iff _ _ _).mp ⟨x, hx, h⟩⟩,
      fun h => (Mode.le_rightResidual_iff _ _ _).mpr h.2⟩
  case left a b c =>
    cases ha : a.eval (some ∘ ρ.modes) <;> cases hb : b.eval (some ∘ ρ.modes) <;>
      cases hc : c.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, ModExpr.Below, ModExpr.WellFormed, ModExpr.eval,
        ha, hb, hc, Mode.le_rightResidual_iff]
  case right a b c =>
    cases ha : a.eval (some ∘ ρ.modes) <;> cases hb : b.eval (some ∘ ρ.modes) <;>
      cases hc : c.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, ModExpr.Below, ModExpr.WellFormed, ModExpr.eval,
        ha, hb, hc, Mode.leftResidual_le_iff, Mode.compose_comm]
  case join a b c | meet a b c =>
    cases ha : a.eval (some ∘ ρ.modes) <;> cases hb : b.eval (some ∘ ρ.modes) <;>
      cases hc : c.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, ModExpr.Below, ModExpr.eval,
        ha, hb, hc, Mode.le_iff, Mode.join, Mode.meet, Bool.and_eq_true, Bool.or_eq_true]
    all_goals tauto
  case close a b =>
    cases ha : a.eval (some ∘ ρ.modes) <;> cases hb : b.eval (some ∘ ρ.modes) <;>
      simp [GroundModels, GroundSatisfies, ModExpr.Below, ModExpr.WellFormed, ModExpr.eval,
        ha, hb, Mode.le_iff, Mode.close, Mode.closeInv]
  case context xs ys before after h ih =>
    simpa only [GroundModels, List.mem_append, or_imp, forall_and] using
      and_congr (and_congr (Iff.rfl (a := GroundModels ρ before)) ih) (Iff.rfl (a := GroundModels ρ after))

end ModalityInference
