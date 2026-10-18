import ModalityInference.ComparisonResidualBounds

/-! The executable residual-bound recognizer exactly matches the declarative
fragment on which joint comparison is complete. -/
namespace ModalityInference

theorem residualBound_iff (c : Constraint) : residualBound c = true ↔ Residual [c] := by
  cases c with
  | sub a b =>
      cases ha : a.outer with
      | mk a' m =>
          cases hb : b.outer with
          | mk b' n =>
              cases a' <;> cases b' <;> simp [residualBound, Residual, ha, hb]
  | _ => simp [residualBound, Residual]

theorem residualBounds_iff (bounds : Bounds) : residualBounds bounds = true ↔ Residual bounds := by
  induction bounds with
  | nil => simp [residualBounds, Residual]
  | cons c cs ih =>
      change (residualBound c && residualBounds cs) = true ↔ Residual (c :: cs)
      rw [Bool.and_eq_true, residualBound_iff, ih]
      simp [Residual]

theorem residualBounds_sound {bounds : Bounds} (h : residualBounds bounds = true) :
    Residual bounds := (residualBounds_iff bounds).mp h

end ModalityInference
