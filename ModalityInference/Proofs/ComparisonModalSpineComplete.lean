import ModalityInference.Proofs.ComparisonModalSpine
import ModalityInference.Proofs.ComparisonAlgebra

namespace ModalityInference.ComparisonModalSpine

theorem act_size (ms : List ModExpr) (base : Ty) :
    (act ms base).size = base.size + ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [act, TypeExpr.size, ih, List.length_cons]; omega

/-- Every literal outer spine is recovered, regardless of the definedness of
its labels or nesting depth. Extraction uses structural recursion. -/
theorem factor_complete (base : Ty) (ms : List ModExpr) :
    factor base (act ms base) = some ms := by
  induction ms with
  | nil => cases base <;> simp [act, factor]
  | cons m ms ih =>
    have hne : TypeExpr.modal (act ms base) m ≠ base := by
      intro he
      have hs := congrArg TypeExpr.size he
      simp only [TypeExpr.size, act_size] at hs
      omega
    simp only [act, factor, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte,
      ih, Option.map_some]

theorem factor_iff (base target : Ty) (ms : List ModExpr) :
    factor base target = some ms ↔ act ms base = target := by
  constructor
  · exact factor_spec
  · intro he
    rw [← he]
    exact factor_complete base ms

theorem ofTy_act (ms : List ModExpr) (base : Ty) :
    CompareTy.ofTy (act ms base) = ComparisonPartialModes.act ms (.ofTy base) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => exact congrArg (fun a => CompareTy.modal a m) ih

/-- The extracted mode is equivalent to the complete target using only outer
identity and composition rules. No totality guard is introduced. -/
theorem factor_equivalent (Δ : Bounds) {base target : Ty} {ms : List ModExpr}
    (h : factor base target = some ms) :
    AlgebraSubtype Δ (.ofTy target) (.modal (.ofTy base) (ComparisonPartialModes.recompose ms)) ∧
      AlgebraSubtype Δ (.modal (.ofTy base) (ComparisonPartialModes.recompose ms)) (.ofTy target) := by
  have hc := ComparisonPartialModes.recompose_correct Δ ms (.ofTy base)
    (CompareTy.wellShaped_ofTy base Δ)
  rw [← ofTy_act, factor_spec h] at hc
  exact ⟨.shaped hc.1, .shaped hc.2⟩

end ModalityInference.ComparisonModalSpine
