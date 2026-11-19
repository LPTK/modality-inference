import ModalityInference.Proofs.ComparisonFiniteGraphLimitation
import ModalityInference.Proofs.ComparisonDefinedCovers

/-! A finite prefixed comparison witness need not be a finite approximation of
the least forward closure. This rules out identifying witness existence with
boundedness of that least fixed point: invariant separator synthesis is a
strictly different requirement. -/
namespace ModalityInference.ComparisonLeastPropagationLimitation

open ComparisonFiniteGraphLimitation

theorem candidate_step (n : Nat) :
    ShapedSubtype bounds (candidate n) (.prod (candidate n) .unit) := by
  induction n with
  | zero => exact .bound (a := A) (b := F A) (by simp [bounds])
  | succ n ih =>
      exact ShapedSubtype.prod_congr ih (.refl trivial)

/-- Every finite lower approximation fails the required prefixed inequality,
in the original guarded comparison algebra. -/
theorem no_candidate_prefixed (n : Nat) :
    ¬AlgebraSubtype bounds (.prod (candidate n) .unit) (candidate n) := by
  exact fun h => no_finite_fixed_point (candidate n) ⟨.shaped (candidate_step n), h⟩

/-- These are genuine lower approximations: every prefixed point above the
lower input bounds every iterate. -/
theorem candidate_below_prefixed {w : CompareTy}
    (ha : AlgebraSubtype bounds (.ofTy A) w)
    (hf : AlgebraSubtype bounds (.prod w .unit) w) (n : Nat) :
    AlgebraSubtype bounds (candidate n) w := by
  induction n with
  | zero => exact ha
  | succ n ih =>
      exact (ComparisonDefinedCovers.prod_congr ih (.refl (a := .unit) trivial)).trans hf

/-- The upper input name is already a finite defined witness of every
one-sided interval and prefixed obligation. -/
theorem finite_prefixed_witness :
    ∃w : CompareTy, w.WellShaped bounds ∧ w.DefinedUnder bounds ∧
      AlgebraSubtype bounds (.ofTy A) w ∧
      AlgebraSubtype bounds (.prod w .unit) w ∧
      AlgebraSubtype bounds w (.ofTy C) := by
  refine ⟨.ofTy C, CompareTy.wellShaped_ofTy C bounds, ?_,
    .shaped (.bound (a := A) (b := C) (by simp [bounds])),
    .shaped (.bound (a := F C) (b := C) (by simp [bounds])), .refl trivial⟩
  exact fun _ _ _ hc => False.elim (List.not_mem_nil hc)

end ModalityInference.ComparisonLeastPropagationLimitation
