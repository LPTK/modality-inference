import ModalityInference.Proofs.ComparisonShapeSolver

/-! Shape compatibility when the declared shape equations have no finite model.
This only discharges shape guards; subtype obligations remain separate. -/
namespace ModalityInference

theorem ComparisonShape.equivalent_of_no_models {Δ : Bounds}
    (h : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (a b : ComparisonShape) :
    ComparisonShape.Equivalent Δ a b := by
  intro ρ hρ
  exact False.elim (h ⟨ρ, hρ⟩)

theorem CompareTy.wellShaped_of_no_models {Δ : Bounds}
    (h : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (a : CompareTy) :
    a.WellShaped Δ := by
  induction a <;> simp_all only [CompareTy.WellShaped, and_self, true_and]
  all_goals exact ComparisonShape.equivalent_of_no_models h _ _

theorem ComparisonShapeSolver.prepare_infeasible_wellShaped {fuel p}
    (h : prepare fuel p = .success .infeasibleAssumptions) (a : CompareTy) :
    a.WellShaped p.assumptions :=
  CompareTy.wellShaped_of_no_models (prepare_infeasible h) a

end ModalityInference
