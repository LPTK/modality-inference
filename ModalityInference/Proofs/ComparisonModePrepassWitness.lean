import ModalityInference.ComparisonModePrepassRegression
import ModalityInference.Proofs.ComparisonAlgebraInstances
/-! A total public witness for the mode-coupled opaque interval regression. -/
namespace ModalityInference.ComparisonModePrepassRegression
def witness : Substitution :=
  { types := [(0,A),(1,B)], modes := [(0,.const Mode.global)] }
theorem ordinary_witness : Subsumes [] source target := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Instantiates, source, witness]
  · change EntailsAll target.bounds.assumptions
      [.sub A A, .sub (.modal A (.const Mode.global)) (.modal B .top), .sub B B]
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨.refl, by simp [A, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels],
        by simp [A, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩
    · refine ⟨.bound ?_, ?_, ?_⟩
      · simp [target, Bounds.assumptions, Constraint.assumptions]
      · intro η hη; simp [TypeExpr.wellFormedBounds, ModeModels, A,
          ModeSatisfies, ModExpr.WellFormed, ModExpr.eval]
      · intro η hη; simp [TypeExpr.wellFormedBounds, ModeModels, B,
          ModeSatisfies, ModExpr.WellFormed, ModExpr.eval, ModExpr.top]
    · exact ⟨.refl, by simp [B, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels],
        by simp [B, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩
  · exact .refl

theorem algebra_witness : AlgebraSubsumes [] source target := ordinary_witness.to_algebra
end ModalityInference.ComparisonModePrepassRegression
