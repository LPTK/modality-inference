import ModalityInference.ComparisonParameterization
import ModalityInference.Proofs.ComparisonPropagationComposition

namespace ModalityInference.ComparisonParameterization

theorem prepared_target (source originalSource originalTarget : Scheme) :
    let p := SchemePreparation.prepare [] originalSource originalTarget
    (SchemePreparation.prepare [] source (target p originalTarget)).targetType = p.targetType ∧
      (SchemePreparation.prepare [] source (target p originalTarget)).assumptions = p.assumptions := by
  have ht : ({} : Substitution).type = TypeExpr.var := by funext v; cases v <;> rfl
  have hm : ({} : Substitution).mode = ModExpr.var := by funext v; cases v <;> rfl
  simp only [target, SchemePreparation.prepare, Scheme.freshSubstitution,
    List.zipIdx_nil, List.map_nil, Substitution.empty_bounds, Substitution.ty,
    ht, hm, TypeExpr.subst_id, and_self]

/-- Solving a symbolic source context preserves the original guarded bounds
and bare body through simultaneous substitution composition. -/
theorem result_sound (originalSource originalTarget : Scheme) (before : Substitution)
    (fresh : List Nat) (extra : Bounds) {e : ComparisonChecker.Evidence}
    (h : ComparisonChecker.PreparedSolution
      (SchemePreparation.prepare []
        (source (SchemePreparation.prepare [] originalSource originalTarget) before fresh extra)
        (target (SchemePreparation.prepare [] originalSource originalTarget) originalTarget)) e) :
    let p := SchemePreparation.prepare [] originalSource originalTarget
    let action := ComparisonExactContext.finish before e.substitution
    action.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (action.bounds p.sourceBounds) ∧
      AlgebraSubtype p.assumptions (action.ty p.sourceType) (.ofTy p.targetType) := by
  have he := prepared_target
    (source (SchemePreparation.prepare [] originalSource originalTarget) before fresh extra)
    originalSource originalTarget
  have hr := h.result
  dsimp only at he hr ⊢
  rw [he.1, he.2] at hr
  refine ⟨ComparisonExactContext.finish_wellShaped before hr.1, ?_, ?_⟩
  · rw [ComparisonExactContext.finish_bounds]
    intro c hc
    apply hr.2.1 c
    simpa only [source, CompareSubstitution.bounds, List.map_append] using
      List.mem_append_left (e.substitution.bounds extra) hc
  · simpa only [ComparisonExactContext.finish_ty, source] using hr.2.2

/-- Solving the exposed structural coordinates preserves the complete original
comparison, including partial leaves and all written source guards. -/
theorem template_result_sound (originalSource originalTarget : Scheme)
    (templates : ComparisonSkeleton.Templates) {e : ComparisonChecker.Evidence}
    (h : ComparisonChecker.PreparedSolution
      (SchemePreparation.prepare []
        (templateSource (SchemePreparation.prepare [] originalSource originalTarget) templates)
        (target (SchemePreparation.prepare [] originalSource originalTarget) originalTarget)) e) :
    let p := SchemePreparation.prepare [] originalSource originalTarget
    let action := ComparisonExactContext.finish templates.substitution e.substitution
    action.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (action.bounds p.sourceBounds) ∧
      AlgebraSubtype p.assumptions (action.ty p.sourceType) (.ofTy p.targetType) := by
  have he := prepared_target
    (templateSource (SchemePreparation.prepare [] originalSource originalTarget) templates)
    originalSource originalTarget
  have hr := h.result
  dsimp only at he hr ⊢
  rw [he.1, he.2] at hr
  refine ⟨ComparisonExactContext.finish_wellShaped templates.substitution hr.1, ?_, ?_⟩
  · simpa only [ComparisonExactContext.finish_bounds, templateSource] using hr.2.1
  · simpa only [ComparisonExactContext.finish_ty, templateSource] using hr.2.2

end ModalityInference.ComparisonParameterization
