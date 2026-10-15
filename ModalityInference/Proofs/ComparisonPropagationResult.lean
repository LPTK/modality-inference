import ModalityInference.Proofs.ComparisonPropagationAgreement
import ModalityInference.Proofs.ComparisonPropagationRuntimeShapes

namespace ModalityInference.ComparisonChecker

theorem modeAllowed_false_of_lt (p : SchemePreparation.Prepared) (v : ModVar)
    (hv : v.index < p.firstMode) : ComparisonInstance.modeAllowed p v = false := by
  cases v with
  | rigid n => rfl
  | flex n =>
    change n < p.firstMode at hv
    simp [ComparisonInstance.modeAllowed, Nat.not_le.mpr hv]

theorem Setup.prepared_target_modes (s : Setup) {source target : Scheme}
    (hp : s.original = SchemePreparation.prepare [] source target) :
    ∀ v ∈ s.original.targetType.modVars, ComparisonInstance.modeAllowed s.original v = false := by
  have ht : s.original.targetType.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_targetType_bounded_first [] source target
  exact fun v hv => modeAllowed_false_of_lt _ v ((TypeExpr.bounded_iff _ _ _).mp ht |>.2 v hv)

theorem Setup.prepared_assumption_modes (s : Setup) {source target : Scheme}
    (hp : s.original = SchemePreparation.prepare [] source target) :
    ∀ v ∈ s.original.assumptions.modVars, ComparisonInstance.modeAllowed s.original v = false := by
  have ht : s.original.assumptions.Bounded s.original.firstType s.original.firstMode := by
    simpa only [hp] using SchemePreparation.prepare_assumptions_bounded_first [] source target
  exact fun v hv => modeAllowed_false_of_lt _ v ((Bounds.bounded_iff _ _ _).mp ht |>.2 v hv)

theorem PropagationTrace.solution_of_semantic {fuel s e source target}
    (t : PropagationTrace fuel s e)
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (hbounds : AlgebraEntailsAll s.original.assumptions
      ((s.semanticAction t.reduced t.types t.modes).bounds s.original.sourceBounds))
    (hbody : AlgebraSubtype s.original.assumptions
      ((s.semanticAction t.reduced t.types t.modes).ty s.original.sourceType)
      (.ofTy s.original.targetType)) : PreparedSolution s.original e := by
  have htarget := s.prepared_target_modes hp
  have hassumptions := s.prepared_assumption_modes hp
  have hbs : s.original.sourceBounds.Bounded s.original.nextType s.original.nextMode := by
    simpa only [hp] using SchemePreparation.prepare_sourceBounds_bounded [] source target
  have hts : s.original.sourceType.Bounded s.original.nextType s.original.nextMode := by
    simpa only [hp] using SchemePreparation.prepare_sourceType_bounded [] source target
  apply t.preparedSolution hb
  · exact s.runtimeAction_wellShaped hp hs hb hbounded t.reduced_eq t.types_eq
  · exact (s.semanticAction_bounds t.reduced_eq t.types_eq htarget hassumptions hbounded
      t.modes s.original.sourceBounds hbs).mp hbounds
  · rw [s.semanticAction_ty t.reduced_eq t.types_eq htarget hassumptions hbounded
      t.modes s.original.sourceType hts] at hbody
    exact hbody

end ModalityInference.ComparisonChecker
