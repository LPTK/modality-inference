import ModalityInference.Proofs.ComparisonCheckerScope

/-! The semantic interface between prepared comparison phases and the original
scheme-subsumption judgment. -/
namespace ModalityInference.ComparisonChecker

def PreparedSolution (p : SchemePreparation.Prepared) (e : Evidence) : Prop :=
  ∃ action : CompareSubstitution,
    e.substitution = ComparisonPreparation.reconstruct p action ∧
    e.obligations = action.bounds p.sourceBounds ∧
    e.body = (action.ty p.sourceType, CompareTy.ofTy p.targetType) ∧
    action.DomainsAbove p.firstType p.firstMode ∧
    action.WellShaped p.assumptions ∧
    AlgebraEntailsAll p.assumptions (action.bounds p.sourceBounds) ∧
    AlgebraSubtype p.assumptions (action.ty p.sourceType) (CompareTy.ofTy p.targetType)

theorem PreparedSolution.subsumes {ambient : Bounds} {source target : Scheme} {e : Evidence}
    (h : PreparedSolution (SchemePreparation.prepare ambient source target) e) :
    AlgebraSubsumes ambient source target := by
  obtain ⟨action, _, _, _, hd, hs, hb, ht⟩ := h
  apply ComparisonPreparation.reconstruct_algebra_sound ambient source target action ?_ ?_ hs hb ht
  · intro v hv
    apply hd.type_fixed
    apply SchemePreparation.original_type_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalTypeIds, List.mem_append,
      TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
    tauto
  · intro v hv
    apply hd.mode_fixed
    apply SchemePreparation.original_mode_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalModeIds, List.mem_append,
      TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
    tauto

/-- The evidence's actual substitution realizes the original source scheme. -/
theorem PreparedSolution.result {ambient : Bounds} {source target : Scheme} {e : Evidence}
    (h : PreparedSolution (SchemePreparation.prepare ambient source target) e) :
    let p := SchemePreparation.prepare ambient source target
    e.substitution.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (e.substitution.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (e.substitution.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨action, he, _, _, hd, hs, hb, ht⟩ := h
  let p := SchemePreparation.prepare ambient source target
  have htypes : ∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars,
      action.type v = .var v := by
    intro v hv
    apply hd.type_fixed
    apply SchemePreparation.original_type_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalTypeIds, List.mem_append,
      TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
    tauto
  have hmodes : ∀ v ∈ source.body.modVars ∪ source.bounds.modVars,
      action.mode v = .var v := by
    intro v hv
    apply hd.mode_fixed
    apply SchemePreparation.original_mode_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalModeIds, List.mem_append,
      TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
    tauto
  rw [he]
  refine ⟨ComparisonPreparation.reconstruct_wellShaped hs, ?_, ?_⟩
  · exact (ComparisonPreparation.reconstruct_algebra_bounds p action source.bounds p.assumptions
      (fun v hv => htypes v (Finset.mem_union_right _ hv))
      (fun v hv => hmodes v (Finset.mem_union_right _ hv))).mpr hb
  · change AlgebraSubtype p.assumptions
      ((ComparisonPreparation.reconstruct p action).ty source.body) (.ofTy p.targetType)
    rw [ComparisonPreparation.reconstruct_ty p action source.body
      (fun v hv => htypes v (Finset.mem_union_left _ hv))
      (fun v hv => hmodes v (Finset.mem_union_left _ hv))]
    exact ht

theorem exact_solution {fuel : Nat} {p : SchemePreparation.Prepared} {result : ComparisonInstance.Result}
    (h : ComparisonInstance.attempt fuel p = .success (some result)) :
    PreparedSolution p
      { substitution := ComparisonPreparation.reconstruct p (.ofSubstitution result.action)
        assumptions := p.assumptions
        obligations := (CompareSubstitution.ofSubstitution result.action).bounds p.sourceBounds
        body := ((CompareSubstitution.ofSubstitution result.action).ty p.sourceType, .ofTy p.targetType)
        flexibleAtoms := []
        query := result.query
        backend := result.backend } := by
  have hr := ComparisonInstance.attempt_some_iff.mp h
  refine ⟨.ofSubstitution result.action, rfl, rfl, rfl,
    ComparisonInstance.run_domainsAbove hr, CompareSubstitution.wellShaped_ofSubstitution _ _, ?_, ?_⟩
  · simpa only [CompareSubstitution.ofSubstitution_bounds] using
      (ComparisonInstance.run_entails hr).to_shaped.to_algebra
  · simp only [CompareSubstitution.ofSubstitution_ty, ComparisonInstance.run_body hr]
    exact .refl (CompareTy.wellShaped_ofTy _ _)

end ModalityInference.ComparisonChecker
