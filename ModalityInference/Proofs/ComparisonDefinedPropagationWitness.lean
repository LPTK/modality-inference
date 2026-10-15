import ModalityInference.Proofs.ComparisonDefinedSetup

/-! Admissible comparison witnesses reach the ordinary propagation input with
the explicit guards used by the public checker. -/

namespace ModalityInference

theorem AlgebraSubsumesUnder.requireDefinedInstances {Δ : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder Δ source target) :
    AlgebraSubsumesUnder Δ source.requireDefinedInstances target := by
  simp only [AlgebraSubsumesUnder, Scheme.requireDefinedInstances_subsumptionIndices] at h ⊢
  obtain ⟨σ, hi, hs, hw, hd, hb, ht⟩ := h
  refine ⟨σ, hi, hs, hw, hd, ?_, ht⟩
  simpa only [Scheme.requireDefinedInstances, CompareSubstitution.bounds,
    List.map_append, AlgebraEntailsAll, List.mem_append, or_imp, forall_and] using
    And.intro hb ((σ.instance_guards_iff hi hs).mpr ⟨hw, hd⟩)

namespace ComparisonChecker

open SchemePreparation

/-- Every admissible comparison in the residual-target domain eventually
reaches the actual ordinary template input with a defined shared witness. -/
theorem algebra_ordinary_template_complete {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    let p := prepare [] source.requireDefinedInstances target
    ∃ n, ∀ fuel ≥ n, ∃ solved σ,
      ComparisonShapeSolver.prepare fuel p = .success (.solved solved) ∧
      ComparisonPreparation.PreparedWitnessUnder p σ ∧
      ∀ known : List ModExpr,
        let s : Setup := ⟨p, {}, solved, known, false⟩
        ∃ trees : ComparisonSkeleton.CoordinateTrees p.assumptions p solved,
          let core := ComparisonSkeleton.preparedForest p solved trees σ
          core.WellShaped s.work.assumptions ∧ core.WellFormedUnder s.work.assumptions ∧
          AlgebraEntailsAll s.work.assumptions
            (core.bounds (s.templates.substitution.bounds s.work.sourceBounds)) ∧
          (core.ty (s.templates.substitution.ty s.work.sourceType)).DefinedUnder s.work.assumptions ∧
          AlgebraSubtype s.work.assumptions
            (core.ty (s.templates.substitution.ty s.work.sourceType)) (.ofTy s.work.targetType) ∧
          (∀ v, v.index < p.nextMode → core.mode v = σ.mode v) ∧
          (∀ v, v.index < p.nextType → core.type v = .var v) := by
  obtain ⟨σ, hw⟩ := ComparisonPreparation.prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n, solved, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete_residual hw.1
    (prepare_assumptions_residual (source := source.requireDefinedInstances) hR)
  exact ⟨n, fun fuel hf => ⟨solved, σ, hs fuel hf, hw,
    prepared_ordinary_template_under (hs fuel hf) hw ht hm hR⟩⟩

end ComparisonChecker
end ModalityInference
