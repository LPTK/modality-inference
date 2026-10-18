import ModalityInference.Proofs.ComparisonSelectedWitness

/-! Selected shapes range over a finite family determined by the prepared
input. The corresponding defined witness retains all original obligations. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonShapeSolver ComparisonWitnessRestriction ComparisonPreparation

theorem shapeChoice_mem (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (σ : CompareSubstitution) (v : TypeVar) :
    choose (shapeChoices p solved) (normalizedRealizer p σ solved) v ∈ shapeChoices p solved :=
  ComparisonShape.select_mem_candidates (anchorNames p solved) solved.fixedShapes
    (anchorTemplates p) (normalizedRealizer p σ solved) v

/-- A finite model of the declared shapes gives an input-relative finite
choice family covering a whole admissible prepared witness simultaneously. -/
theorem prepared_selected_shapes {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hsp : Supported (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    ∃ τ ρ, PreparedWitnessUnder p τ ∧ Supported p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      (∀ v, ρ v ∈ shapeChoices p solved) ∧
      ∀ v ∈ inputTypes p, ComparisonShape.Equivalent p.assumptions (τ.type v).shape
        ((solved.resolveAll v).subst ρ) := by
  exact ⟨selectedAction h hw, _, selectedAction_prepared h hw,
    selectedAction_supported h hw hsp, selectedAction_keys h hw, selectedAction_modes h hw,
    shapeChoice_mem _ _ σ, fun _ hv => selectedAction_shape h hw hv⟩

/-- The bounded witness is obtained from the full defined-instance relation
under arbitrary ambient bounds; all guards remain obligations of that context. -/
theorem algebra_selected_shapes {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃ φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃ n solved τ ρ,
      (∀ fuel ≥ n, prepare fuel p = .success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧
      (∀ v, ρ v ∈ shapeChoices p solved) ∧
      ∀ v ∈ inputTypes p, ComparisonShape.Equivalent p.assumptions (τ.type v).shape
        ((solved.resolveAll v).subst ρ) := by
  obtain ⟨σ, hw⟩ := prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n, solved, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete hw.1 hdecl
  obtain ⟨σ', hw', _, _, hsp⟩ := prepared_supported_under hw
  obtain ⟨τ, ρ, ht, htp, _, _, hchoices, hshapes⟩ := prepared_selected_shapes (hs n le_rfl) hw' hsp
  exact ⟨n, solved, τ, ρ, hs, ht, htp, hchoices, hshapes⟩

end ModalityInference.ComparisonShapeRetraction
