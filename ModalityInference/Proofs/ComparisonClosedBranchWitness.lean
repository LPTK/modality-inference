import ModalityInference.Proofs.ComparisonSelectedBranchWitness
import ModalityInference.Proofs.ComparisonTypeModeClosure

/-! Shared shape branches admit one idempotent modality assignment. Closing
the reconstructed type annotations under that assignment preserves the
original comparison, including every definedness obligation. -/
namespace ModalityInference.ComparisonSelectedBases

open ComparisonPreparation ComparisonWitnessRestriction ComparisonShapeRetraction

theorem prepared_closed_branch_polynomials {fuel : Nat} {ambient : Bounds}
    {source target : Scheme} {solved : ComparisonShapeSolver.Solved}
    {σ : CompareSubstitution} (first : Nat)
    (hs : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    ∃τ ρ, PreparedWitnessUnder p τ ∧ Supported p τ ∧ τ.ModesIdempotent ∧
      (∀v, ρ v∈shapeChoices p solved) ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ ∧
      PreparedWitnessUnder p τ.closeTypeModes ∧ Supported p τ.closeTypeModes := by
  obtain ⟨σ', hw', hsp, _, hi⟩ := ComparisonFixedModeWitness.prepared_supported_fixed hw
  obtain ⟨τ, ρ, hτ, hsupport, _, hmodes, hchoices, hbranches⟩ :=
    prepared_branch_polynomials first hs hw' hsp
  have hτi := hi.of_modes_eq hmodes
  exact ⟨τ, ρ, hτ, hsupport, hτi, hchoices, hbranches,
    hτ.closeTypeModes hτi, hsupport.closeTypeModes⟩

theorem algebra_closed_branch_polynomials {ambient : Bounds} {source target : Scheme}
    (first : Nat) (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃n solved τ ρ,
      (∀fuel≥n, ComparisonShapeSolver.prepare fuel p = .success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧ τ.ModesIdempotent ∧
      (∀v, ρ v∈shapeChoices p solved) ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ ∧
      PreparedWitnessUnder p τ.closeTypeModes ∧ Supported p τ.closeTypeModes := by
  obtain ⟨σ, hw⟩ := prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n, solved, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete hw.1 hdecl
  obtain ⟨τ, ρ, hτ, hsupport, hi, hchoices, hbranches, hclose, hcs⟩ :=
    prepared_closed_branch_polynomials first (hs n le_rfl) hw
  exact ⟨n, solved, τ, ρ, hs, hτ, hsupport, hi, hchoices, hbranches, hclose, hcs⟩

end ModalityInference.ComparisonSelectedBases
