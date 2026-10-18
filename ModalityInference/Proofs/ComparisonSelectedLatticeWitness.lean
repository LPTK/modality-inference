import ModalityInference.Proofs.ComparisonStructuralWitness
import ModalityInference.Proofs.ComparisonSelectedShapeBounds

/-! Finite input shape choices and structural lattice bases normalize one
complete defined comparison witness, with its shared modalities unchanged. -/

namespace ModalityInference.ComparisonStructuralBasis

open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice
open ComparisonShapeRetraction ComparisonWitnessRestriction ComparisonPreparation

def SelectedLattice (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (ρ : TypeVar → ComparisonShape) (action : CompareSubstitution) : Prop :=
  ∀v∈inputTypes p, ∃b,
    basis (inputTypes p).toList (inputModes p).toList solved.fixedShapes
      (((solved.resolveAll v).subst ρ).subst solved.fixedShapes) = some b ∧
    LatticeForm b.types (action.type v) ∧
    Representable p.assumptions (((solved.resolveAll v).subst ρ).subst solved.fixedShapes)
      (action.type v)

/-- Finite source-shape selection and finite lattice normalization share a
single admissible substitution and the original modality assignment. -/
theorem prepared_selected_lattice {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hsp : Supported (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    ∃τ ρ, PreparedWitnessUnder p τ ∧ Supported p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      (∀v, ρ v ∈ shapeChoices p solved) ∧
      (∀v∈inputTypes p, ComparisonShape.Equivalent p.assumptions (τ.type v).shape
        ((solved.resolveAll v).subst ρ)) ∧ SelectedLattice p solved ρ τ := by
  obtain ⟨selected, ρ, hw', hsp', ht', hm', hc, hs⟩ := prepared_selected_shapes h hw hsp
  obtain ⟨result, hw'', ht'', hm'', hsp'', hr, hl⟩ := prepared_lattice_witness h hw' hsp'
  refine ⟨result, ρ, hw'', hsp'', ht''.trans ht', hm''.trans hm', hc, ?_, ?_⟩
  · intro v hv
    exact (hr.images v).1.shape_equivalent.symm.trans (hs v hv)
  · intro v hv
    have he := hs v hv solved.fixedShapes
      (ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp h).1)
    simpa only [he] using hl v hv

/-- Every admissible comparison with a finite declared shape model has one
witness in the input-relative family of finite structural lattice bases. -/
theorem algebra_selected_lattice {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃n solved τ ρ,
      (∀fuel≥n, ComparisonShapeSolver.prepare fuel p = .success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧
      (∀v, ρ v ∈ shapeChoices p solved) ∧
      (∀v∈inputTypes p, ComparisonShape.Equivalent p.assumptions (τ.type v).shape
        ((solved.resolveAll v).subst ρ)) ∧ SelectedLattice p solved ρ τ := by
  obtain ⟨σ, hw⟩ := prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n, solved, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete hw.1 hdecl
  obtain ⟨σ', hw', _, _, hsp⟩ := prepared_supported_under hw
  obtain ⟨τ, ρ, ht, htp, _, _, hchoices, hshapes, hlattice⟩ :=
    prepared_selected_lattice (hs n le_rfl) hw' hsp
  exact ⟨n, solved, τ, ρ, hs, ht, htp, hchoices, hshapes, hlattice⟩

end ModalityInference.ComparisonStructuralBasis
