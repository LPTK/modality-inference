import ModalityInference.Proofs.ComparisonSelectedBases
import ModalityInference.Proofs.ComparisonSelectedPolynomials

/-! Actual finite basis branches and positive clause polynomials represent one
admissible witness under shared finite shape selectors. -/

namespace ModalityInference.ComparisonSelectedBases

open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonStructuralLattice
open ComparisonPreparation ComparisonWitnessRestriction ComparisonShapeRetraction

/-- Every observed image is represented by an enabled executable basis branch
and its positive finite clause polynomial, under one shared selector world. -/
def BranchPolynomials (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (action : CompareSubstitution) : Prop :=
  (layout first p solved).theory.eval world = true ∧
  ∀v∈inputNames p, ∃branch∈prepared first p solved v, ∃clauses t,
    branch.guard.eval world = true ∧
    ComparisonLatticeCompiler.compile branch.basis (action.type v) = some clauses ∧
    Polynomial branch.basis clauses ∧ reify branch.basis.types clauses = some t ∧
    Representable p.assumptions branch.shape t ∧ Equiv p.assumptions t (action.type v)

theorem encoded_polynomials {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {ρ : TypeVar → ComparisonShape}
    {action : CompareSubstitution} (hρ : ∀v, ρ v∈shapeChoices p solved)
    (hp : ComparisonStructuralBasis.SelectedPolynomialsOn (inputNames p) (inputModes p)
      p solved ρ action) :
    BranchPolynomials first p solved ((layout first p solved).encode ρ) action := by
  refine ⟨layout_encode hρ, ?_⟩
  intro v hv
  obtain ⟨b, clauses, t, hb, hc, hpoly, ht, hrep, he⟩ := hp v ((mem_inputNames p v).mp hv)
  obtain ⟨branch, hbranch, hg, hs, hbb⟩ := prepared_encoded_complete hρ hv hb
  refine ⟨branch, hbranch, clauses, t, hg, ?_, ?_, ?_, ?_, he⟩
  · simpa only [hbb] using hc
  · simpa only [hbb] using hpoly
  · simpa only [hbb] using ht
  · simpa only [hs] using hrep

/-- The actual prepared witness can be normalized into the executable branch
family without changing its quantified domains or modality assignment. -/
theorem prepared_branch_polynomials {fuel : Nat} {ambient : Bounds}
    {source target : Scheme} {solved : ComparisonShapeSolver.Solved}
    {σ : CompareSubstitution} (first : Nat)
    (hs : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target) =
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hsp : Supported (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    ∃τ ρ, PreparedWitnessUnder p τ ∧ Supported p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      (∀v, ρ v∈shapeChoices p solved) ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ := by
  obtain ⟨τ, ρ, hτ, hsupport, hkeys, hmodes, hchoices, _, hlattice⟩ :=
    ComparisonStructuralBasis.prepared_selected_lattice_on
      (inputNames _) (inputModes _) (mem_inputNames _) (mem_inputModes _) hs hw hsp
  exact ⟨τ, ρ, hτ, hsupport, hkeys, hmodes, hchoices,
    encoded_polynomials hchoices (hlattice.polynomials hs)⟩

/-- Under a finite model of the declared shapes, the full admissible comparison
has one common selector world and actual finite basis polynomials. -/
theorem algebra_branch_polynomials {ambient : Bounds} {source target : Scheme}
    (first : Nat) (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃n solved τ ρ,
      (∀fuel≥n, ComparisonShapeSolver.prepare fuel p = .success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧
      (∀v, ρ v∈shapeChoices p solved) ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ := by
  obtain ⟨σ, hw⟩ := prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n, solved, hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete hw.1 hdecl
  obtain ⟨σ', hw', _, _, hsp⟩ := prepared_supported_under hw
  obtain ⟨τ, ρ, hτ, hsupport, _, _, hchoices, hbranches⟩ :=
    prepared_branch_polynomials first (hs n le_rfl) hw' hsp
  exact ⟨n, solved, τ, ρ, hs, hτ, hsupport, hchoices, hbranches⟩

end ModalityInference.ComparisonSelectedBases
