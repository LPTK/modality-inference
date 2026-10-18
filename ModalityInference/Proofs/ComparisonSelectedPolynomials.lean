import ModalityInference.Proofs.ComparisonSelectedLatticeWitness
import ModalityInference.Proofs.ComparisonLatticeCompiler

/-! The input-relative lattice witness is covered by actual finite positive
clause outputs, preserving its shared parameters and original guarded context. -/
namespace ModalityInference.ComparisonStructuralBasis

open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonStructuralLattice
open ComparisonShapeRetraction ComparisonWitnessRestriction ComparisonPreparation

def SelectedPolynomialsOn (names : List TypeVar) (modes : List ModVar) (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (ρ : TypeVar → ComparisonShape) (action : CompareSubstitution) : Prop :=
  ∀v∈inputTypes p, ∃b clauses t,
    basis names modes solved.fixedShapes
      (((solved.resolveAll v).subst ρ).subst solved.fixedShapes) = some b ∧
    ComparisonLatticeCompiler.compile b (action.type v) = some clauses ∧
    Polynomial b clauses ∧ reify b.types clauses = some t ∧
    Representable p.assumptions (((solved.resolveAll v).subst ρ).subst solved.fixedShapes) t ∧
    Equiv p.assumptions t (action.type v)


def SelectedPolynomials (p : SchemePreparation.Prepared) (solved : ComparisonShapeSolver.Solved)
    (ρ : TypeVar → ComparisonShape) (action : CompareSubstitution) : Prop :=
  SelectedPolynomialsOn (inputTypes p).toList (inputModes p).toList p solved ρ action

theorem SelectedLatticeOn.polynomials {names : List TypeVar} {modes : List ModVar}
    {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {ρ : TypeVar → ComparisonShape}
    {action : CompareSubstitution}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hl : SelectedLatticeOn names modes p solved ρ action) : SelectedPolynomialsOn names modes p solved ρ action := by
  intro v hv
  obtain ⟨b, hb, hform, _⟩ := hl v hv
  obtain ⟨clauses, hc⟩ := ComparisonLatticeCompiler.compile_complete hform
  have hheads := heads_representable names modes
    solved.fixedShapes (fun v => ComparisonSkeleton.fixedShapes_equivalent h (.var v))
    (((solved.resolveAll v).subst ρ).subst solved.fixedShapes)
  have htypes : ∀t∈b.types, Representable p.assumptions
      (((solved.resolveAll v).subst ρ).subst solved.fixedShapes) t := by
    rw [(basis_spec hb).2.2]
    exact extend_representable _ hheads
  obtain ⟨t, ht, hrep, he⟩ := ComparisonLatticeCompiler.compile_correct htypes hc
  exact ⟨b, clauses, t, hb, hc, (ComparisonLatticeCompiler.compile_polynomial hc).2, ht, hrep, he⟩


theorem SelectedLattice.polynomials {fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {ρ : TypeVar → ComparisonShape}
    {action : CompareSubstitution}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved solved))
    (hl : SelectedLattice p solved ρ action) : SelectedPolynomials p solved ρ action :=
  SelectedLatticeOn.polynomials h hl

theorem algebra_selected_polynomials {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃n solved τ ρ,
      (∀fuel≥n, ComparisonShapeSolver.prepare fuel p = .success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧
      (∀v, ρ v ∈ shapeChoices p solved) ∧
      (∀v∈inputTypes p, ComparisonShape.Equivalent p.assumptions (τ.type v).shape
        ((solved.resolveAll v).subst ρ)) ∧ SelectedPolynomials p solved ρ τ := by
  obtain ⟨n, solved, τ, ρ, hs, hw, hsp, hc, hshape, hl⟩ := algebra_selected_lattice h hdecl
  exact ⟨n, solved, τ, ρ, hs, hw, hsp, hc, hshape, hl.polynomials (hs n le_rfl)⟩

end ModalityInference.ComparisonStructuralBasis
