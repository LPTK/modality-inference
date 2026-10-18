import ModalityInference.Proofs.ComparisonClosedBranchWitness
import ModalityInference.Proofs.ComparisonFixedModeScope
import ModalityInference.Proofs.ComparisonPreparedScalar
import ModalityInference.Proofs.ComparisonInputAction

/-! Admissible normalization retains an exact finite source-modality domain.
The resulting shared coordinate strategy is uniform and supports all selected
structural branches simultaneously. -/
namespace ModalityInference.ComparisonPreparedScalar

def ModeDomain (p : SchemePreparation.Prepared) (σ : CompareSubstitution) : Prop :=
  ∀entry∈σ.modes,entry.1∈modeIds p

theorem ModeDomain.uniform {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : ModeDomain p σ) :
    ModalSynthesis.Uniform ModalSynthesis.locality (flexibleAtoms p)
      (SchemeModeSynthesis.strategy σ.mode) := by
  apply SchemeModeSynthesis.strategy_uniform
  intro v hv
  cases v with
  | rigid n => rfl
  | flex n =>
    have hn : σ.modes.lookup n=none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      exact bne_iff_ne.mpr (fun hne=>hv entry.1 (h entry he) (by rw [hne]))
    simp only [CompareSubstitution.mode,hn,Option.getD_none]

end ModalityInference.ComparisonPreparedScalar

namespace ModalityInference.ComparisonFixedModeWitness
open ComparisonPreparation ComparisonWitnessRestriction

theorem prepared_supported_fixed_modeDomain {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    let p:=SchemePreparation.prepare ambient source target
    ∃τ,PreparedWitnessUnder p τ ∧ Supported p τ ∧ FixedImages p.firstMode τ ∧
      τ.ModesIdempotent ∧ ComparisonPreparedScalar.ModeDomain p τ := by
  obtain ⟨σ',hs,_,_,hsp⟩ := prepared_supported_under hw
  let p:=SchemePreparation.prepare ambient source target
  refine ⟨project p.firstMode p.sourceBounds p.sourceType σ',
    (prepared_project hs).1,project_supported hsp,(prepared_project hs).2,
    project_modesIdempotent _ _ _ _,?_⟩
  intro entry he
  apply (ComparisonPreparedScalar.mem_modeIds p entry.1).mpr
  apply project_modeDomain σ' ?_ entry he
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).2 v hv
  · exact ((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceType_bounded ambient source target)).2 v hv

end ModalityInference.ComparisonFixedModeWitness

namespace ModalityInference.ComparisonSelectedBases
open ComparisonPreparation ComparisonWitnessRestriction ComparisonShapeRetraction

theorem BranchPolynomials.inputAction {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hp : BranchPolynomials first p solved world σ)
    (hd : σ.DomainsAbove p.firstType p.firstMode) :
    BranchPolynomials first p solved world (inputAction p σ) := by
  refine ⟨hp.1,?_⟩
  intro v hv
  simpa only [inputAction_type hd hv] using hp.2 v hv

theorem prepared_closed_branch_polynomials_scoped {fuel : Nat} {ambient : Bounds}
    {source target : Scheme} {solved : ComparisonShapeSolver.Solved}
    {σ : CompareSubstitution} (first : Nat)
    (hs : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare ambient source target)=
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    let p:=SchemePreparation.prepare ambient source target
    ∃τ ρ,PreparedWitnessUnder p τ ∧ Supported p τ ∧ τ.ModesIdempotent ∧
      ComparisonPreparedScalar.ModeDomain p τ ∧
      (∀v,ρ v∈shapeChoices p solved) ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ ∧
      PreparedWitnessUnder p τ.closeTypeModes ∧ Supported p τ.closeTypeModes := by
  obtain ⟨σ',hw',hsp,_,hi,hdom⟩ :=
    ComparisonFixedModeWitness.prepared_supported_fixed_modeDomain hw
  obtain ⟨τ,ρ,hτ,hsupport,_,hmodes,hchoices,hbranches⟩ :=
    prepared_branch_polynomials first hs hw' hsp
  have hτi:=hi.of_modes_eq hmodes
  refine ⟨τ,ρ,hτ,hsupport,hτi,?_,hchoices,hbranches,
    hτ.closeTypeModes hτi,hsupport.closeTypeModes⟩
  intro entry he
  exact hdom entry (hmodes ▸ he)

theorem algebra_closed_branch_polynomials_scoped {ambient : Bounds} {source target : Scheme}
    (first : Nat) (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ,ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p:=SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃n solved τ ρ,
      (∀fuel≥n,ComparisonShapeSolver.prepare fuel p=.success (.solved solved)) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧ τ.ModesIdempotent ∧
      ComparisonPreparedScalar.ModeDomain p τ ∧
      (∀v,ρ v∈shapeChoices p solved) ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ ∧
      PreparedWitnessUnder p τ.closeTypeModes ∧ Supported p τ.closeTypeModes := by
  obtain ⟨σ,hw⟩ := prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n,solved,hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete hw.1 hdecl
  obtain ⟨τ,ρ,hτ,hsp,hi,hdom,hchoices,hbranches,hclose,hcs⟩ :=
    prepared_closed_branch_polynomials_scoped first (hs n le_rfl) hw
  exact ⟨n,solved,τ,ρ,hs,hτ,hsp,hi,hdom,hchoices,hbranches,hclose,hcs⟩

end ModalityInference.ComparisonSelectedBases
