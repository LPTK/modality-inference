import ModalityInference.Proofs.ComparisonPreparedQueryComplete
import ModalityInference.Proofs.ComparisonPreparedFamilyValidity

/-! Admissible finite-basis images validate every enabled actual alternative.
The endpoint alignment and its original guards come from preparation; the
compiled theory contains only declared constraints. -/
namespace ModalityInference.ComparisonPreparedQueries
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout ComparisonAlgebra
  ComparisonControls ComparisonSelectedBases ComparisonPreparation ComparisonWitnessRestriction

theorem witness_branch_alignment {shapeFuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    {endpoint : Ty×Ty} (he : endpoint∈endpoints (SchemePreparation.prepare [] source target))
    {b : ComparisonSelectedBases.Branch}
    (hb : b∈branches first (SchemePreparation.prepare [] source target) solved endpoint)
    (hg : b.guard.eval world=true) {layout : Layout}
    (hl : selected (inputNames (SchemePreparation.prepare [] source target))
      (ComparisonSelectedBases.inputModes (SchemePreparation.prepare [] source target)) solved.fixedShapes b=some layout) :
    let p:=SchemePreparation.prepare [] source target
    ∃labels : List (GuardedMode p.assumptions),
      b.shape.subst solved.fixedShapes=b.shape ∧
      Endpoint p.assumptions labels (inputTypeKeys p) (inputAction p σ) layout endpoint.1 ∧
      Endpoint p.assumptions labels (inputTypeKeys p) (inputAction p σ) layout endpoint.2 ∧
      (∀g∈labels,∀v∈g.expression.vars,v∈ComparisonSelectedBases.inputModes p) := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨actual,labels,hbuild,_,_,hleft,hright,_,_,hsupport⟩:=prepared_alignment hs hw hsp he
  have hn : ∀v∈endpoint.1.typeVars,v∈inputNames p :=
    fun v hv=>(mem_inputNames p v).mpr ((endpoints_input he).1 hv)
  have hscope : ∀v∈((ComparisonShape.ofTy endpoint.1).subst solved.resolveAll).vars,
      v∈(ComparisonSelectedBases.layout first p solved).parameters := fun _=>template_scope hn
  have hshape:=(bases_sound hp.1 hscope hb hg).1
  rw [←(inputAction_polynomials hw hp).ty_shape hs endpoint.1 hn] at hshape
  have heq : actual=layout := by
    have hl' : build (inputNames p) (ComparisonSelectedBases.inputModes p) solved.fixedShapes
      (((inputAction p σ).ty endpoint.1).shape.subst solved.fixedShapes)=some layout := by
      simpa only [selected,hshape] using hl
    exact Option.some.inj (hbuild.symm.trans hl')
  subst actual
  refine ⟨labels,?_,hleft,hright,?_⟩
  · rw [hshape]
    exact ComparisonShapeRetraction.fixedShapes_idempotent hs _
  · intro g hg v hv
    exact hsupport g hg v (by simpa only [ModExpr.mem_freeVariables] using hv)

theorem branch_witness_valid {shapeFuel normFuel fuel first activation : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    (hi : σ.ModesIdempotent)
    {declared : List ComparisonStructuralEndpoints.Pair}
    (hd : ComparisonStructuralEndpoints.normalizeList normFuel (SchemePreparation.prepare [] source target) solved
      (ComparisonStructuralEndpoints.declared (SchemePreparation.prepare [] source target))=.success declared)
    {endpoint : Ty×Ty} (he : endpoint∈endpoints (SchemePreparation.prepare [] source target))
    {b : ComparisonSelectedBases.Branch}
    (hb : b∈branches first (SchemePreparation.prepare [] source target) solved endpoint)
    (hg : b.guard.eval world=true) {a : Alternative}
    (ha : branch fuel first activation (SchemePreparation.prepare [] source target) solved declared endpoint b=.success (some a)) :
    let p:=SchemePreparation.prepare [] source target
    a.source.source.Valid
      (fun n=>((ComparisonSignedBranchImages.input (ComparisonSignedBranchImages.entries first p solved)).bases n).length)
      (ComparisonPreparedFamily.images (ComparisonSignedBranchImages.entries first p solved) (inputAction p σ))
      (SchemeModeSynthesis.strategy σ.mode) := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨_,_,_,hbuild,htheory,hguards,hremap⟩:=branch_spec ha
  obtain ⟨labels,hfixed,hleft,hright,hsupport⟩:=witness_branch_alignment hs hw hsp hp he hb hg hbuild
  have hab:=(prepared_guarded (inputAction_prepared hw) (inputAction_supported hsp) he).subtype
  have hvalid:=ComparisonPreparedFamily.mapped_valid hs (inputAction_polynomials hw hp)
    (inputAction_modesIdempotent (p:=p) hi) hd (SchemePreparation.prepared_typeBoundsDefined source target)
    hbuild hfixed htheory hleft hright hsupport hab hguards hremap
  exact hvalid

end ModalityInference.ComparisonPreparedQueries
