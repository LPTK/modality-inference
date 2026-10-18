import ModalityInference.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonSignedClosedAlignment
import ModalityInference.Proofs.ComparisonSignedBranchObservation

namespace ModalityInference.ComparisonPreparedQueryAlignment
open ComparisonSelectedBases ComparisonSignedBranchImages ComparisonAlgebra ComparisonControls
  ComparisonSignedObservation ComparisonStructuralLayout ComparisonInterpolation

/-- An enabled endpoint alternative has the shape of the actual selected
images, with the shared shape selector interpreted only once. -/
theorem active_shape {shapeFuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (ha : (anchorTheory first (SchemePreparation.prepare ambient source target) solved).eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first (SchemePreparation.prepare ambient source target) solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions
      ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution}
    (h : select first (SchemePreparation.prepare ambient source target) solved world images modes=some result)
    {pair : Ty×Ty} (hp : pair∈endpoints (SchemePreparation.prepare ambient source target))
    {branch : Branch}
    (hb : branch∈ComparisonPreparedQueries.branches first (SchemePreparation.prepare ambient source target) solved pair)
    (hg : branch.guard.eval world=true) :
    branch.shape=(result.ty pair.1).shape.subst solved.fixedShapes := by
  let p:=SchemePreparation.prepare ambient source target
  have hi:=endpoints_input hp
  have hinput : ∀v∈pair.1.typeVars,v∈inputNames p := fun v hv=>(mem_inputNames p v).mpr (hi.1 hv)
  have hanchor:=((ComparisonSelectedBases.layout first p solved).matchTheory_correct solved.fixedShapes
    (anchorEquations p solved) world (anchorEquations_scope first p solved)).mp ha
  have hsbranch := (bases_sound hanchor.1 (fun _=>template_scope hinput) hb hg).1
  exact hsbranch.trans (select_ty_shape hs ha (fun _=>prepared_rigid_input) hr hm h pair.1 hinput).symm

/-- Successful selection supplies endpoint alignment for every active actual
structural alternative; the only semantic input is the required scalar guard. -/
theorem active_alignment {shapeFuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (ha : (anchorTheory first (SchemePreparation.prepare ambient source target) solved).eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first (SchemePreparation.prepare ambient source target) solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions
      ({modes:=modes}:CompareSubstitution).mode)
    (hms : ∀v∈inputModes (SchemePreparation.prepare ambient source target),
      ∀w∈(({modes:=modes}:CompareSubstitution).mode v).vars,
        w∈inputModes (SchemePreparation.prepare ambient source target))
    {result : CompareSubstitution}
    (h : select first (SchemePreparation.prepare ambient source target) solved world images modes=some result)
    {pair : Ty×Ty} (hp : pair∈endpoints (SchemePreparation.prepare ambient source target))
    (hguards : ∀a∈[pair.1,pair.2],∀m∈ComparisonAnnotations.expressions a,
      Entails (SchemePreparation.prepare ambient source target).assumptions (.defined (m.subst result.mode)))
    {branch : Branch}
    (hb : branch∈ComparisonPreparedQueries.branches first (SchemePreparation.prepare ambient source target) solved pair)
    (hg : branch.guard.eval world=true) {layout : Layout}
    (hbuild : selected (inputNames (SchemePreparation.prepare ambient source target))
      (inputModes (SchemePreparation.prepare ambient source target)) solved.fixedShapes branch=some layout) :
    let p:=SchemePreparation.prepare ambient source target
    layout.shape=(result.ty pair.1).shape.subst solved.fixedShapes ∧
      Based (inputNames p) (inputModes p) solved.fixedShapes layout ∧
      ∃closed,
        Endpoint p.assumptions closed (inputTypeKeys p) result layout pair.1 ∧
        Endpoint p.assumptions closed (inputTypeKeys p) result layout pair.2 ∧
        (∀m∈ComparisonStructuralAlignment.tests (inputModes p),∃n∈closed,n.expression=m) ∧
        (∀m∈labels p.assumptions (inputModes p),∃n∈closed,n.expression=m.expression.subst result.mode) ∧
        (∀m∈closed,∀v∈m.expression.freeVariables,v∈inputModes p) := by
  obtain ⟨other,closed,ho,hshape,hbased,hl,hrr,ht,hh,hsup⟩:=
    ComparisonSignedClosedAlignment.select_alignment hs ha hr hm hms h hp hguards
  have he:=active_shape hs ha hr hm h hp hb hg
  have hbo : build (inputNames (SchemePreparation.prepare ambient source target))
      (inputModes (SchemePreparation.prepare ambient source target)) solved.fixedShapes
      ((result.ty pair.1).shape.subst solved.fixedShapes)=some layout := by
    simpa only [selected,he] using hbuild
  have hsame : other=layout := Option.some.inj (ho.symm.trans hbo)
  subst other
  exact ⟨hshape,hbased,closed,hl,hrr,ht,hh,hsup⟩

theorem active_endpoint_sound {shapeFuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (ha : (anchorTheory first (SchemePreparation.prepare ambient source target) solved).eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first (SchemePreparation.prepare ambient source target) solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions
      ({modes:=modes}:CompareSubstitution).mode)
    (hms : ∀v∈inputModes (SchemePreparation.prepare ambient source target),
      ∀w∈(({modes:=modes}:CompareSubstitution).mode v).vars,
        w∈inputModes (SchemePreparation.prepare ambient source target))
    {result : CompareSubstitution}
    (h : select first (SchemePreparation.prepare ambient source target) solved world images modes=some result)
    {pair : Ty×Ty} (hp : pair∈endpoints (SchemePreparation.prepare ambient source target))
    (hguards : ∀a∈[pair.1,pair.2],∀m∈ComparisonAnnotations.expressions a,
      Entails (SchemePreparation.prepare ambient source target).assumptions (.defined (m.subst result.mode)))
    {branch : Branch}
    (hb : branch∈ComparisonPreparedQueries.branches first (SchemePreparation.prepare ambient source target) solved pair)
    (hg : branch.guard.eval world=true) {layout : Layout}
    (hbuild : selected (inputNames (SchemePreparation.prepare ambient source target))
      (inputModes (SchemePreparation.prepare ambient source target)) solved.fixedShapes branch=some layout)
    {normFuel theoryFuel endpointFuel : Nat} {pairs : List ComparisonStructuralEndpoints.Pair}
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel (SchemePreparation.prepare ambient source target) solved
      (ComparisonStructuralEndpoints.declared (SchemePreparation.prepare ambient source target))=.success pairs)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    {theory : CNF}
    (htheory : ComparisonStructuralCoherence.run theoryFuel (SchemePreparation.prepare ambient source target).assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success theory)
    {original clauses : List ComparisonSignedEndpoints.CompiledClause}
    (hc : ComparisonSignedEndpoints.compileGuards endpointFuel
      (ComparisonSignedEndpoints.compile (inputTypeKeys (SchemePreparation.prepare ambient source target))
        (context layout ModExpr.var) pair.1 pair.2)=.success original)
    (hremap : ComparisonSignedBranchCalls.compile
      (entries first (SchemePreparation.prepare ambient source target) solved) layout original=some clauses)
    (hv : ComparisonSignedStrategySynthesis.Valid
      (fun n=>((input (entries first (SchemePreparation.prepare ambient source target) solved)).bases n).length)
      ComparisonLayoutWorlds.decode theory clauses
      ((input (entries first (SchemePreparation.prepare ambient source target) solved)).imageValue r parameters)
      (SchemeModeSynthesis.strategy result.mode)) :
    AlgebraSubtype (SchemePreparation.prepare ambient source target).assumptions
      (result.ty pair.1) (result.ty pair.2) := by
  obtain ⟨hshape,hbased,closed,hl,hrr,ht,hh,hsup⟩:=
    active_alignment hs ha hr hm hms h hp hguards hb hg hbuild
  have hanchor:=((ComparisonSelectedBases.layout first (SchemePreparation.prepare ambient source target) solved).matchTheory_correct
    solved.fixedShapes (anchorEquations (SchemePreparation.prepare ambient source target) solved) world
      (anchorEquations_scope first (SchemePreparation.prepare ambient source target) solved)).mp ha
  have he:=active_shape hs ha hr hm h hp hb hg
  have hfix : branch.shape.subst solved.fixedShapes=branch.shape := by
    rw [he]
    exact ComparisonShapeRetraction.fixedShapes_idempotent hs _
  have hμ : ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions result.mode := by
    simpa only [select_mode h] using hm
  exact ComparisonSignedBranchObservation.selected_endpoint_sound hs hnorm hΔ hbuild hfix htheory
    hanchor.1 hr h hμ hl hrr ht hh hsup hc hremap hv

end ModalityInference.ComparisonPreparedQueryAlignment
