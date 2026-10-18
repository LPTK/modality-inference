import ModalityInference.Proofs.ComparisonSignedCallCoverage
import ModalityInference.Proofs.ComparisonSignedEndpointQueries
import ModalityInference.Proofs.ComparisonLayoutWorldDecoder

namespace ModalityInference.ComparisonSignedBranchObservation
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonSignedObservation
  ComparisonSignedEndpoints ComparisonSelectedBases ComparisonSignedBranchImages
  ComparisonSignedCallCoverage ComparisonPropagation

private theorem lookup_mem {α : Type} {xs : List (Nat×α)} {key : Nat} {a : α}
    (h : xs.lookup key=some a) : (key,a)∈xs := by
  obtain ⟨left,right,rfl,_⟩:=List.lookup_eq_some_iff.mp h
  simp

theorem selected_reads {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (ComparisonSelectedBases.layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result)
    (hμ : ComparisonModeRestriction.Fixed p.assumptions result.mode)
    {layout : Layout} (hb : Based (inputNames p) (inputModes p) solved.fixedShapes layout)
    (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {closed : List (GuardedMode p.assumptions)} (observation : Nat→Bool) :
    ComparisonLayoutModePullback.Reads hμ closed (inputTypeKeys p) result layout observation
      (ComparisonSignedBranchCalls.pullback (entries first p solved) layout
        (ComparisonSignedPoints.basisImages (fun n=>((input (entries first p solved)).bases n).length)
          ((input (entries first p solved)).imageValue r parameters) observation)) := by
  intro route node hn f c η ht name hname hrep
  have hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode := by
    simpa only [select_mode h] using hμ
  obtain ⟨node',raw,branch,key,hn',he,hbranch,hkey,himage,hshape⟩ :=
    selected_site hs hw hr hm h hf (call:=⟨name,route⟩) ⟨node,hn,hname,hrep⟩
  have hne : node'=node := Option.some.inj (hn'.symm.trans hn)
  subst node'
  have hresolve : ComparisonSignedBranchCalls.resolve (entries first p solved) layout ⟨name,route⟩=
      some ⟨key,route⟩ := by
    simp [ComparisonSignedBranchCalls.resolve,hn,hshape,hkey]
  rw [ComparisonSignedBranchCalls.pullback,hresolve]
  simp only [Option.map_some,Option.getD_some]
  have hbn := nodeAt_based hb hn
  have hpb := entry_basis (entry := (name,branch)) (mem_entries.mpr ⟨hname,(enabled_spec hbranch).1⟩)
  rw [←hshape] at hpb
  have hbe : branch.basis=node.basis := Option.some.inj (hpb.symm.trans hbn.basis)
  have hbas := locate_basis (enabled_spec hbranch).1 hkey
  rw [hbe] at hbas
  have hreify := ((input (entries first p solved)).reconstruct_spec hr).2 _ (lookup_mem himage)
  have hraw : Representable p.assumptions node.shape raw := by
    have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
      fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
    apply reify_property hreify _
    · rw [hbas]
      exact ComparisonStructuralNode.basis_representable node.basis (hbn.valid hshapes).heads
    · exact fun _ _=>ComparisonStructuralLattice.representable_typeOp true
    · exact fun _ _=>ComparisonStructuralLattice.representable_typeOp false
  apply Bool.eq_iff_iff.mpr
  change ComparisonSignedSynthesis.polynomialValue _ _=true ↔ _
  rw [ComparisonSignedSynthesis.polynomialValue_correct]
  have hreify' : reify node.basis.types
      (ComparisonSignedPolynomials.polynomial parameters ((input (entries first p solved)).key key)
        ((input (entries first p solved)).bases key).length
        ((input (entries first p solved)).assignment r))=some raw := by
    rw [←hbas]
    exact hreify
  have hv := ComparisonReifiedEndpointTheory.reified_value hreify'
    (booleanValue (ComparisonObserverModePullback.observer hμ f))
    (booleanValue_join _) (booleanValue_meet _) ht.observes.types
  rw [ComparisonObserverModePullback.observer_value hμ f hraw,←he] at hv
  refine (CNFPropagation.holds_congr ?_).trans hv
  intro i hi
  have hir := List.mem_range.mp (ComparisonReifiedEndpointTheory.reify_support hreify' i hi)
  simp only [ComparisonSignedPoints.basisPoint,hbas,hir,if_true,Function.comp_apply]


/-- A successful branch remapping retains the common image family while the
same symbolic mode strategy acts at every recursive observer world. -/
theorem compiled_family_sound {fuel keys layout left right original clauses}
    (hc : compileGuards fuel (ComparisonSignedEndpoints.compile keys
      (context layout ModExpr.var) left right)=.success original)
    {table : List Entry}
    (hb : ComparisonSignedBranchCalls.compile table layout original=some clauses)
    (size : Nat→Nat) (family : Nat→(Nat→Bool)→Bool) (modes : ModVar→ModExpr)
    {theory : CNF}
    (hv : ComparisonSignedStrategySynthesis.Valid size ComparisonLayoutWorlds.decode theory clauses
      family (SchemeModeSynthesis.strategy modes)) :
    ∀world,CNFHolds (ComparisonLayoutModePullback.acted modes world) theory→
      interpret keys (context layout modes) world
        (ComparisonSignedBranchCalls.pullback table layout
          (ComparisonSignedPoints.basisImages size family world)) [] left ≤
      interpret keys (context layout modes) world
        (ComparisonSignedBranchCalls.pullback table layout
          (ComparisonSignedPoints.basisImages size family world)) [] right := by
  intro world hw
  obtain ⟨blocks,hblocks⟩:=ComparisonLayoutWorlds.rawValue_surjective world
  have hraw : CNFHolds (ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode
      (SchemeModeSynthesis.strategy modes) blocks) theory := by
    change CNFHolds (ComparisonSignedWorlds.rawValue ComparisonLayoutWorlds.decode id
      (SchemeModeSynthesis.strategy modes) blocks) theory
    rw [ComparisonLayoutWorlds.rawValue_apply,hblocks]
    exact hw
  have hold := (ComparisonSignedBranchCalls.compile_correct hb _ _).mp (fun c hcm=>hv blocks c hcm hraw)
  rw [ComparisonLayoutWorlds.basisImages_strategy] at hold
  have he := (ComparisonLayoutWorlds.compiled_strategy hc modes blocks _).mp hold
  apply Bool.le_iff_imp.mpr
  have hblocks' : ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode id blocks=world := hblocks
  simpa only [hblocks'] using he


/-- An active whole-endpoint query for the actual selected branch images
implies its algebraic comparison under the original declared bounds. -/
theorem selected_endpoint_sound {shapeFuel normFuel theoryFuel endpointFuel first : Nat}
    {p : SchemePreparation.Prepared} {solved : ComparisonShapeSolver.Solved}
    {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved
      (ComparisonStructuralEndpoints.declared p)=.success pairs)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {shape : ComparisonShape} {layout : Layout}
    (hbuild : build (inputNames p) (inputModes p) solved.fixedShapes shape=some layout)
    (hf : shape.subst solved.fixedShapes=shape)
    {theory : CNF} (htheory : ComparisonStructuralCoherence.run theoryFuel p.assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success theory)
    {world parameters : Nat→Bool}
    (hw : (ComparisonSelectedBases.layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result)
    (hμ : ComparisonModeRestriction.Fixed p.assumptions result.mode)
    {closed : List (GuardedMode p.assumptions)} {left right : Ty}
    (hl : Endpoint p.assumptions closed (inputTypeKeys p) result layout left)
    (hrr : Endpoint p.assumptions closed (inputTypeKeys p) result layout right)
    (htests : ∀m∈ComparisonStructuralAlignment.tests (inputModes p),∃n∈closed,n.expression=m)
    (hlabels : ∀m∈labels p.assumptions (inputModes p),
      ∃n∈closed,n.expression=m.expression.subst result.mode)
    (hsupport : ∀m∈closed,∀v∈m.expression.freeVariables,v∈inputModes p)
    {original clauses : List CompiledClause}
    (hc : compileGuards endpointFuel (ComparisonSignedEndpoints.compile (inputTypeKeys p)
      (context layout ModExpr.var) left right)=.success original)
    (hb : ComparisonSignedBranchCalls.compile (entries first p solved) layout original=some clauses)
    (hv : ComparisonSignedStrategySynthesis.Valid
      (fun n=>((input (entries first p solved)).bases n).length) ComparisonLayoutWorlds.decode theory clauses
      ((input (entries first p solved)).imageValue r parameters) (SchemeModeSynthesis.strategy result.mode)) :
    AlgebraSubtype p.assumptions (result.ty left) (result.ty right) := by
  have hbased:=(ComparisonStructuralQuerySoundness.build_based hbuild).2
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  have hfixed : layout.shape.subst solved.fixedShapes=layout.shape := by
    simpa only [(ComparisonStructuralQuerySoundness.build_based hbuild).1] using hf
  have hvalid:=hbased.valid hshapes
  apply (subtype_iff_boolean_observers (represented (hl.representable hvalid))
    (represented (hrr.representable hvalid))).mpr
  intro f
  have hn:=ComparisonStructuralTheory.declared_normalized hs hnorm hΔ
  obtain ⟨c,η,observation,ho,ht⟩:=ComparisonLayoutModePullback.run_mapped_labels hμ hbased hshapes
    htests hlabels hsupport (fun _ _ hp=>hn.at_subtype hp) htheory f
  have hreads:=selected_reads hs hw hr h hμ hbased hfixed (closed:=closed) observation
  have he:=compiled_family_sound hc hb _ _ result.mode hv observation ho
  rw [ComparisonLayoutModePullback.interpret_value hl hvalid ht hreads,
    ComparisonLayoutModePullback.interpret_value hrr hvalid ht hreads] at he
  rw [←booleanValue_represented f _ (hl.representable hvalid),
    ←booleanValue_represented f _ (hrr.representable hvalid)]
  exact he

end ModalityInference.ComparisonSignedBranchObservation
