import ModalityInference.Proofs.ComparisonPreparedFamily
import ModalityInference.Proofs.ComparisonLayoutStrategy
import ModalityInference.Proofs.ComparisonPreparedQueries

/-! The same finite family and idempotent modality action validate every
compiled endpoint query. Raw coordinate projections retain the original scalar
guards, including outside the modality expressions’ defined domain. -/
namespace ModalityInference.ComparisonPreparedFamily
open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonSignedSynthesis
  ComparisonSelectedBases ComparisonSignedBranchImages ComparisonSignedEndpoints
  ComparisonSignedObservation ComparisonStructuralLayout ComparisonStructuralQuerySoundness

theorem strategy_idempotent {σ : CompareSubstitution} (hi : σ.ModesIdempotent)
    (world : Nat→Bool) :
    SchemeModeSynthesis.strategy σ.mode (SchemeModeSynthesis.strategy σ.mode world)=
      SchemeModeSynthesis.strategy σ.mode world := by
  funext i
  have hp := ComparisonLayoutWorlds.project_subst σ.mode world
    (σ.mode (SymbolicModes.atomVariable i))
  rw [hi] at hp
  obtain h | h | h : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
  · simpa only [SchemeModeSynthesis.strategy,SchemeModeSynthesis.coordinate,h] using hp.1.symm
  · simpa only [SchemeModeSynthesis.strategy,SchemeModeSynthesis.coordinate,h] using hp.2.1.symm
  · simpa only [SchemeModeSynthesis.strategy,SchemeModeSynthesis.coordinate,h] using hp.2.2.symm

theorem interpret_idempotent {σ : CompareSubstitution} (hi : σ.ModesIdempotent)
    (world : Nat→Nat→Bool) (layout : Layout) (keys : List Nat)
    (images : Call→Bool) (route : Route) (a : Ty) :
    interpret keys (context layout σ.mode)
        (ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode
          (SchemeModeSynthesis.strategy σ.mode) world) images route a=
      interpret keys (context layout ModExpr.var)
        (ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode
          (SchemeModeSynthesis.strategy σ.mode) world) images route a := by
  let acted : Nat→Nat→Bool := fun b=>
    if b=0 then world b else SchemeModeSynthesis.strategy σ.mode (world b)
  have hid : ComparisonSignedWorlds.rawValue ComparisonLayoutWorlds.decode id id acted=
      ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode
        (SchemeModeSynthesis.strategy σ.mode) world := by
    funext i
    simp only [ComparisonSignedWorlds.rawValue,ComparisonSignedPoints.raw,
      ComparisonWorldClauses.shared,acted]
    split <;> simp_all
  have hact : ComparisonSignedWorlds.rawValue ComparisonLayoutWorlds.decode id
      (SchemeModeSynthesis.strategy σ.mode) acted=
      ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode
        (SchemeModeSynthesis.strategy σ.mode) world := by
    funext i
    simp only [ComparisonSignedWorlds.rawValue,ComparisonSignedPoints.raw,
      ComparisonWorldClauses.shared,acted]
    split <;> simp_all [strategy_idempotent hi]
  simpa only [hid,hact] using
    ComparisonLayoutWorlds.interpret_strategy σ.mode acted layout keys images route a

theorem mapped_valid {shapeFuel normFuel theoryFuel guardFuel first : Nat}
    {p : SchemePreparation.Prepared} {solved : ComparisonShapeSolver.Solved}
    {σ : CompareSubstitution} {shapeWorld : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hp : BranchPolynomials first p solved shapeWorld σ) (hi : σ.ModesIdempotent)
    {pairs : List ComparisonStructuralEndpoints.Pair}
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved
      (ComparisonStructuralEndpoints.declared p)=.success pairs)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {shape : ComparisonShape} {layout : Layout}
    (hbuild : build (inputNames p) (inputModes p) solved.fixedShapes shape=some layout)
    (hf : shape.subst solved.fixedShapes=shape)
    {theory : CNF} (htheory : ComparisonStructuralCoherence.run theoryFuel p.assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success theory)
    {labels : List (GuardedMode p.assumptions)} {left right : Ty}
    (hl : Endpoint p.assumptions labels (inputTypeKeys p) σ layout left)
    (hr : Endpoint p.assumptions labels (inputTypeKeys p) σ layout right)
    (hsupport : ∀g∈labels,∀v∈g.expression.vars,v∈inputModes p)
    (hab : AlgebraSubtype p.assumptions (σ.ty left) (σ.ty right))
    {original mapped : List CompiledClause}
    (hc : compileGuards guardFuel (ComparisonSignedEndpoints.compile (inputTypeKeys p)
      (context layout ModExpr.var) left right)=.success original)
    (hm : ComparisonSignedBranchCalls.compile (entries first p solved) layout original=some mapped) :
    ComparisonSignedEndpointQueries.Source.Valid
      ⟨ComparisonLayoutWorlds.decode,theory,mapped⟩
      (fun n=>((input (entries first p solved)).bases n).length)
      (images (entries first p solved) σ) (SchemeModeSynthesis.strategy σ.mode) := by
  have hbased := (build_based hbuild).2
  have hfixed : layout.shape.subst solved.fixedShapes=layout.shape := by
    simpa only [(build_based hbuild).1] using hf
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor
      (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  have hv := hbased.valid hshapes
  intro worlds c hcm ht
  let observation := ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode
    (SchemeModeSynthesis.strategy σ.mode) worlds
  let calls := ComparisonSignedPoints.basisImages
    (fun n=>((input (entries first p solved)).bases n).length)
    (images (entries first p solved) σ) observation
  apply (ComparisonSignedBranchCalls.compile_correct hm observation calls).mpr ?_ c hcm
  rw [compileGuards_correct hc,ComparisonSignedEndpoints.compile_correct]
  let originalCalls := ComparisonSignedBranchCalls.pullback (entries first p solved) layout calls
  have hreads := trace_reads hs hp hbased hfixed observation
  obtain ⟨child,htrace⟩ := ComparisonStructuralTrace.run_trace hs hnorm (fun _ h=>h)
    hΔ hbuild hf htheory ht
  have horder := child.value_mono (hl.representable hv) (hr.representable hv) hab
  have heleft := ComparisonStructuralTrace.interpret_trace hl hv hsupport htrace hreads
  have heright := ComparisonStructuralTrace.interpret_trace hr hv hsupport htrace hreads
  rw [←heleft,←heright] at horder
  rw [interpret_idempotent hi worlds layout (inputTypeKeys p) originalCalls [] left,
    interpret_idempotent hi worlds layout (inputTypeKeys p) originalCalls [] right] at horder
  exact fun hleft=>Bool.le_iff_imp.mp horder hleft

end ModalityInference.ComparisonPreparedFamily
