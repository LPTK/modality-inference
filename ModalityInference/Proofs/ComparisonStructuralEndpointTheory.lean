import ModalityInference.Proofs.ComparisonStructuralTrace
import ModalityInference.Proofs.ComparisonStructuralTheory
import ModalityInference.Proofs.ComparisonSignedPreparedEndpoints
import ModalityInference.Proofs.ComparisonLayoutStrategy

/-! Whole public endpoint comparisons are exactly the signed implications from
the recursively compiled declared-bound theory. A common image polynomial is
used at every route, while all annotations use one modality substitution. -/
namespace ModalityInference.ComparisonStructuralEndpointTheory
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonStructuralWorld
  ComparisonStructuralCoherence ComparisonShapedObserverGluing ComparisonStructuralLattice
  ComparisonStructuralRealization ComparisonStructuralQuerySoundness ComparisonSignedObservation
  ComparisonSignedEndpoints ComparisonStructuralEndpoints

theorem run_realized_labels {Δ : Bounds} {names modes fixed layout}
    (hb : Based names modes fixed layout)
    (hs : ∀v,ComparisonShape.Equivalent Δ (.var v) (fixed v))
    {extra : List (GuardedMode Δ)}
    (hbase : ∀g∈ComparisonStructuralLayout.labels Δ modes,g∈extra)
    (hsupport : ∀g∈extra,∀v∈g.expression.freeVariables,v∈modes)
    {endpoints : ComparisonShape→List (CompareTy×CompareTy)}
    (hinput : ∀s,∀pair∈endpoints s,AlgebraSubtype Δ pair.1 pair.2)
    {fuel output} (hr : ComparisonStructuralCoherence.run fuel Δ endpoints layout=.success output)
    (f : LatticeHom (Order Δ layout.shape) Bool) :
    ∃c η world,CNFHolds world output ∧ Realized Δ extra layout f c η world := by
  have hv := hb.valid hs
  let anchor := represented (hv.heads layout.basis.head (by simp [Basis.heads]))
  obtain ⟨c,η,hm⟩ := observer_model f anchor extra
  obtain ⟨q,hq,hqcorrect⟩ := ComparisonStructuralCoherence.run_correct hr
  have htests : ∀m∈ComparisonStructuralAlignment.tests modes,∃n∈extra,n.expression=m := by
    intro m hm
    obtain ⟨g,hg,he⟩ := labels_tests Δ modes m hm
    exact ⟨g,hbase g hg,he⟩
  have hlabels : ∀b : Basis,b.modes=modes→∀p∈b.modalPairs,∃g∈extra,g.expression=p.2 := by
    intro b hb p hp
    obtain ⟨g,hg,he⟩ := labels_basis Δ b hb p hp
    exact ⟨g,hbase g hg,he⟩
  obtain ⟨world,_,hw,htree⟩ := ComparisonStructuralLayout.query_realized htests hsupport hlabels hinput hv hq f hm
  have htop : ∃g∈extra,g.expression=.top := by
    obtain ⟨g,hg,he⟩ := (labels_mem (Δ:=Δ) (modes:=modes) (e:=ModExpr.top)).mpr
      (by simp [labelExpressions,ComparisonStructuralAlignment.tests,ModExpr.top])
    exact ⟨g,hbase g hg,he⟩
  have hbottom : ∃g∈extra,g.expression=.const Mode.bottom := by
    obtain ⟨g,hg,he⟩ := (labels_mem (Δ:=Δ) (modes:=modes) (e:=.const Mode.bottom)).mpr
      (by simp [labelExpressions])
    exact ⟨g,hbase g hg,he⟩
  exact ⟨c,η,world,(hqcorrect world).mpr ⟨hw,Realized.theory htree hv hbottom htop⟩,htree⟩

theorem endpoint_subtype_iff {shapeFuel normFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {pairs : List Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : normalizeList normFuel p solved (declared p)=.success pairs)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {shape : ComparisonShape} {layout : Layout}
    (hbuild : build (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes shape=some layout)
    (hf : shape.subst solved.fixedShapes=shape)
    {theory : CNF} (htheory : ComparisonStructuralCoherence.run fuel p.assumptions
      (atShape pairs) layout=.success theory)
    {extra : List (GuardedMode p.assumptions)} {keys : List Nat} {σ : CompareSubstitution}
    {left right : Ty}
    (hl : Endpoint p.assumptions extra keys σ layout left)
    (hr : Endpoint p.assumptions extra keys σ layout right)
    (hbase : ∀g∈ComparisonStructuralLayout.labels p.assumptions (ComparisonSelectedBases.inputModes p),g∈extra)
    (hsupport : ∀g∈extra,∀v∈g.expression.freeVariables,v∈ComparisonSelectedBases.inputModes p)
    (polynomials : Nat→CNF)
    (hp : ∀n∈keys,∃basis,
      ComparisonStructuralBasis.basis (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
        solved.fixedShapes ((σ.type (.flex n)).shape.subst solved.fixedShapes)=some basis ∧
      ComparisonLatticeCompiler.compile basis (σ.type (.flex n))=some (polynomials n)) :
    AlgebraSubtype p.assumptions (σ.ty left) (σ.ty right) ↔
      ∀world,CNFHolds world theory→
        interpret keys (context layout σ.mode) world (polynomialImages polynomials world) [] left ≤
          interpret keys (context layout σ.mode) world (polynomialImages polynomials world) [] right := by
  have hbased := (build_based hbuild).2
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  have hfixed : layout.shape.subst solved.fixedShapes=layout.shape := by
    simpa only [(build_based hbuild).1] using hf
  have hmodel := ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  have hv := hbased.valid hshapes
  have hvars : ∀g∈extra,∀v∈g.expression.vars,v∈ComparisonSelectedBases.inputModes p :=
    fun g hg v hv=>hsupport g hg v ((g.expression.mem_freeVariables v).mpr hv)
  constructor
  · intro hab world hw
    obtain ⟨child,ht⟩ := ComparisonStructuralTrace.run_trace hs hnorm (fun _ h=>h) hΔ hbuild hf htheory hw
    have hreads := ComparisonStructuralTrace.polynomialImages_reads_of_bases
      (traceNames:=ComparisonSelectedBases.inputModes p) (world:=world) hbased hmodel hfixed polynomials hp
    rw [ComparisonStructuralTrace.interpret_trace hl hv hvars ht hreads,
      ComparisonStructuralTrace.interpret_trace hr hv hvars ht hreads]
    exact child.value_mono (hl.representable hv) (hr.representable hv) hab
  · intro hall
    apply (subtype_iff_boolean_observers (represented (hl.representable hv)) (represented (hr.representable hv))).mpr
    intro f
    have hn := ComparisonStructuralTheory.declared_normalized hs hnorm hΔ
    obtain ⟨c,η,world,hw,ht⟩ := run_realized_labels hbased hshapes hbase hsupport
      (fun _ _ hp=>hn.at_subtype hp) htheory f
    have hreads := ComparisonSignedObservation.polynomialImages_reads_of_bases (labels:=extra) (world:=world) hbased hmodel hfixed polynomials hp
    have h := hall world hw
    rw [hl.interpret_value hv ht hreads,hr.interpret_value hv ht hreads] at h
    rw [←booleanValue_represented f _ (hl.representable hv),←booleanValue_represented f _ (hr.representable hv)]
    exact h

end ModalityInference.ComparisonStructuralEndpointTheory
