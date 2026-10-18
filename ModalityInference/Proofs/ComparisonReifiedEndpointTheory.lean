import ModalityInference.Proofs.ComparisonStructuralEndpointTheory

/-! Actual positive type reconstruction has the same shared route semantics
as compiled image polynomials. Successful reconstruction itself supplies finite
atom support; no canonical-output equality is required. -/
namespace ModalityInference.ComparisonReifiedEndpointTheory
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonStructuralWorld
  ComparisonShapedObserverGluing ComparisonSignedObservation ComparisonSignedEndpoints
  ComparisonStructuralEndpoints ComparisonPropagation ComparisonStructuralQuerySoundness

theorem clauseType_support {basis : List CompareTy} {clause : Clause} {t : CompareTy}
    (h : clauseType basis clause=some t) : ∀literal∈clause,literal.1<basis.length := by
  induction clause generalizing t with
  | nil => simp [clauseType] at h
  | cons literal rest ih =>
    rcases literal with ⟨v,positive⟩
    cases positive with
    | false => simp [clauseType] at h
    | true =>
      cases hb : basis[v]? with
      | none => simp [clauseType,hb] at h
      | some a =>
        have hv : v<basis.length := by
          by_contra hv
          have hn : basis[v]?=none := List.getElem?_eq_none (Nat.le_of_not_gt hv)
          rw [hn] at hb
          cases hb
        cases rest with
        | nil => simpa using hv
        | cons literal rest =>
          cases ht : clauseType basis (literal::rest) with
          | none => rw [clauseType] at h;simp [hb,ht] at h
          | some b => exact List.forall_mem_cons.mpr ⟨hv,ih ht⟩

theorem reify_support {basis : List CompareTy} {clauses : CNF} {t : CompareTy}
    (h : reify basis clauses=some t) : Supported (List.range basis.length) clauses := by
  have hl : ∀clause∈clauses,∀literal∈clause,literal.1<basis.length := by
    induction clauses generalizing t with
    | nil => simp [reify] at h
    | cons c cs ih =>
      cases hc : clauseType basis c with
      | none => simp [reify,hc] at h
      | some a =>
        cases cs with
        | nil => exact List.forall_mem_singleton.mpr (clauseType_support hc)
        | cons c' cs =>
          cases hr : reify basis (c'::cs) with
          | none => rw [reify] at h;simp [hc,hr] at h
          | some b => exact List.forall_mem_cons.mpr ⟨clauseType_support hc,ih hr⟩
  intro v hv
  obtain ⟨c,hc,b,hb⟩ := CNFPropagation.mem_atoms.mp hv
  exact List.mem_range.mpr (hl c hc (v,b) hb)

theorem reified_value {basis : Basis} {a : CompareTy} {clauses : CNF}
    (h : reify basis.types clauses=some a) (value : CompareTy→Bool)
    (hj : ∀a b,value (.join a b)=(value a || value b))
    (hm : ∀a b,value (.meet a b)=(value a && value b))
    {basisAtom : Nat→Nat} {world : Nat→Bool}
    (hb : ∀i (hi : i<basis.types.length),world (basisAtom i)=value basis.types[i]) :
    CNFHolds (world ∘ basisAtom) clauses ↔ value a=true := by
  refine (CNFPropagation.holds_congr ?_).trans (reify_correct h value hj hm).symm
  intro i hi
  have hir := List.mem_range.mp (reify_support h i hi)
  simpa [basisValue,List.getElem?_eq_getElem hir] using hb i hir

theorem polynomialImages_reads {Δ labels keys σ layout world} (polynomials : Nat → CNF)
    (hp : ∀route node, nodeAt layout route=some node → ∀n∈keys,
      Representable Δ node.shape (σ.type (.flex n)) →
      reify node.basis.types (polynomials n)=some (σ.type (.flex n))) :
    @Reads Δ labels keys σ layout world (polynomialImages polynomials world) := by
  intro route node hn f c η ht n hk hr
  apply Bool.eq_iff_iff.mpr
  exact (ComparisonStructuralMatrix.cnfValue_correct _ _).trans
    (reified_value (hp route node hn n hk hr)
      (booleanValue f) (booleanValue_join f) (booleanValue_meet f) ht.observes.types)


theorem polynomialImages_trace_reads {Δ names keys σ layout world} (polynomials : Nat → CNF)
    (hp : ∀route node, nodeAt layout route=some node → ∀n∈keys,
      Representable Δ node.shape (σ.type (.flex n)) →
      reify node.basis.types (polynomials n)=some (σ.type (.flex n))) :
    @ComparisonStructuralTrace.Reads Δ names keys σ layout world (polynomialImages polynomials world) := by
  intro route node hn child ht n hk hr
  obtain ⟨model,rfl⟩ := ht.realizes
  apply Bool.eq_iff_iff.mpr
  exact (ComparisonStructuralMatrix.cnfValue_correct _ _).trans
    (reified_value (hp route node hn n hk hr)
      (booleanValue model.child.observer) (booleanValue_join model.child.observer) (booleanValue_meet model.child.observer) model.types)



theorem polynomialImages_reads_of_bases {Δ labels keys σ layout world names modes shapes}
    (hb : Based names modes shapes layout) (hmodel : ComparisonShape.Models Δ shapes)
    (hf : layout.shape.subst shapes=layout.shape) (polynomials : Nat → CNF)
    (hp : ∀n∈keys, ∃basis,
      ComparisonStructuralBasis.basis names modes shapes ((σ.type (.flex n)).shape.subst shapes)=some basis ∧
      reify basis.types (polynomials n)=some (σ.type (.flex n))) :
    @Reads Δ labels keys σ layout world (polynomialImages polynomials world) := by
  apply polynomialImages_reads polynomials
  intro route node hn n hk hr
  obtain ⟨basis,hbasis,hcompile⟩ := hp n hk
  have he : (σ.type (.flex n)).shape.subst shapes=node.shape :=
    (hr.2.2 shapes hmodel).trans (nodeAt_fixed hf hn)
  rw [he] at hbasis
  have hbnode := (nodeAt_based hb hn).basis
  have hbe : basis=node.basis := Option.some.inj (hbasis.symm.trans hbnode)
  exact hbe ▸ hcompile


theorem polynomialImages_trace_reads_of_bases {Δ traceNames keys σ layout world names modes shapes}
    (hb : Based names modes shapes layout) (hmodel : ComparisonShape.Models Δ shapes)
    (hf : layout.shape.subst shapes=layout.shape) (polynomials : Nat → CNF)
    (hp : ∀n∈keys, ∃basis,
      ComparisonStructuralBasis.basis names modes shapes ((σ.type (.flex n)).shape.subst shapes)=some basis ∧
      reify basis.types (polynomials n)=some (σ.type (.flex n))) :
    @ComparisonStructuralTrace.Reads Δ traceNames keys σ layout world (polynomialImages polynomials world) := by
  apply polynomialImages_trace_reads polynomials
  intro route node hn n hk hr
  obtain ⟨basis,hbasis,hcompile⟩ := hp n hk
  have he : (σ.type (.flex n)).shape.subst shapes=node.shape :=
    (hr.2.2 shapes hmodel).trans (nodeAt_fixed hf hn)
  rw [he] at hbasis
  have hbnode := (nodeAt_based hb hn).basis
  have hbe : basis=node.basis := Option.some.inj (hbasis.symm.trans hbnode)
  exact hbe ▸ hcompile


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
      reify basis.types (polynomials n)=some (σ.type (.flex n))) :
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
    have hreads := polynomialImages_trace_reads_of_bases
      (traceNames:=ComparisonSelectedBases.inputModes p) (world:=world) hbased hmodel hfixed polynomials hp
    rw [ComparisonStructuralTrace.interpret_trace hl hv hvars ht hreads,
      ComparisonStructuralTrace.interpret_trace hr hv hvars ht hreads]
    exact child.value_mono (hl.representable hv) (hr.representable hv) hab
  · intro hall
    apply (subtype_iff_boolean_observers (represented (hl.representable hv)) (represented (hr.representable hv))).mpr
    intro f
    have hn := ComparisonStructuralTheory.declared_normalized hs hnorm hΔ
    obtain ⟨c,η,world,hw,ht⟩ := ComparisonStructuralEndpointTheory.run_realized_labels hbased hshapes hbase hsupport
      (fun _ _ hp=>hn.at_subtype hp) htheory f
    have hreads := polynomialImages_reads_of_bases (labels:=extra) (world:=world) hbased hmodel hfixed polynomials hp
    have h := hall world hw
    rw [hl.interpret_value hv ht hreads,hr.interpret_value hv ht hreads] at h
    rw [←booleanValue_represented f _ (hl.representable hv),←booleanValue_represented f _ (hr.representable hv)]
    exact h

end ModalityInference.ComparisonReifiedEndpointTheory
