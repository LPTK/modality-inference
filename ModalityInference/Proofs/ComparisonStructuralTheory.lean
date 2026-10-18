import ModalityInference.Proofs.ComparisonStructuralQuerySoundness
import ModalityInference.Proofs.ComparisonStructuralEndpointQuery

/-! The recursively compiled declared-bound theory is exact for defined
finite-basis types. Finite query models reconstruct genuine algebra observers,
and every algebra observer supplies a finite query model. Required comparisons
remain implications from this theory rather than assumptions within it. -/
namespace ModalityInference.ComparisonStructuralTheory
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout
  ComparisonStructuralEndpoints ComparisonStructuralQuerySoundness

theorem normalizeList_correct {shapeFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy×CompareTy)}
    {pairs : List Pair} (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (h : normalizeList fuel p solved originals=.success pairs)
    (hg : ∀pair∈originals,GuardedPair p pair) : NormalizedList p solved originals pairs := by
  have ht := normalizeList_spec h
  clear h
  induction ht with
  | nil => exact .nil
  | @cons original pair rest pairs hp ht ih =>
    have ho := hg original List.mem_cons_self
    have hn := normalizePair_correct hs
      ⟨ho.subtype.wellShaped_left,ho.left_defined,ho.left_supported⟩
      ⟨ho.subtype.wellShaped_right,ho.right_defined,ho.right_supported⟩
      ho.subtype.shape_equivalent hp
    exact .cons ⟨hn,hn.subtype_iff.mp ho.subtype⟩
      (ih (fun p hp=>hg p (List.mem_cons_of_mem _ hp)))

theorem declared_normalized {shapeFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {pairs : List Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (h : normalizeList fuel p solved (declared p)=.success pairs)
    (hΔ : p.assumptions.TypeBoundsDefined) : NormalizedList p solved (declared p) pairs :=
  normalizeList_correct hs h (declared_guarded p hΔ)

theorem compiled_subtype_iff {shapeFuel normFuel fuel : Nat} {p : SchemePreparation.Prepared}
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
    {a b : CompareTy} {left right : CNF}
    (ha : Representable p.assumptions layout.shape a)
    (hb : Representable p.assumptions layout.shape b)
    (hl : ComparisonLatticeCompiler.compile layout.basis a=some left)
    (hr : ComparisonLatticeCompiler.compile layout.basis b=some right) :
    AlgebraSubtype p.assumptions a b ↔
      ∀world,CNFHolds world theory→
        CNFHolds (world ∘ basisAtom) left→ CNFHolds (world ∘ basisAtom) right := by
  constructor
  · intro hab world hw hleft
    obtain ⟨model⟩ := ComparisonStructuralQuerySoundness.run_realizes hs hnorm
      (fun _ hp=>hp) hΔ hbuild hf htheory hw
    have hc₁ := ComparisonStructuralNode.compiled_value hl (booleanValue model.child.observer)
      (booleanValue_join _) (booleanValue_meet _) model.types
    have hc₂ := ComparisonStructuralNode.compiled_value hr (booleanValue model.child.observer)
      (booleanValue_join _) (booleanValue_meet _) model.types
    exact hc₂.mpr ((Bool.le_iff_imp.mp (model.child.value_mono ha hb hab)) (hc₁.mp hleft))
  · intro h
    apply (subtype_iff_boolean_observers (represented ha) (represented hb)).mpr
    intro f
    have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
      fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
    have hn := declared_normalized hs hnorm hΔ
    obtain ⟨c,η,world,hw,htree⟩ := ComparisonStructuralCoherence.run_realized
      (build_based hbuild).2 hshapes (fun _ _ hp=>hn.at_subtype hp) htheory f
    have hc₁ := ComparisonStructuralNode.compiled_value hl (booleanValue f)
      (booleanValue_join f) (booleanValue_meet f) htree.observes.types
    have hc₂ := ComparisonStructuralNode.compiled_value hr (booleanValue f)
      (booleanValue_join f) (booleanValue_meet f) htree.observes.types
    rw [←booleanValue_represented f a ha,←booleanValue_represented f b hb]
    exact Bool.le_iff_imp.mpr (fun hx=>hc₂.mp (h world hw (hc₁.mpr hx)))

theorem compile_declared_complete {shapeFuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hΔ : p.assumptions.TypeBoundsDefined) {shape : ComparisonShape} {layout : Layout}
    (hbuild : build (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes shape=some layout) :
    ∃threshold pairs theory,∀fuel≥threshold,
      normalizeList fuel p solved (declared p)=.success pairs ∧
      ComparisonStructuralCoherence.run fuel p.assumptions (atShape pairs) layout=.success theory := by
  obtain ⟨n,pairs,hn,hcorrect⟩ := normalizeList_complete hs (declared p) (declared_guarded p hΔ)
  obtain ⟨q,hq⟩ := (build_based hbuild).2.query_complete p.assumptions (atShape pairs)
    (fun _ _ hb pair hp=>⟨(hcorrect.at_lattice hb pair hp).1,(hcorrect.at_lattice hb pair hp).2.1⟩)
  obtain ⟨k,theory,hk⟩ := ComparisonStructuralCoherence.run_complete hq
  exact ⟨max n k,pairs,theory,fun fuel hf=>
    ⟨hn fuel ((le_max_left _ _).trans hf),hk fuel ((le_max_right _ _).trans hf)⟩⟩

theorem prepared_compiled_subtype_iff {shapeFuel normFuel fuel : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {pairs : List Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hnorm : normalizeList normFuel (SchemePreparation.prepare [] source target) solved
      (declared (SchemePreparation.prepare [] source target))=.success pairs)
    {shape : ComparisonShape} {layout : Layout}
    (hbuild : build (ComparisonSelectedBases.inputNames (SchemePreparation.prepare [] source target))
      (ComparisonSelectedBases.inputModes (SchemePreparation.prepare [] source target))
      solved.fixedShapes shape=some layout)
    (hf : shape.subst solved.fixedShapes=shape)
    {theory : CNF} (htheory : ComparisonStructuralCoherence.run fuel
      (SchemePreparation.prepare [] source target).assumptions (atShape pairs) layout=.success theory)
    {a b : CompareTy} {left right : CNF}
    (ha : Representable (SchemePreparation.prepare [] source target).assumptions layout.shape a)
    (hb : Representable (SchemePreparation.prepare [] source target).assumptions layout.shape b)
    (hl : ComparisonLatticeCompiler.compile layout.basis a=some left)
    (hr : ComparisonLatticeCompiler.compile layout.basis b=some right) :
    AlgebraSubtype (SchemePreparation.prepare [] source target).assumptions a b ↔
      ∀world,CNFHolds world theory→
        CNFHolds (world ∘ basisAtom) left→ CNFHolds (world ∘ basisAtom) right :=
  compiled_subtype_iff hs hnorm (SchemePreparation.prepared_typeBoundsDefined source target)
    hbuild hf htheory ha hb hl hr

end ModalityInference.ComparisonStructuralTheory
