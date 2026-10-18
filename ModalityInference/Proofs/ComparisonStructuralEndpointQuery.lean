import ModalityInference.Proofs.ComparisonStructuralEndpoints
import ModalityInference.Proofs.ComparisonStructuralCoherence

/-! Actual endpoint normalization feeds the recursive coherent structural query
at one common budget, retaining whole bounds and genuine observer realizations. -/
namespace ModalityInference.ComparisonStructuralEndpoints
open ComparisonAlgebra ComparisonControls ComparisonStructuralBasis ComparisonStructuralLattice
open ComparisonShapeSolver ComparisonPreparation ComparisonWitnessRestriction

theorem NormalizedList.at_subtype {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy × CompareTy)}
    {pairs : List Pair} (h : NormalizedList p solved originals pairs)
    {shape : ComparisonShape} {pair : CompareTy × CompareTy} (hp : pair∈atShape pairs shape) :
    AlgebraSubtype p.assumptions pair.1 pair.2 := by
  obtain ⟨node,hn,_,rfl⟩ := atShape_origin hp
  obtain ⟨_,_,_,hsub⟩ := h.member hn
  exact hsub

theorem NormalizedList.layout_complete {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy × CompareTy)}
    {pairs : List Pair} (h : NormalizedList p solved originals pairs)
    {shapeFuel first : Nat} {v : TypeVar} {branch : ComparisonSelectedBases.Branch}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hb : branch∈ComparisonSelectedBases.prepared first p solved v) :
    ∃layout threshold output,
      ComparisonStructuralLayout.selected (ComparisonSelectedBases.inputNames p)
        (ComparisonSelectedBases.inputModes p) solved.fixedShapes branch=some layout ∧
      layout.shape=branch.shape ∧ layout.basis=branch.basis ∧
      (∀fuel≥threshold,ComparisonStructuralCoherence.run fuel p.assumptions (atShape pairs) layout=
        .success output) ∧
      ∀f : LatticeHom (Order p.assumptions layout.shape) Bool,
        ∃c η world,CNFHolds world output ∧
          ComparisonStructuralLayout.Realized p.assumptions
            (ComparisonStructuralLayout.labels p.assumptions (ComparisonSelectedBases.inputModes p))
            layout f c η world := by
  have heq : ∀v, ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ => (unify_factor (prepare_solved_iff.mp hs).1 hφ v).symm
  apply ComparisonStructuralCoherence.selected_run_complete hb heq (atShape pairs)
  · intro s b hbasis pair hp
    exact ⟨(h.at_lattice hbasis pair hp).1,(h.at_lattice hbasis pair hp).2.1⟩
  · intro s pair hp
    exact h.at_subtype hp

theorem prepared_layout_complete {shapeFuel first : Nat} {source target : Scheme}
    {action : CompareSubstitution} {solved : ComparisonShapeSolver.Solved} {v : TypeVar}
    {branch : ComparisonSelectedBases.Branch}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=
      .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) action)
    (hsp : Supported (SchemePreparation.prepare [] source target) action)
    (hb : branch∈ComparisonSelectedBases.prepared first (SchemePreparation.prepare [] source target) solved v) :
    let p := SchemePreparation.prepare [] source target
    ∃threshold pairs layout output,
      NormalizedList p solved (all p action) pairs ∧
      ComparisonStructuralLayout.selected (ComparisonSelectedBases.inputNames p)
        (ComparisonSelectedBases.inputModes p) solved.fixedShapes branch=some layout ∧
      layout.shape=branch.shape ∧ layout.basis=branch.basis ∧
      (∀fuel≥threshold,
        ComparisonShapeSolver.prepare fuel p=.success (.solved solved) ∧
        run fuel p solved action=.success pairs ∧
        ComparisonStructuralCoherence.run fuel p.assumptions (atShape pairs) layout=.success output) ∧
      ∀f : LatticeHom (Order p.assumptions layout.shape) Bool,
        ∃c η world,CNFHolds world output ∧
          ComparisonStructuralLayout.Realized p.assumptions
            (ComparisonStructuralLayout.labels p.assumptions (ComparisonSelectedBases.inputModes p))
            layout f c η world := by
  dsimp only
  obtain ⟨n,pairs,hpairs,hn⟩ := prepared_run_complete hs hw hsp
  obtain ⟨layout,k,output,hl,hshape,hbasis,hquery,hmodel⟩ := hn.layout_complete hs hb
  refine ⟨max shapeFuel (max n k),pairs,layout,output,hn,hl,hshape,hbasis,?_,hmodel⟩
  intro fuel hf
  have hnf : n≤fuel := (le_max_left n k).trans ((le_max_right shapeFuel _).trans hf)
  have hkf : k≤fuel := (le_max_right n k).trans ((le_max_right shapeFuel _).trans hf)
  exact ⟨prepare_solved_monotone ((le_max_left _ _).trans hf) hs,hpairs fuel hnf,hquery fuel hkf⟩

end ModalityInference.ComparisonStructuralEndpoints
