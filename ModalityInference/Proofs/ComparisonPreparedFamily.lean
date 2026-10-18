import ModalityInference.Proofs.ComparisonClosedBranchWitness
import ModalityInference.Proofs.ComparisonSignedCallCoverage
import ModalityInference.Proofs.ComparisonReifiedEndpointTheory

/-! One admissible type assignment determines polynomials for every structural
branch key. Unused shape alternatives receive a basis generator; enabled
alternatives retain the original image under all lattice observers. -/
namespace ModalityInference.ComparisonPreparedFamily
open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonSignedSynthesis
  ComparisonSelectedBases ComparisonSignedBranchImages ComparisonSignedEndpoints
  ComparisonSignedObservation ComparisonStructuralLayout

def clauses (table : List Entry) (σ : CompareSubstitution) (key : Nat) : CNF :=
  ((table[key]?).bind fun entry=>
    ComparisonLatticeCompiler.compile entry.2.basis (σ.type (.flex entry.1))).getD [[(0,true)]]

def images (table : List Entry) (σ : CompareSubstitution) : Nat→(Nat→Bool)→Bool :=
  fun key=>polynomialValue (clauses table σ key)

theorem clauses_polynomial {table : List Entry} (σ : CompareSubstitution)
    {key : Nat} {entry : Entry} (h : table[key]?=some entry) :
    Polynomial entry.2.basis (clauses table σ key) := by
  unfold clauses
  rw [h,Option.bind_some]
  cases hc : ComparisonLatticeCompiler.compile entry.2.basis (σ.type (.flex entry.1)) with
  | some cs => exact (ComparisonLatticeCompiler.compile_polynomial hc).2
  | none =>
    apply Polynomial.atom
    simp [Basis.types,Basis.keys,Basis.heads]

theorem family (table : List Entry) (σ : CompareSubstitution) : Family (input table) (images table σ) := by
  apply polynomial_family
  all_goals intro key hk
  all_goals have hk' : key<table.length := List.mem_range.mp hk
  all_goals have hh := clauses_polynomial σ (List.getElem?_eq_getElem hk')
  · exact hh.positive
  · simpa only [input,List.getElem?_eq_getElem hk',Option.map_some,Option.getD_some] using hh.supported
  · exact hh.zero
  · exact hh.one

theorem locate_compile {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {name key : Nat} {branch : ComparisonSelectedBases.Branch}
    (hb : branch∈prepared first p solved (.flex name))
    (hk : locate name branch.shape (entries first p solved)=some key)
    {σ : CompareSubstitution} {cs : CNF}
    (hc : ComparisonLatticeCompiler.compile branch.basis (σ.type (.flex name))=some cs) :
    clauses (entries first p solved) σ key=cs := by
  obtain ⟨entry,he,hn,hs⟩ := locate_spec hk
  have hbentry := entry_basis (List.mem_of_getElem? he)
  obtain ⟨_,_,_,_,hbbranch⟩ := bases_origin hb
  rw [hs,hbbranch] at hbentry
  have hbe := Option.some.inj hbentry
  simp [clauses,he,hn,←hbe,hc]


theorem witness_site {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution} {world : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hp : BranchPolynomials first p solved world σ)
    {layout : Layout} (hb : Based (inputNames p) (inputModes p) solved.fixedShapes layout)
    (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {call : Call} (hc : ComparisonSignedCallCoverage.Site p.assumptions (inputTypeKeys p) σ layout call) :
    ∃node key cs, nodeAt layout call.route=some node ∧
      ComparisonSignedBranchCalls.resolve (entries first p solved) layout call=some ⟨key,call.route⟩ ∧
      ComparisonLatticeCompiler.compile node.basis (σ.type (.flex call.name))=some cs ∧
      clauses (entries first p solved) σ key=cs ∧
      (input (entries first p solved)).bases key=node.basis.types := by
  obtain ⟨node,hn,hname,hrep⟩ := hc
  have hv := (mem_inputTypeKeys p call.name).mp hname |>.1
  obtain ⟨branch,hbranch,cs,t,hg,hcompile,_,_,ht,he⟩ := hp.2 _ hv
  have hmodel := ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  have hfix : branch.shape.subst solved.fixedShapes=branch.shape := by
    obtain ⟨raw,_,he,_,_⟩ := bases_origin hbranch
    rw [he]
    exact ComparisonShapeRetraction.fixedShapes_idempotent hs _
  have hshape : (σ.type (.flex call.name)).shape.subst solved.fixedShapes=branch.shape :=
    ((he.2.shape_equivalent.trans ht.2.2) solved.fixedShapes hmodel).trans hfix
  have hnode : node.shape=branch.shape :=
    ((hrep.2.2 solved.fixedShapes hmodel).trans (nodeAt_fixed hf hn)).symm.trans hshape
  obtain ⟨key,hkey⟩ := locate_prepared hname hbranch
  have hbas := (nodeAt_based hb hn).basis
  obtain ⟨_,_,_,_,hbranchBasis⟩ := bases_origin hbranch
  rw [hnode,hbranchBasis] at hbas
  have hbe : branch.basis=node.basis := Option.some.inj hbas
  refine ⟨node,key,cs,hn,?_,hbe ▸ hcompile,locate_compile hbranch hkey hcompile,?_⟩
  · simp [ComparisonSignedBranchCalls.resolve,hn,hnode,hkey]
  · rw [locate_basis hbranch hkey,hbe]


theorem trace_reads {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution} {world : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hp : BranchPolynomials first p solved world σ)
    {layout : Layout} (hb : Based (inputNames p) (inputModes p) solved.fixedShapes layout)
    (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    (observation : Nat→Bool) :
    ComparisonStructuralTrace.Reads (Δ:=p.assumptions) (inputModes p) (inputTypeKeys p) σ layout observation
      (ComparisonSignedBranchCalls.pullback (entries first p solved) layout
        (ComparisonSignedPoints.basisImages (fun n=>((input (entries first p solved)).bases n).length)
          (images (entries first p solved) σ) observation)) := by
  intro route node hn child ht name hname hrep
  obtain ⟨node',key,cs,hn',hresolve,hcompile,hclauses,hbasis⟩ :=
    witness_site hs hp hb hf (call:=⟨name,route⟩) ⟨node,hn,hname,hrep⟩
  have he : node'=node := Option.some.inj (hn'.symm.trans hn)
  subst node'
  obtain ⟨model,rfl⟩ := ht.realizes
  rw [ComparisonSignedBranchCalls.pullback,hresolve]
  simp only [Option.map_some,Option.getD_some,ComparisonSignedPoints.basisImages,images,hclauses]
  apply Bool.eq_iff_iff.mpr
  rw [polynomialValue_correct]
  refine (CNFPropagation.holds_congr ?_).trans
    (ComparisonStructuralNode.compiled_value hcompile (booleanValue model.child.observer)
      (booleanValue_join _) (booleanValue_meet _) model.types)
  intro i hi
  have hir := List.mem_range.mp ((ComparisonLatticeCompiler.compile_polynomial hcompile).2.supported i hi)
  simp only [ComparisonSignedPoints.basisPoint,hbasis,hir,if_true,Function.comp_apply]

theorem compile_complete {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution} {world : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hp : BranchPolynomials first p solved world σ)
    {layout : Layout} (hb : Based (inputNames p) (inputModes p) solved.fixedShapes layout)
    (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {labels : List (GuardedMode p.assumptions)} {left right : Ty}
    (hl : Endpoint p.assumptions labels (inputTypeKeys p) σ layout left)
    (hr : Endpoint p.assumptions labels (inputTypeKeys p) σ layout right)
    {fuel : Nat} {ctx : ComparisonSignedEndpoints.Context} {output : List CompiledClause}
    (hc : compileGuards fuel (ComparisonSignedEndpoints.compile (inputTypeKeys p) ctx left right)=.success output) :
    ∃mapped,ComparisonSignedBranchCalls.compile (entries first p solved) layout output=some mapped := by
  apply ComparisonSignedBranchCalls.compile_complete
  intro c hcm literal hli
  obtain ⟨node,key,cs,_,he,_⟩ := witness_site hs hp hb hf
    (ComparisonSignedCallCoverage.compiled_sites hl hr hc hcm hli)
  exact ⟨_,he⟩

end ModalityInference.ComparisonPreparedFamily
