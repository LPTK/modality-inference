import ModalityInference.Proofs.ComparisonPreparedQuerySupport
import ModalityInference.Proofs.ComparisonStructuralTheory
import ModalityInference.Proofs.ComparisonPreparedFamily

namespace ModalityInference.ComparisonPreparedQueries
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout ComparisonAlgebra
  ComparisonControls ComparisonSelectedBases ComparisonPreparation ComparisonWitnessRestriction

/-- Branch construction always finishes; unsuccessful alternatives are retained
as absence, while all Boolean conversions use their ordinary complete compiler. -/
theorem branch_complete (first activation : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoint : Ty × Ty) (b : ComparisonSelectedBases.Branch) :
    ∃threshold output,∀fuel≥threshold,
      branch fuel first activation p solved declared endpoint b=.success output := by
  cases hl : selected (inputNames p) (ComparisonSelectedBases.inputModes p) solved.fixedShapes b with
  | none => exact ⟨0,none,by intro fuel _;simp [branch,hl]⟩
  | some layout =>
    cases hq : query p.assumptions (ComparisonStructuralEndpoints.atShape declared) layout with
    | none => exact ⟨0,none,by intro fuel _;simp [branch,hl,ComparisonStructuralCoherence.run,hq]⟩
    | some q =>
      obtain ⟨n,theory,ht⟩:=ComparisonStructuralCoherence.run_complete hq
      obtain ⟨k,original,hc⟩:=compileGuards_complete
        (ComparisonSignedEndpoints.compile (inputTypeKeys p) (context layout ModExpr.var) endpoint.1 endpoint.2)
      let output:= (ComparisonSignedBranchCalls.compile (ComparisonSignedBranchImages.entries first p solved)
        layout original).map fun clauses=>
          (⟨activation,b,endpoint,layout,theory,original,clauses⟩ : Alternative)
      refine ⟨max n k,output,?_⟩
      intro fuel hf
      simp only [branch,hl,ht fuel ((le_max_left _ _).trans hf),hc fuel ((le_max_right _ _).trans hf),
        bind,pure,RunResult.bind]
      dsimp only [output]
      cases ComparisonSignedBranchCalls.compile (ComparisonSignedBranchImages.entries first p solved)
        layout original <;> rfl

/-- Every branch family has one fuel-independent, completed compiled list. -/
theorem alternatives_complete (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoint : Ty × Ty) (bs : List ComparisonSelectedBases.Branch) (next : Nat) :
    ∃threshold output,∀fuel≥threshold,
      alternatives fuel first p solved declared endpoint next bs=.success output := by
  induction bs generalizing next with
  | nil => exact ⟨0,[],by intro fuel _;rfl⟩
  | cons b bs ih =>
    obtain ⟨n,head,hh⟩:=branch_complete first next p solved declared endpoint b
    obtain ⟨k,tail,ht⟩:=ih (next+1)
    refine ⟨max n k,head.toList++tail,?_⟩
    intro fuel hf
    simp [alternatives,hh fuel ((le_max_left _ _).trans hf),ht fuel ((le_max_right _ _).trans hf),
      bind,pure,RunResult.bind]



theorem inputAction_polynomials {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder p σ) (hp : BranchPolynomials first p solved world σ) :
    BranchPolynomials first p solved world (inputAction p σ) := by
  refine ⟨hp.1,?_⟩
  intro v hv
  simpa only [inputAction_type hw.1.1 hv] using hp.2 v hv


theorem endpoint_selected {shapeFuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    {endpoint : Ty×Ty} (he : endpoint∈endpoints (SchemePreparation.prepare [] source target)) :
    let p:=SchemePreparation.prepare [] source target
    ∃b∈branches first p solved endpoint,∃layout labels,
      b.guard.eval world=true ∧ selected (inputNames p) (ComparisonSelectedBases.inputModes p)
        solved.fixedShapes b=some layout ∧
      Based (inputNames p) (ComparisonSelectedBases.inputModes p) solved.fixedShapes layout ∧
      layout.shape.subst solved.fixedShapes=layout.shape ∧
      Endpoint p.assumptions labels (inputTypeKeys p) (inputAction p σ) layout endpoint.1 ∧
      Endpoint p.assumptions labels (inputTypeKeys p) (inputAction p σ) layout endpoint.2 := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨layout,labels,hbuild,hshape,hbased,hl,hr,_⟩:=prepared_alignment hs hw hsp he
  have hn : ∀v∈endpoint.1.typeVars,v∈inputNames p :=
    fun v hv=>(mem_inputNames p v).mpr ((endpoints_input he).1 hv)
  have hscope : ∀v∈((ComparisonShape.ofTy endpoint.1).subst solved.resolveAll).vars,
      v∈(ComparisonSelectedBases.layout first p solved).parameters := fun _=>template_scope hn
  obtain ⟨raw,hraw,hguard,hrawshape⟩:=(ComparisonShapeSelectors.Layout.branches_decoded hp.1
    ((ComparisonShape.ofTy endpoint.1).subst solved.resolveAll) hscope).2
  have hsame : raw.shape.subst solved.fixedShapes=layout.shape := by
    rw [hrawshape,←(inputAction_polynomials hw hp).ty_shape hs endpoint.1 hn,←hshape]
  have hb : ComparisonStructuralBasis.basis (inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes (raw.shape.subst solved.fixedShapes)=some layout.basis := by
    rw [hsame]
    exact hbased.basis
  refine ⟨⟨raw.shape.subst solved.fixedShapes,raw.guard,layout.basis⟩,
    bases_insert hraw hb,layout,labels,hguard,?_,hbased,?_,hl,hr⟩
  · change build _ _ _ (raw.shape.subst solved.fixedShapes)=some layout
    rw [hsame,hshape]
    exact hbuild
  · rw [hshape]
    exact ComparisonShapeRetraction.fixedShapes_idempotent hs _


theorem endpoint_branch_complete {shapeFuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    {declared : List ComparisonStructuralEndpoints.Pair}
    (hd : ComparisonStructuralEndpoints.NormalizedList (SchemePreparation.prepare [] source target) solved
      (ComparisonStructuralEndpoints.declared (SchemePreparation.prepare [] source target)) declared)
    {endpoint : Ty×Ty} (he : endpoint∈endpoints (SchemePreparation.prepare [] source target)) :
    let p:=SchemePreparation.prepare [] source target
    ∃threshold b,b∈branches first p solved endpoint ∧ b.guard.eval world=true ∧
      ∀fuel≥threshold,∀activation,∃a,
        branch fuel first activation p solved declared endpoint b=.success (some a) := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨b,hb,layout,labels,hguard,hbuild,hbased,hfixed,hl,hr⟩:=endpoint_selected hs hw hsp hp he
  obtain ⟨q,hq⟩:=hbased.query_complete p.assumptions (ComparisonStructuralEndpoints.atShape declared)
    (fun _ _ hbas pair hpair=>⟨(hd.at_lattice hbas pair hpair).1,(hd.at_lattice hbas pair hpair).2.1⟩)
  obtain ⟨n,theory,ht⟩:=ComparisonStructuralCoherence.run_complete hq
  obtain ⟨k,original,hc⟩:=compileGuards_complete
    (ComparisonSignedEndpoints.compile (inputTypeKeys p) (context layout ModExpr.var) endpoint.1 endpoint.2)
  obtain ⟨clauses,hclauses⟩:=ComparisonPreparedFamily.compile_complete hs
    (inputAction_polynomials hw hp) hbased hfixed hl hr (hc k le_rfl)
  refine ⟨max n k,b,hb,hguard,?_⟩
  intro fuel hf activation
  dsimp only [p] at ht hc
  refine ⟨⟨activation,b,endpoint,layout,theory,original,clauses⟩,?_⟩
  simp only [branch,hbuild,ht fuel ((le_max_left _ _).trans hf),hc fuel ((le_max_right _ _).trans hf),
    hclauses,bind,pure,RunResult.bind]


private theorem get_success {α β : Type} {r : RunResult α} {f : α→RunResult β} {b : β}
    (h : r.bind f=.success b) : ∃a,r=.success a ∧ f a=.success b := by
  cases r <;> simp_all [RunResult.bind]

theorem alternatives_contains {fuel first next : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty×Ty} {bs : List ComparisonSelectedBases.Branch} {output : List Alternative}
    (h : alternatives fuel first p solved declared endpoint next bs=.success output)
    {b : ComparisonSelectedBases.Branch} (hb : b∈bs)
    (hs : ∀activation,∃a,branch fuel first activation p solved declared endpoint b=.success (some a)) :
    ∃a∈output,a.branch=b := by
  induction bs generalizing next output with
  | nil => cases hb
  | cons c cs ih =>
    obtain ⟨head,hhead,hrest⟩:=get_success h
    obtain ⟨tail,htail,he⟩:=get_success hrest
    have hout : output=head.toList++tail := by simpa only [pure,RunResult.success.injEq] using he.symm
    subst output
    rcases List.mem_cons.mp hb with rfl|hb
    · obtain ⟨a,ha⟩:=hs next
      have heq : head=some a:=RunResult.success.inj (hhead.symm.trans ha)
      exact ⟨a,by simp [heq],(branch_spec ha).2.1⟩
    · obtain ⟨a,ha,he⟩:=ih htail hb
      exact ⟨a,List.mem_append_right _ ha,he⟩

theorem groups_complete (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoints : List (Ty×Ty)) (next : Nat) :
    ∃threshold output,∀fuel≥threshold,groups fuel first p solved declared next endpoints=.success output := by
  induction endpoints generalizing next with
  | nil => exact ⟨0,[],by intro fuel _;rfl⟩
  | cons endpoint endpoints ih =>
    obtain ⟨n,choices,hc⟩:=alternatives_complete first p solved declared endpoint
      (branches first p solved endpoint) next
    obtain ⟨k,tail,ht⟩:=ih (next+(branches first p solved endpoint).length)
    refine ⟨max n k,⟨endpoint,choices⟩::tail,?_⟩
    intro fuel hf
    simp [groups,hc fuel ((le_max_left _ _).trans hf),ht fuel ((le_max_right _ _).trans hf),
      bind,pure,RunResult.bind]

theorem groups_covered {fuel first next : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoints : List (Ty×Ty)} {output : List Group} {world : Nat→Bool}
    (h : groups fuel first p solved declared next endpoints=.success output)
    (hc : ∀endpoint∈endpoints,∃b∈branches first p solved endpoint,b.guard.eval world=true ∧
      ∀activation,∃a,branch fuel first activation p solved declared endpoint b=.success (some a)) :
    ∀g∈output,∃a∈g.alternatives,a.branch.guard.eval world=true := by
  induction endpoints generalizing next output with
  | nil => have he : output=[]:=by simpa [groups] using h.symm
           subst output; simp
  | cons endpoint endpoints ih =>
    obtain ⟨choices,hchoices,hrest⟩:=get_success h
    obtain ⟨tail,htail,he⟩:=get_success hrest
    have hout : output=⟨endpoint,choices⟩::tail:=by simpa only [pure,RunResult.success.injEq] using he.symm
    subst output
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · obtain ⟨b,hb,hguard,hbranch⟩:=hc endpoint List.mem_cons_self
      obtain ⟨a,ha,he⟩:=alternatives_contains hchoices hb hbranch
      exact ⟨a,ha,he ▸ hguard⟩
    · exact ih htail (fun e he=>hc e (List.mem_cons_of_mem _ he)) g hg


theorem endpoints_branches_complete {shapeFuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    {declared : List ComparisonStructuralEndpoints.Pair}
    (hd : ComparisonStructuralEndpoints.NormalizedList (SchemePreparation.prepare [] source target) solved
      (ComparisonStructuralEndpoints.declared (SchemePreparation.prepare [] source target)) declared)
    (pairs : List (Ty×Ty)) (he : ∀endpoint∈pairs,endpoint∈endpoints (SchemePreparation.prepare [] source target)) :
    let p:=SchemePreparation.prepare [] source target
    ∃threshold,∀fuel≥threshold,∀endpoint∈pairs,
      ∃b∈branches first p solved endpoint,b.guard.eval world=true ∧
        ∀activation,∃a,branch fuel first activation p solved declared endpoint b=.success (some a) := by
  induction pairs with
  | nil => exact ⟨0,by simp⟩
  | cons endpoint pairs ih =>
    obtain ⟨n,b,hb,hguard,hbcomplete⟩:=endpoint_branch_complete hs hw hsp hp hd (he endpoint List.mem_cons_self)
    obtain ⟨k,hrest⟩:=ih (fun endpoint hm=>he endpoint (List.mem_cons_of_mem _ hm))
    refine ⟨max n k,?_⟩
    intro fuel hf pair hpair
    rcases List.mem_cons.mp hpair with rfl|hpair
    · exact ⟨b,hb,hguard,hbcomplete fuel ((le_max_left _ _).trans hf)⟩
    · exact hrest fuel ((le_max_right _ _).trans hf) pair hpair

/-- The actual prepared compiler retains an enabled successful alternative for
all source bounds and the body, under the witness's one shared shape valuation. -/
theorem compile_complete_covered {shapeFuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ) :
    let p:=SchemePreparation.prepare [] source target
    ∃threshold program,(∀fuel≥threshold,compile fuel first p solved=.success program) ∧
      ∀g∈program.groups,∃a∈g.alternatives,a.branch.guard.eval world=true := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨n,declared,hn,hd⟩:=ComparisonStructuralEndpoints.normalizeList_complete hs
    (ComparisonStructuralEndpoints.declared p)
    (ComparisonStructuralEndpoints.declared_guarded p (SchemePreparation.prepared_typeBoundsDefined source target))
  change ∀fuel≥n,ComparisonStructuralEndpoints.normalizeList fuel p solved
    (ComparisonStructuralEndpoints.declared p)=.success declared at hn
  obtain ⟨k,gs,hg⟩:=groups_complete first p solved declared (sourceEndpoints p)
    (ComparisonSelectedBases.layout first p solved).next
  obtain ⟨m,hb⟩:=endpoints_branches_complete hs hw hsp hp hd (sourceEndpoints p)
    (fun _ he=>List.mem_append_right _ he)
  obtain ⟨j,condition,hc⟩:=CompactCNF.toCNF_complete
    (.and (selectorFormula first p solved) (.all (gs.map Group.formula))) true
  let threshold:=max (max n k) (max m j)
  have hng : n≤threshold:=le_trans (le_max_left _ _) (le_max_left _ _)
  have hkg : k≤threshold:=le_trans (le_max_right _ _) (le_max_left _ _)
  have hmg : m≤threshold:=le_trans (le_max_left _ _) (le_max_right _ _)
  have hjg : j≤threshold:=le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨threshold,⟨declared,gs,condition⟩,?_,?_⟩
  · intro fuel hf
    change compile fuel first p solved=.success _
    simp only [compile,hn fuel (hng.trans hf),hg fuel (hkg.trans hf),hc fuel (hjg.trans hf),
      bind,pure,RunResult.bind]
  · exact groups_covered (hg threshold hkg) (hb threshold hmg)

end ModalityInference.ComparisonPreparedQueries
