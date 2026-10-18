import ModalityInference.ComparisonPreparedDriver
import ModalityInference.Proofs.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonPreparedScalar
import ModalityInference.Proofs.ComparisonPreparedWitness
import ModalityInference.Proofs.ComparisonPreparedModeSupport
import ModalityInference.Proofs.ComparisonPreparedQuerySupport

namespace ModalityInference.ComparisonPreparedDriver

abbrev queryInput (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :=
  ComparisonSignedBranchImages.input (ComparisonSignedBranchImages.entries first p solved)

abbrev shapeWorld (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (sources : List ComparisonGuardedEndpointQueries.Source)
    (result : ComparisonSignedQuerySolver.Solution) :=
  ComparisonGuardedEndpointQueries.shapeValue (fun n=>((queryInput first p solved).bases n).length)
    sources (CNFPropagation.valuation result.selectors)

abbrev modeWitness (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (sources : List ComparisonGuardedEndpointQueries.Source)
    (result : ComparisonSignedQuerySolver.Solution) :=
  ComparisonGuardedEndpointQueries.modes ModalSynthesis.locality
    (ComparisonPreparedScalar.flexibleAtoms p) (queryInput first p solved) sources
    (CNFPropagation.valuation result.selectors)

structure Execution (fuel first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (output : CompareSubstitution) where
  program : ComparisonPreparedQueries.Program
  scalar : ComparisonGuardedEndpointQueries.Source
  solution : ComparisonSignedQuerySolver.Solution
  action : Substitution
  compiled : ComparisonPreparedQueries.compile fuel first p solved=.success program
  scalar_compiled : ComparisonPreparedScalar.run fuel p=.success scalar
  queried : ComparisonGuardedEndpointQueries.run fuel (queryInput first p solved)
    ModalSynthesis.locality (ComparisonPreparedScalar.flexibleAtoms p)
    (program.sources++[scalar]) program.condition=.success solution
  assembled : ComparisonPreparedScalar.assemble p
    (modeWitness first p solved (program.sources++[scalar]) solution)=some action
  selected : ComparisonSignedBranchImages.select first p solved
    (shapeWorld first p solved (program.sources++[scalar]) solution) solution.images action.modes=some output

private theorem bind_success {α β : Type} {r : RunResult α} {f : α → RunResult β} {b : β}
    (h : r.bind f=.success b) : ∃a,r=.success a ∧ f a=.success b := by
  cases r <;> simp_all [RunResult.bind]

theorem propagate_spec {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (h : propagate fuel first p solved=.success output) :
    Nonempty (Execution fuel first p solved output) := by
  obtain ⟨program,hp,h⟩ := bind_success h
  obtain ⟨scalar,hs,h⟩ := bind_success h
  obtain ⟨solution,hq,h⟩ := bind_success h
  cases ha : ComparisonPreparedScalar.assemble p
    (modeWitness first p solved (program.sources++[scalar]) solution) with
  | none => simp only [ha] at h; contradiction
  | some action =>
      simp only [ha] at h
      cases ht : ComparisonSignedBranchImages.select first p solved
        (shapeWorld first p solved (program.sources++[scalar]) solution) solution.images action.modes with
      | none => simp only [ht] at h; contradiction
      | some result =>
          simp only [ht,RunResult.success.injEq] at h
          subst result
          exact ⟨⟨program,scalar,solution,action,hp,hs,hq,ha,ht⟩⟩

theorem Execution.allowed {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (e : Execution fuel first p solved output) :
    ∀source∈e.program.sources++[e.scalar],source.Allowed (queryInput first p solved).keys := by
  intro source hs
  rcases List.mem_append.mp hs with hs|hs
  · exact ComparisonPreparedQueries.compile_allowed e.compiled source hs
  · have he : source=e.scalar := by simpa using hs
    subst source
    exact ComparisonPreparedScalar.run_allowed e.scalar_compiled _

theorem Execution.binary {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (e : Execution fuel first p solved output) :
    ∀source∈e.program.sources++[e.scalar],source.Binary := by
  intro source hs
  rcases List.mem_append.mp hs with hs|hs
  · exact ComparisonPreparedQueries.compile_binary e.compiled source hs
  · have he : source=e.scalar := by simpa using hs
    subst source
    exact ComparisonPreparedScalar.run_binary e.scalar_compiled

theorem Execution.prepared_of_support {shapeFuel fuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (e : Execution fuel first (SchemePreparation.prepare [] source target) solved output)
    (hmodeSupport : ∀v∈ComparisonSelectedBases.inputModes (SchemePreparation.prepare [] source target),
      ∀w∈(e.action.mode v).vars,w∈ComparisonSelectedBases.inputModes (SchemePreparation.prepare [] source target)) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) output := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨queries,r,_,_,hr,_,hcondition,_,hvalid⟩ :=
    ComparisonGuardedEndpointQueries.run_sound e.allowed e.queried
  have hform:=(ComparisonPreparedQueries.compile_condition e.compiled _).mp hcondition
  have hanchor:=(ComparisonSelectedBases.selectorFormula_eval first p solved _).mp hform.1 |>.1
  have htheory:=((ComparisonSelectedBases.layout first p solved).matchTheory_correct solved.fixedShapes
    (ComparisonSelectedBases.anchorEquations p solved) _
      (ComparisonSelectedBases.anchorEquations_scope first p solved)).mp hanchor |>.1
  have hscalar:=hvalid e.scalar (List.mem_append_right _ List.mem_cons_self)
  have hfixed : ComparisonModeRestriction.Fixed p.assumptions e.action.mode :=
    ComparisonPreparedScalar.assemble_fixed_prepared e.assembled
  have hmode : output.mode=e.action.mode := ComparisonSignedBranchImages.select_mode e.selected
  have hguards:=ComparisonPreparedScalar.assembled_entails e.scalar_compiled e.assembled hscalar
  apply ComparisonPreparedWitness.selected_assembled hs htheory hr e.assembled e.selected
    e.scalar_compiled hscalar
  intro pair hpair
  obtain ⟨a,ham,hap,hactive,hguard,hb,hbranch⟩ :=
    ComparisonPreparedQueries.compile_active_endpoint e.compiled hcondition hpair
  obtain ⟨_,_,_,hbuild,htheory,hcompile,hremap⟩ := ComparisonPreparedQueries.branch_spec hbranch
  have hp : pair∈ComparisonSignedObservation.endpoints p := List.mem_append_right _ hpair
  have hg : ∀t∈[pair.1,pair.2],∀m∈ComparisonAnnotations.expressions t,
      Entails p.assumptions (.defined (m.subst output.mode)) := by
    rw [hmode]
    exact ComparisonPreparedScalar.endpoint_guards hguards hp
  have hv := hvalid a.source (List.mem_append_left _ ham)
  have hv' : ComparisonSignedStrategySynthesis.Valid
      (fun n=>((queryInput first p solved).bases n).length)
      ComparisonLayoutWorlds.decode a.theory a.clauses
      ((queryInput first p solved).imageValue r (CNFPropagation.valuation e.solution.selectors))
      (SchemeModeSynthesis.strategy output.mode) := by
    rw [hmode,ComparisonPreparedScalar.assemble_strategy e.assembled]
    exact hv ((ComparisonPreparedQueries.Alternative.active_iff a _).mpr hactive)
  exact ComparisonPreparedQueryAlignment.active_endpoint_sound hs hanchor hr hfixed hmodeSupport
    e.selected hp hg hb hguard hbuild (ComparisonPreparedQueries.compile_spec e.compiled).1
    (SchemePreparation.prepared_typeBoundsDefined source target) htheory hcompile hremap hv'

theorem propagate_of_solved {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : ComparisonPreparedQueries.Program}
    (hp : ComparisonPreparedQueries.compile fuel first p solved=.success program)
    {scalar : ComparisonGuardedEndpointQueries.Source}
    (hs : ComparisonPreparedScalar.run fuel p=.success scalar)
    {result : ComparisonSignedQuerySolver.Solution}
    (hq : ComparisonGuardedEndpointQueries.run fuel (queryInput first p solved)
      ModalSynthesis.locality (ComparisonPreparedScalar.flexibleAtoms p)
      (program.sources++[scalar]) program.condition=.success result) :
    ∃output,propagate fuel first p solved=.success output := by
  have ha : ∀source∈program.sources++[scalar],source.Allowed (queryInput first p solved).keys := by
    intro source hsource
    rcases List.mem_append.mp hsource with hsource|hsource
    · exact ComparisonPreparedQueries.compile_allowed hp source hsource
    · have he : source=scalar := by simpa using hsource
      subst source
      exact ComparisonPreparedScalar.run_allowed hs _
  obtain ⟨_,_,_,_,_,hkeys,hcondition,_,_⟩ := ComparisonGuardedEndpointQueries.run_sound ha hq
  have hcoverage := (ComparisonSelectedBases.selectorFormula_eval first p solved _).mp
    ((ComparisonPreparedQueries.compile_condition hp _).mp hcondition).1 |>.2
  obtain ⟨action,hact⟩ := ComparisonPreparedScalar.modes_assemble p (queryInput first p solved)
    (program.sources++[scalar]) (CNFPropagation.valuation result.selectors)
  obtain ⟨output,hout⟩ := ComparisonSignedBranchImages.select_complete action.modes hkeys
    (fun name hn=>hcoverage (.flex name) ((ComparisonSelectedBases.mem_inputTypeKeys p name).mp hn).1)
  refine ⟨output,?_⟩
  simp only [propagate,hp,hs,hq,bind,RunResult.bind,hact,hout]

theorem reconstruct_result {ambient : Bounds} {source target : Scheme} {action : CompareSubstitution}
    (h : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) action) :
    let p:=SchemePreparation.prepare ambient source target
    let result:=ComparisonPreparation.reconstruct p action
    CompareInstantiatesUnder p.assumptions source result ∧ result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  let p:=SchemePreparation.prepare ambient source target
  have htypes : ∀v∈source.body.typeVars ∪ source.bounds.typeVars,action.type v=.var v := by
    intro v hv
    apply h.1.1.type_fixed
    apply SchemePreparation.original_type_lt_first
    have hv':=Finset.mem_union.mp hv
    simp only [SchemePreparation.originalTypeIds,List.mem_append,
      TypeExpr.mem_typeVariables,Bounds.mem_typeVariables]
    tauto
  have hmodes : ∀v∈source.body.modVars ∪ source.bounds.modVars,action.mode v=.var v := by
    intro v hv
    apply h.1.1.mode_fixed
    apply SchemePreparation.original_mode_lt_first
    have hv':=Finset.mem_union.mp hv
    simp only [SchemePreparation.originalModeIds,List.mem_append,
      TypeExpr.mem_modeVariables,Bounds.mem_modeVariables]
    tauto
  have he:=ComparisonPreparation.reconstruct_ty p action source.body
    (fun v hv=>htypes v (Finset.mem_union_left _ hv))
    (fun v hv=>hmodes v (Finset.mem_union_left _ hv))
  exact ⟨⟨ComparisonPreparation.reconstruct_instantiates ambient source target action,
      ComparisonPreparation.reconstruct_wellFormedUnder h.2.1,he.symm ▸ h.2.2⟩,
    ComparisonPreparation.reconstruct_wellShaped h.1.2.1,
    (ComparisonPreparation.reconstruct_algebra_bounds p action source.bounds p.assumptions
      (fun v hv=>htypes v (Finset.mem_union_right _ hv))
      (fun v hv=>hmodes v (Finset.mem_union_right _ hv))).mpr h.1.2.2.1,
    he.symm ▸ h.1.2.2.2⟩

theorem run_spec {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target=.success result) :
    let p:=SchemePreparation.prepare [] source.requireDefinedInstances target
    ∃solved action,ComparisonShapeSolver.prepare fuel p=.success (.solved solved) ∧
      propagate fuel 0 p solved=.success action ∧ result=ComparisonPreparation.reconstruct p action := by
  unfold run at h
  split at h
  · cases h
  · dsimp only [bind,pure,RunResult.bind] at h
    obtain ⟨_,_,h⟩ := bind_success h
    obtain ⟨shapes,hs,hrest⟩ := bind_success h
    cases shapes with
    | infeasibleAssumptions => cases hrest
    | solved solved =>
        obtain ⟨action,ha,he⟩ := bind_success hrest
        exact ⟨solved,action,hs,ha,by simpa [pure] using he.symm⟩

/-- Every successfully assembled result discharges all original comparisons
and definedness guards under the original declared bounds. -/
theorem Execution.prepared {shapeFuel fuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (e : Execution fuel first (SchemePreparation.prepare [] source target) solved output) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) output := by
  apply e.prepared_of_support hs
  apply ComparisonGuardedEndpointQueries.assembled_inputModes e.assembled
  intro source hsource
  rcases List.mem_append.mp hsource with hsource|hsource
  · exact ComparisonPreparedQueries.compile_scalar_supported e.compiled _ source hsource
  · have he : source=e.scalar := by simpa using hsource
    subst source
    exact ComparisonPreparedScalar.run_scalar_supported e.scalar_compiled _

theorem propagate_sound {shapeFuel fuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (h : propagate fuel first (SchemePreparation.prepare [] source target) solved=.success output) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) output := by
  obtain ⟨e⟩ := propagate_spec h
  exact e.prepared hs

/-- The exact returned substitution has the public quantified domain, defined
images and body, and proves the original source constraints and comparison. -/
theorem run_result {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target=.success result) :
    let p:=SchemePreparation.prepare [] source target
    CompareInstantiatesUnder p.assumptions source result ∧ result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨solved,action,hs,ha,rfl⟩ := run_spec h
  have hw:=reconstruct_result (propagate_sound hs ha)
  let p:=SchemePreparation.prepare [] source.requireDefinedInstances target
  let result:=ComparisonPreparation.reconstruct p action
  have hi : CompareInstantiatesUnder p.assumptions source result := ⟨hw.1.domain,hw.1.images,hw.1.body⟩
  have hb : AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.instanceGuards) := by
    simpa only [Scheme.requireDefinedInstances,CompareSubstitution.bounds,
      List.map_append,AlgebraEntailsAll,List.mem_append,or_imp,forall_and] using hw.2.2.1
  have he : p.assumptions=(SchemePreparation.prepare [] source target).assumptions := by
    simp only [p,SchemePreparation.prepare_assumptions,Scheme.requireDefinedInstances_subsumptionIndices]
  have ht : p.targetType=(SchemePreparation.prepare [] source target).targetType := by
    simp only [p,SchemePreparation.prepare,Scheme.requireDefinedInstances_subsumptionIndices]
  have hbody : AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := hw.2.2.2
  exact ⟨he ▸ hi,he ▸ hw.2.1,he ▸ hb.1,by simpa only [he,ht] using hbody⟩

theorem run_algebra_subsumesUnder {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target=.success result) : AlgebraSubsumesUnder [] source target := by
  obtain ⟨hi,hs,hb,ht⟩ := run_result h
  exact ⟨result,hi.domain,hs,hi.images,hi.body,hb,ht⟩

end ModalityInference.ComparisonPreparedDriver
