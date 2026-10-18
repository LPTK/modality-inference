import ModalityInference.ComparisonAmbientDriver
import ModalityInference.Proofs.ComparisonPreparedAmbientGuards
import ModalityInference.Proofs.ComparisonPreparedDriverTermination

/-! Successful ambient comparison establishes its own required annotation guards.
The returned witness uses the original ambient assumptions and exactly the source
quantifier domain. -/
namespace ModalityInference.ComparisonPreparedDriver

theorem Execution.ambient_assumptions_defined {fuel first : Nat} {ambient : Bounds}
    {source target : Scheme} {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (e : Execution fuel first (SchemePreparation.prepare ambient source target) solved output) :
    (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined := by
  obtain ⟨_,_,_,_,_,_,_,_,hvalid⟩ := ComparisonGuardedEndpointQueries.run_sound e.allowed e.queried
  exact ComparisonPreparedScalar.required_typeBoundsDefined
    (ComparisonPreparedScalar.assemble_fixed_prepared e.assembled).fixed
    (ComparisonPreparedScalar.assembled_entails e.scalar_compiled e.assembled
      (hvalid e.scalar (List.mem_append_right _ List.mem_cons_self)))

theorem Execution.prepared_ambient_of_support {shapeFuel fuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (e : Execution fuel first (SchemePreparation.prepare ambient source target) solved output)
    (hmodeSupport : ∀v∈ComparisonSelectedBases.inputModes (SchemePreparation.prepare ambient source target),
      ∀w∈(e.action.mode v).vars,w∈ComparisonSelectedBases.inputModes (SchemePreparation.prepare ambient source target)) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) output := by
  let p:=SchemePreparation.prepare ambient source target
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
    e.ambient_assumptions_defined htheory hcompile hremap hv'

theorem Execution.prepared_ambient {shapeFuel fuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (e : Execution fuel first (SchemePreparation.prepare ambient source target) solved output) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) output := by
  apply e.prepared_ambient_of_support hs
  apply ComparisonGuardedEndpointQueries.assembled_inputModes e.assembled
  intro source hsource
  rcases List.mem_append.mp hsource with hsource|hsource
  · exact ComparisonPreparedQueries.compile_scalar_supported e.compiled _ source hsource
  · have he : source=e.scalar := by simpa using hsource
    subst source
    exact ComparisonPreparedScalar.run_scalar_supported e.scalar_compiled _

theorem propagate_ambient_sound {shapeFuel fuel first : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {output : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare ambient source target)=.success (.solved solved))
    (h : propagate fuel first (SchemePreparation.prepare ambient source target) solved=.success output) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) output := by
  obtain ⟨e⟩ := propagate_spec h
  exact e.prepared_ambient hs

end ModalityInference.ComparisonPreparedDriver

namespace ModalityInference.ComparisonAmbientDriver

private theorem bind_success {α β : Type} {r : RunResult α} {f : α → RunResult β} {b : β}
    (h : r.bind f=.success b) : ∃a,r=.success a ∧ f a=.success b := by
  cases r <;> simp_all [RunResult.bind]

theorem run_spec {fuel : Nat} {ambient : Bounds} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel ambient source target=.success result) :
    let p:=SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃solved action,ComparisonShapeSolver.prepare fuel p=.success (.solved solved) ∧
      ComparisonPreparedDriver.propagate fuel 0 p solved=.success action ∧ result=ComparisonPreparation.reconstruct p action := by
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

/-- The exact returned substitution has the public quantified domain, defined
images and body, and proves the original source constraints and comparison. -/
theorem run_result {fuel : Nat} {ambient : Bounds} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel ambient source target=.success result) :
    let p:=SchemePreparation.prepare ambient source target
    CompareInstantiatesUnder p.assumptions source result ∧ result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨solved,action,hs,ha,rfl⟩ := run_spec h
  have hw:=ComparisonPreparedDriver.reconstruct_result (ComparisonPreparedDriver.propagate_ambient_sound hs ha)
  let p:=SchemePreparation.prepare ambient source.requireDefinedInstances target
  let result:=ComparisonPreparation.reconstruct p action
  have hi : CompareInstantiatesUnder p.assumptions source result := ⟨hw.1.domain,hw.1.images,hw.1.body⟩
  have hb : AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.instanceGuards) := by
    simpa only [Scheme.requireDefinedInstances,CompareSubstitution.bounds,
      List.map_append,AlgebraEntailsAll,List.mem_append,or_imp,forall_and] using hw.2.2.1
  have he : p.assumptions=(SchemePreparation.prepare ambient source target).assumptions := by
    simp only [p,SchemePreparation.prepare_assumptions,Scheme.requireDefinedInstances_subsumptionIndices]
  have ht : p.targetType=(SchemePreparation.prepare ambient source target).targetType := by
    simp only [p,SchemePreparation.prepare,Scheme.requireDefinedInstances_subsumptionIndices]
  have hbody : AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := hw.2.2.2
  exact ⟨he ▸ hi,he ▸ hw.2.1,he ▸ hb.1,by simpa only [he,ht] using hbody⟩

theorem run_algebra_subsumesUnder {fuel : Nat} {ambient : Bounds} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel ambient source target=.success result) : AlgebraSubsumesUnder ambient source target := by
  obtain ⟨hi,hs,hb,ht⟩ := run_result h
  exact ⟨result,hi.domain,hs,hi.images,hi.body,hb,ht⟩

theorem run_assumptions_defined {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {result : CompareSubstitution} (h : run fuel ambient source target=.success result) :
    (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined := by
  obtain ⟨_,_,_,ha,_⟩ := run_spec h
  obtain ⟨e⟩ := ComparisonPreparedDriver.propagate_spec ha
  simpa only [SchemePreparation.prepare_assumptions,Scheme.requireDefinedInstances_subsumptionIndices]
    using e.ambient_assumptions_defined

@[simp] theorem run_nil (fuel : Nat) (source target : Scheme) :
    run fuel [] source target=ComparisonPreparedDriver.run fuel source target := rfl

open ComparisonPartialPropagation.Fuel

theorem run_settles (ambient : Bounds) (source target : Scheme) :
    Settles (fun fuel => run fuel ambient source target) := by
  unfold run
  split
  · exact Settles.rejected _
  · apply Settles.bind (ComparisonPreparedScalarPreflight.run_settles _)
    intro _
    apply Settles.bind ⟨shapePrepare_stable _, ComparisonShapeSolver.prepare_eventually _⟩
    intro shapes
    cases shapes with
    | infeasibleAssumptions => exact Settles.rejected _
    | solved solved =>
        apply Settles.bind (ComparisonPreparedDriver.propagate_settles _ _ _)
        intro result
        exact Settles.pure _

theorem run_terminates (ambient : Bounds) (source target : Scheme) :
    ∃threshold result,result ≠ .exhausted ∧
      ∀fuel≥threshold,run fuel ambient source target=result :=
  (run_settles ambient source target).2

theorem run_stable {small large : Nat} {ambient : Bounds} {source target : Scheme}
    {result : RunResult CompareSubstitution}
    (h : run small ambient source target=result) (hr : result ≠ .exhausted)
    (hle : small≤large) : run large ambient source target=result :=
  (run_settles ambient source target).1 hle h hr

end ModalityInference.ComparisonAmbientDriver
