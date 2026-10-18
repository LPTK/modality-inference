import ModalityInference.Proofs.ComparisonPreparedDriver
import ModalityInference.Proofs.ComparisonPreparedDriverTermination
import ModalityInference.Proofs.ComparisonPreparedModeWitness
import ModalityInference.Proofs.ComparisonPreparedAlternativeValidity
import ModalityInference.Proofs.ComparisonPreparedActivations

/-! Admissible witnesses yield one shared family, shape valuation and uniform
modality strategy for the actual guarded solver. Preparation and reconstruction
therefore complete for every comparison with a finite declared-shape model. -/
namespace ModalityInference.ComparisonPreparedQueries
open ComparisonSelectedBases ComparisonPreparation ComparisonWitnessRestriction

theorem program_witness_valid {shapeFuel fuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world shape : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    (hi : σ.ModesIdempotent) {program : Program}
    (hc : compile fuel first (SchemePreparation.prepare [] source target) solved=.success program)
    (hactive : ∀g∈program.groups,∀a∈g.alternatives,
      shape a.activation=true→a.branch.guard.eval world=true) :
    let p:=SchemePreparation.prepare [] source target
    ∀s∈program.sources,s.Valid
      (fun n=>((ComparisonSignedBranchImages.input (ComparisonSignedBranchImages.entries first p solved)).bases n).length)
      shape (ComparisonPreparedFamily.images (ComparisonSignedBranchImages.entries first p solved) (inputAction p σ))
      (SchemeModeSynthesis.strategy σ.mode) := by
  dsimp only
  intro s hsources hnot
  obtain ⟨g,hg,hsources⟩ := List.mem_flatMap.mp hsources
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hsources
  have has := (Alternative.active_iff a shape).mp hnot
  have hguard := hactive g hg a ha has
  have hgs := groups_spec (compile_spec hc).2.1
  obtain ⟨activation,b,hb,hbranch⟩ := hgs.2 g hg a ha
  have he : g.endpoint∈ComparisonSignedObservation.endpoints
      (SchemePreparation.prepare [] source target) := by
    apply List.mem_append_right
    rw [←hgs.1]
    exact List.mem_map.mpr ⟨g,hg,rfl⟩
  apply branch_witness_valid hs hw hsp hp hi (compile_spec hc).1 he hb ?_ hbranch
  simpa only [(branch_spec hbranch).2.1] using hguard

end ModalityInference.ComparisonPreparedQueries

namespace ModalityInference.ComparisonPreparedDriver
open ComparisonSelectedBases ComparisonPreparation ComparisonWitnessRestriction

theorem solver_complete_of_activation {shapeFuel compileFuel scalarFuel first : Nat}
    {source target : Scheme} {solved : ComparisonShapeSolver.Solved}
    {world shape : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    (hi : σ.ModesIdempotent)
    (hd : ComparisonPreparedScalar.ModeDomain (SchemePreparation.prepare [] source target) σ)
    {program : ComparisonPreparedQueries.Program}
    (hc : ComparisonPreparedQueries.compile compileFuel first
      (SchemePreparation.prepare [] source target) solved=.success program)
    {scalar : ComparisonGuardedEndpointQueries.Source}
    (hscalar : ComparisonPreparedScalar.run scalarFuel (SchemePreparation.prepare [] source target)=.success scalar)
    (hcondition : CNFHolds shape program.condition)
    (hactive : ∀g∈program.groups,∀a∈g.alternatives,
      shape a.activation=true→a.branch.guard.eval world=true) :
    let p:=SchemePreparation.prepare [] source target
    ∃threshold result,∀fuel≥threshold,
      ComparisonGuardedEndpointQueries.run fuel (queryInput first p solved)
        ModalSynthesis.locality (ComparisonPreparedScalar.flexibleAtoms p)
        (program.sources++[scalar]) program.condition=.success result := by
  let p:=SchemePreparation.prepare [] source target
  have hb : ∀s∈program.sources++[scalar],s.Binary := by
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact ComparisonPreparedQueries.compile_binary hc s hs
    · have he : s=scalar := by simpa using hs
      subst s
      exact ComparisonPreparedScalar.run_binary hscalar
  have ha : ∀s∈program.sources++[scalar],s.Allowed (queryInput first p solved).keys := by
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact ComparisonPreparedQueries.compile_allowed hc s hs
    · have he : s=scalar := by simpa using hs
      subst s
      exact ComparisonPreparedScalar.run_allowed hscalar _
  apply ComparisonGuardedEndpointQueries.run_complete_stable _ _ _ _ _ hb ha hcondition
    (ComparisonPreparedFamily.family _ (inputAction p σ)) hd.uniform
  intro s hsources
  rcases List.mem_append.mp hsources with hsources|hsources
  · exact ComparisonPreparedQueries.program_witness_valid hs hw hsp hp hi hc hactive s hsources
  · have he : s=scalar := by simpa using hsources
    subst s
    exact ComparisonPreparedScalar.run_prepared_valid hw hsp hscalar _ _ _

theorem propagate_complete {shapeFuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool} {σ : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=.success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : Supported (SchemePreparation.prepare [] source target) σ)
    (hp : BranchPolynomials first (SchemePreparation.prepare [] source target) solved world σ)
    (hi : σ.ModesIdempotent)
    (hd : ComparisonPreparedScalar.ModeDomain (SchemePreparation.prepare [] source target) σ) :
    let p:=SchemePreparation.prepare [] source target
    ∃threshold action,∀fuel≥threshold,propagate fuel first p solved=.success action := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨n,program,hprogram,hcovered⟩ :=
    ComparisonPreparedQueries.compile_complete_covered hs hw hsp hp
  obtain ⟨k,scalar,hscalar⟩ := ComparisonPreparedScalar.run_complete p
  obtain ⟨shape,hcondition,hactive⟩ := ComparisonPreparedQueries.compile_activation
    (hprogram n le_rfl) (hp.selectorFormula hs hw) hcovered
  obtain ⟨m,result,hsolver⟩ := solver_complete_of_activation hs hw hsp hp hi hd
    (hprogram n le_rfl) (hscalar k le_rfl) hcondition hactive
  let threshold:=max (max n k) m
  have hn : n≤threshold := (le_max_left _ _).trans (le_max_left _ _)
  have hk : k≤threshold := (le_max_right _ _).trans (le_max_left _ _)
  have hm : m≤threshold := le_max_right _ _
  obtain ⟨action,ha⟩ := propagate_of_solved (hprogram threshold hn)
    (hscalar threshold hk) (hsolver threshold hm)
  exact ⟨threshold,action,fun _ hf=>propagate_stable ha (by simp) hf⟩

theorem run_success_of_prepared {fuel : Nat} {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    {solved : ComparisonShapeSolver.Solved} {action : CompareSubstitution}
    (hpre : ComparisonPreparedScalarPreflight.run fuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target)=.success ())
    (hs : ComparisonShapeSolver.prepare fuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target)=.success (.solved solved))
    (hp : propagate fuel 0 (SchemePreparation.prepare [] source.requireDefinedInstances target) solved=.success action) :
    run fuel source target=.success
      (ComparisonPreparation.reconstruct (SchemePreparation.prepare [] source.requireDefinedInstances target) action) := by
  simp only [run,ht,hm,not_true_eq_false,or_self,↓reduceIte,hpre,hs,hp,
    bind,pure,RunResult.bind]

/-- Every admissible comparison with a finite model of its declared shapes
has an eventual successful result of the actual prepared structural driver. -/
theorem run_complete_finite_model {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (h : AlgebraSubsumesUnder [] source target)
    (hdecl : ∃φ,ComparisonShape.Models
      (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions φ) :
    ∃threshold result,∀fuel≥threshold,run fuel source target=.success result := by
  obtain ⟨n,solved,σ,ρ,hs,hw,hsp,hi,hd,_,hp,_,_⟩ :=
    algebra_closed_branch_polynomials_scoped 0 h hdecl
  obtain ⟨k,action,ha⟩ := propagate_complete (hs n le_rfl) hw hsp hp hi hd
  obtain ⟨j,hpre⟩ := ComparisonPreparedScalarPreflight.run_prepared_complete hw hsp hd
  refine ⟨max (max n k) j,ComparisonPreparation.reconstruct
    (SchemePreparation.prepare [] source.requireDefinedInstances target) action,?_⟩
  intro fuel hf
  exact run_success_of_prepared ht hm (hpre fuel ((le_max_right _ _).trans hf))
    (hs fuel ((le_max_left _ _).trans ((le_max_left _ _).trans hf)))
    (ha fuel ((le_max_right _ _).trans ((le_max_left _ _).trans hf)))

end ModalityInference.ComparisonPreparedDriver
