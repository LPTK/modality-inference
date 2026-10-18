import ModalityInference.Proofs.ComparisonLayoutScalarSupport
import ModalityInference.Proofs.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonSignedWorldSupport

namespace ModalityInference.ComparisonPreparedQueries
open ComparisonLayoutScalarSupport ComparisonSelectedBases ComparisonSignedObservation

/-- Successful branch compilation introduces only original input modality names.
The result is syntactic and does not depend on an accepting witness. -/
theorem branch_scalar_supported {fuel first activation : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {b : ComparisonSelectedBases.Branch} {a : Alternative}
    (h : branch fuel first activation p solved declared endpoint b=.success (some a))
    (he : endpoint∈ComparisonSignedObservation.endpoints p) (size : Nat→Nat) :
    a.source.source.ScalarSupported size
      (fun i=>SymbolicModes.atomVariable i∈ComparisonSelectedBases.inputModes p) := by
  obtain ⟨_,_,_,hb,ht,hc,hr⟩:=branch_spec h
  have hbased:=(ComparisonStructuralQuerySoundness.build_based hb).2
  have hmode : ∀v∈p.assumptions.modVars,v∈ComparisonSelectedBases.inputModes p := by
    intro v hv
    apply (ComparisonSelectedBases.mem_inputModes p v).mpr
    simp [ComparisonWitnessRestriction.inputModes,hv]
  have htheory:=coherence_run_support hbased (scoped_bounds hmode) ht
  have he':=endpoints_input he
  have hl : ∀v∈endpoint.1.modVars,v∈ComparisonSelectedBases.inputModes p :=
    fun v hv=>(ComparisonSelectedBases.mem_inputModes p v).mpr (he'.2.2.1 hv)
  have hu : ∀v∈endpoint.2.modVars,v∈ComparisonSelectedBases.inputModes p :=
    fun v hv=>(ComparisonSelectedBases.mem_inputModes p v).mpr (he'.2.2.2 hv)
  have hguards:=compileGuards_support hc (compile_scoped (context_scoped _ _) _ hl hu)
  constructor
  · intro v hv hn
    exact allowed_decode.mp (htheory v hv) hn
  · intro c hcm v hv hn
    obtain ⟨source,hs,hcs⟩:=ComparisonSignedBranchCalls.compile_origin hr c hcm
    have hg:=(ComparisonSignedBranchCalls.clause_spec hcs).1
    have hmem : v∈CNFPropagation.atoms [source.guard] := hg ▸ hv
    exact allowed_decode.mp (hguards source hs v hmem) hn
  · intro call _ i _
    exact congrArg Prod.fst (ComparisonLayoutWorlds.decode_basis call.route i)

/-- Every source returned by the actual prepared compiler has exact scalar
input provenance, for any finite image-coordinate sizes. -/
theorem compile_scalar_supported {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program}
    (h : compile fuel first p solved=.success program) (size : Nat→Nat) :
    ∀source∈program.sources,source.source.ScalarSupported size
      (fun i=>SymbolicModes.atomVariable i∈ComparisonSelectedBases.inputModes p) := by
  intro source hs
  obtain ⟨g,hg,hs⟩:=List.mem_flatMap.mp hs
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hs
  have hgroups:=groups_spec (compile_spec h).2.1
  obtain ⟨activation,b,_,hb⟩:=hgroups.2 g hg a ha
  have hep : g.endpoint∈ComparisonSignedObservation.sourceEndpoints p := by
    rw [←hgroups.1]
    exact List.mem_map.mpr ⟨g,hg,rfl⟩
  exact branch_scalar_supported hb (List.mem_append_right _ hep) size

end ModalityInference.ComparisonPreparedQueries
