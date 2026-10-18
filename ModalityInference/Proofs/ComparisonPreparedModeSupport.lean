import ModalityInference.Proofs.ComparisonSignedWorldSupport
import ModalityInference.Proofs.ModeFormulaSupport

/-! The actual prepared scalar query and finite modality reconstruction preserve
input-name support. The common scalar strategy is unchanged by this proof. -/
namespace ModalityInference.ComparisonPreparedScalar

private theorem annotation_variables (body : Ty) {m : ModExpr}
    (hm : m∈ComparisonAnnotations.expressions body) : m.vars⊆body.modVars := by
  induction body with
  | var | unit | credit => simp [ComparisonAnnotations.expressions] at hm
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    rcases List.mem_append.mp hm with hm|hm
    · exact (ia hm).trans Finset.subset_union_left
    · exact (ib hm).trans Finset.subset_union_right
  | modal a n ia =>
    rcases List.mem_cons.mp hm with rfl|hm
    · exact Finset.subset_union_right
    · exact (ia hm).trans Finset.subset_union_left

theorem annotations_input {p : SchemePreparation.Prepared} {m : ModExpr}
    (hm : m∈annotations p) {v : ModVar} (hv : v∈m.vars) :
    v∈ComparisonSelectedBases.inputModes p := by
  obtain ⟨pair,hpair,hm⟩ := List.mem_flatMap.mp hm
  apply (ComparisonSelectedBases.mem_inputModes p v).mpr
  rcases List.mem_append.mp hm with hm|hm
  · exact (ComparisonSignedObservation.endpoints_input hpair).2.2.1
      (annotation_variables pair.1 hm hv)
  · exact (ComparisonSignedObservation.endpoints_input hpair).2.2.2
      (annotation_variables pair.2 hm hv)

theorem required_input {p : SchemePreparation.Prepared} {v : ModVar}
    (hv : v∈(required p).modVars) : v∈ComparisonSelectedBases.inputModes p := by
  obtain ⟨c,hc,hv⟩ := (Bounds.mem_modVars_iff _ _).mp hv
  rcases List.mem_append.mp hc with hc|hc
  · have hh := ComparisonGuardedTotal.scalarBounds_modVars p.sourceBounds
      ((Bounds.mem_modVars_iff _ _).mpr ⟨c,hc,hv⟩)
    apply (ComparisonSelectedBases.mem_inputModes p v).mpr
    simp [ComparisonWitnessRestriction.inputModes,hh]
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hc
    exact annotations_input hm hv


theorem run_scalar_supported {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result)
    (size : Nat→Nat) : result.source.ScalarSupported size
      (fun i=>SymbolicModes.atomVariable i∈ComparisonSelectedBases.inputModes p) := by
  obtain ⟨theory,goals,ht,hg,rfl⟩ := run_spec h
  constructor
  · intro i hi _
    have hv := boundsModeFormula_variables (CompactCNF.toCNF_atoms ht hi)
    apply (ComparisonSelectedBases.mem_inputModes p _).mpr
    simp [source,ComparisonWitnessRestriction.inputModes,hv]
  · intro c hc i hi _
    obtain ⟨guard,hguard,rfl⟩ := List.mem_map.mp hc
    have hi' : i∈CNFPropagation.atoms goals := by
      obtain ⟨d,hd,polarity,hp⟩ := CNFPropagation.mem_atoms.mp hi
      cases List.mem_singleton.mp hd
      exact CNFPropagation.mem_atoms.mpr ⟨guard,hguard,polarity,hp⟩
    exact required_input (boundsModeFormula_variables (CompactCNF.toCNF_atoms hg hi'))
  · intro call hcall
    simp [source,ComparisonSignedWorlds.calls,List.flatMap_map] at hcall

end ModalityInference.ComparisonPreparedScalar

namespace ModalityInference.ComparisonGuardedEndpointQueries

/-- Actual assembled modality images use only names from the prepared input.
Both endpoint queries and the always-active scalar source use this same action. -/
theorem assembled_inputModes {p : SchemePreparation.Prepared}
    {input : ComparisonSignedSynthesis.Input} {sources : List Source}
    {selectors : Nat→Bool} {action : Substitution}
    (ha : ComparisonPreparedScalar.assemble p
      (modes ModalSynthesis.locality (ComparisonPreparedScalar.flexibleAtoms p)
        input sources selectors)=some action)
    (hs : ∀source∈sources,source.source.ScalarSupported
      (fun n=>(input.bases n).length)
      (fun i=>SymbolicModes.atomVariable i∈ComparisonSelectedBases.inputModes p)) :
    ∀v∈ComparisonSelectedBases.inputModes p,∀w∈(action.mode v).vars,
      w∈ComparisonSelectedBases.inputModes p := by
  intro v hv w hw
  exact assembled_mode_support ha hs hv hw

end ModalityInference.ComparisonGuardedEndpointQueries
