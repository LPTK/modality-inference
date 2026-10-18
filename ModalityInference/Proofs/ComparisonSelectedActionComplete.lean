import ModalityInference.Proofs.ComparisonInputAction
import ModalityInference.Proofs.ComparisonSelectedAction
import ModalityInference.Proofs.ComparisonSelectedPlan

/-! Finite-shape admissible comparisons have one compiled selector plan and
one complete executable reconstruction with the same modality assignment. -/
namespace ModalityInference.ComparisonSelectedBases

open ComparisonPreparation ComparisonWitnessRestriction ComparisonShapeRetraction

theorem algebra_reifyAction {ambient : Bounds} {source target : Scheme}
    (first : Nat) (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃threshold solved world plan modes entries action,
      (∀fuel≥threshold,
        ComparisonShapeSolver.prepare fuel p=.success (.solved solved) ∧
        compilePlan fuel first p solved=.success plan) ∧
      CNFHolds world plan.clauses ∧
      reifyAction first p solved world modes entries=some action ∧
      action.types.map Prod.fst=inputTypeKeys p ∧ action.modes=modes ∧
      PreparedWitnessUnder p action ∧ action.ModesIdempotent := by
  let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
  obtain ⟨σ,hw⟩ := prepare_algebra_under_complete h.requireDefinedInstances
  obtain ⟨n,solved,hs⟩ := ComparisonSkeleton.prepared_witness_shape_complete hw.1 hdecl
  obtain ⟨σ',hw',hsp,_,hi⟩ := ComparisonFixedModeWitness.prepared_supported_fixed hw
  obtain ⟨τ,ρ,hτ,hτsp,hkeys,hmodes,_,hp⟩ := prepared_branch_polynomials first (hs n le_rfl)
    (inputAction_prepared hw') (inputAction_supported hsp)
  have hτi := (inputAction_modesIdempotent (p:=p) hi).of_modes_eq hmodes
  have hτkeys : τ.types.map Prod.fst=inputTypeKeys p :=
    hkeys.trans (inputAction_keys p σ')
  obtain ⟨entries,action,ha,_,haks,ham,haw⟩ := hp.reifyAction hτ hτi
    (fun k hk => ((mem_inputTypeKeys p k).mp (hτkeys ▸ hk)).1)
  obtain ⟨m,plan,hplan⟩ := compilePlan_complete first p solved
  refine ⟨max n m,solved,(layout first p solved).encode ρ,plan,τ.modes,entries,action,
    ?_,?_,ha,haks.trans hτkeys,ham,haw,hτi.of_modes_eq ham⟩
  · intro fuel hf
    exact ⟨hs fuel (Nat.le_trans (Nat.le_max_left ..) hf),
      hplan fuel (Nat.le_trans (Nat.le_max_right ..) hf)⟩
  · exact (CompactCNF.toCNF_correct (compilePlan_spec (hplan m le_rfl)).2.2 _).mpr
      (hp.selectorFormula (hs n le_rfl) hτ)

end ModalityInference.ComparisonSelectedBases
