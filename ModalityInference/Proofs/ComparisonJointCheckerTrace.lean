import ModalityInference.ComparisonJointChecker
import ModalityInference.Proofs.ComparisonJointEliminationDomains
import ModalityInference.Proofs.ComparisonPreparation

/-! Exact successful executions of the shared checker and the domains of their
restored and reconstructed substitutions. -/
namespace ModalityInference.ComparisonJointChecker

open ComparisonChecker

def executionSetup (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (known : List ModExpr) : Setup := ⟨p, {}, shapes, known, false⟩

structure PropagateTrace (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (action : CompareSubstitution) where
  known : List ModExpr
  reduced : ComparisonReduction.State
  output : ComparisonJointBatchReification.Output
  known_eq : ComparisonBody.knownTotal fuel (p.assumptions ++ p.sourceBounds.assumptions)
    (ComparisonAnnotations.obligationExpressions p) = .success known
  reduced_eq :
    let s := executionSetup p shapes known
    ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced
  elimination_eq :
    let s := executionSetup p shapes known
    ComparisonJointElimination.run fuel s.work shapes s.templates (s.reduced reduced)
      (allowedModes p) s.modeIds (6 * p.firstMode) = .success output
  action_eq : action = restore (executionSetup p shapes known) output

theorem propagate_trace {fuel p shapes action}
    (h : propagate fuel p shapes = .success action) :
    Nonempty (PropagateTrace fuel p shapes action) := by
  simp only [propagate, bind, pure, RunResult.bind] at h
  repeat' first | contradiction | cases h | split at h
  rename_i _ known hk _ reduced hr _ output ho
  exact ⟨⟨known, reduced, output, hk, hr, ho, rfl⟩⟩

structure RunTrace (fuel : Nat) (source target : Scheme) (result : CompareSubstitution) where
  types_nodup : source.typeParams.Nodup
  modes_nodup : source.modParams.Nodup
  shapes : ComparisonShapeSolver.Solved
  action : CompareSubstitution
  shape_eq : ComparisonShapeSolver.prepare fuel
    (SchemePreparation.prepare [] source.requireDefinedInstances target) = .success (.solved shapes)
  propagate_eq : propagate fuel (SchemePreparation.prepare [] source.requireDefinedInstances target)
    shapes = .success action
  result_eq : result = ComparisonPreparation.reconstruct
    (SchemePreparation.prepare [] source.requireDefinedInstances target) action

theorem run_trace {fuel source target result}
    (h : run fuel source target = .success result) : Nonempty (RunTrace fuel source target result) := by
  simp only [run, bind, pure, RunResult.bind] at h
  split at h
  · contradiction
  · rename_i hn
    have ht := not_or.mp hn
    simp only [not_not] at ht
    repeat' first | contradiction | cases h | split at h
    rename_i _ shapes hs _ action ha
    exact ⟨⟨ht.1, ht.2, shapes, action, hs, ha, rfl⟩⟩

theorem templates_domains (s : Setup) :
    (CompareSubstitution.ofSubstitution s.templates.substitution).DomainsAbove
      s.original.firstType s.original.firstMode := by
  constructor
  · intro entry he
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp he
    have hn := List.mem_map_of_mem (f := Prod.fst) hp
    rw [Setup.templates, ComparisonSkeleton.allocate_domain] at hn
    have hr := (List.mem_filter.mp hn).1
    simp only [List.mem_range'] at hr
    change s.original.firstType ≤ pair.1
    omega
  · have hm : s.templates.substitution.modes = [] := by
      change (ComparisonSkeleton.allocate s.work s.shapes s.names s.original.nextType
        s.annotations.nextMode).substitution.modes = []
      cases s.names <;> rfl
    simp [CompareSubstitution.ofSubstitution, hm]

theorem PropagateTrace.domainsAbove {fuel p shapes action}
    (t : PropagateTrace fuel p shapes action) (hp : p.firstType ≤ p.nextType) :
    action.DomainsAbove p.firstType p.firstMode := by
  rw [t.action_eq]
  apply ComparisonExactContext.finish_domainsAbove (templates_domains _)
  have h := ComparisonJointElimination.setup_run_domains t.elimination_eq
  exact ⟨fun entry he => hp.trans (h.1 entry he), h.2⟩

theorem propagate_domains {fuel p shapes action}
    (h : propagate fuel p shapes = .success action) (hp : p.firstType ≤ p.nextType) :
    action.DomainsAbove p.firstType p.firstMode := by
  obtain ⟨t⟩ := propagate_trace h
  exact t.domainsAbove hp

theorem propagate_prepared_domains {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {action : CompareSubstitution}
    (h : propagate fuel (SchemePreparation.prepare ambient source target) shapes = .success action) :
    action.DomainsAbove (SchemePreparation.prepare ambient source target).firstType
      (SchemePreparation.prepare ambient source target).firstMode :=
  propagate_domains h (Nat.le_add_right _ _)

theorem RunTrace.action_domains {fuel source target result}
    (t : RunTrace fuel source target result) :
    t.action.DomainsAbove (SchemePreparation.prepare [] source.requireDefinedInstances target).firstType
      (SchemePreparation.prepare [] source.requireDefinedInstances target).firstMode :=
  propagate_prepared_domains t.propagate_eq

theorem run_spec {fuel source target result}
    (h : run fuel source target = .success result) :
    source.typeParams.Nodup ∧ source.modParams.Nodup ∧
      ∃shapes action,
        ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source.requireDefinedInstances target) =
          .success (.solved shapes) ∧
        propagate fuel (SchemePreparation.prepare [] source.requireDefinedInstances target) shapes = .success action ∧
        result = ComparisonPreparation.reconstruct
          (SchemePreparation.prepare [] source.requireDefinedInstances target) action ∧
        action.DomainsAbove (SchemePreparation.prepare [] source.requireDefinedInstances target).firstType
          (SchemePreparation.prepare [] source.requireDefinedInstances target).firstMode := by
  obtain ⟨t⟩ := run_trace h
  exact ⟨t.types_nodup, t.modes_nodup, t.shapes, t.action, t.shape_eq, t.propagate_eq,
    t.result_eq, t.action_domains⟩

theorem run_domain {fuel source target result}
    (h : run fuel source target = .success result) : CompareInstantiates source result := by
  obtain ⟨t⟩ := run_trace h
  rw [t.result_eq]
  exact ComparisonPreparation.reconstruct_instantiates [] source.requireDefinedInstances target t.action

theorem run_exact_domains {fuel source target result}
    (h : run fuel source target = .success result) :
    result.types.map Prod.fst = source.typeParams ∧ result.modes.map Prod.fst = source.modParams := by
  obtain ⟨t⟩ := run_trace h
  rw [t.result_eq]
  simp [ComparisonPreparation.reconstruct, SchemePreparation.prepare, Scheme.freshSubstitution,
    Scheme.requireDefinedInstances, List.map_map, Function.comp_def]

end ModalityInference.ComparisonJointChecker
