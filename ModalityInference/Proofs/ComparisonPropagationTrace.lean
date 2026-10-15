import ModalityInference.Proofs.ComparisonPropagationSetup
import ModalityInference.Proofs.ComparisonCheckerScope
import ModalityInference.Proofs.ComparisonCheckerSolution

/-! Exact stages and returned action of a successful propagation branch. -/
namespace ModalityInference.ComparisonChecker

def Setup.runtimeImages (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) : List (Nat × CompareTy) :=
  reduced.partialTypes ++ s.templates.substitution.types.map
    (fun (n, t) => (n, ({ types := types.types } : CompareSubstitution).ty t))

def Setup.runtimeModes (s : Setup) (modes : SchemeModeSynthesis.Result) : Substitution :=
  { modes := s.absorption.action.modes ++
      s.annotations.images.map (fun (n, m) => (n, m.subst modes.substitution.mode)) ++
      modes.substitution.modes }

def Setup.runtimeAfter (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) : CompareSubstitution :=
  { types := (s.runtimeImages reduced types).map
      (fun (n, t) => (n, t.subst CompareTy.var (s.runtimeModes modes).mode))
    modes := (s.runtimeModes modes).modes }

def Setup.runtimeAction (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result) : CompareSubstitution :=
  ComparisonExactContext.finish s.before (s.runtimeAfter reduced types modes)

def Setup.evidence (s : Setup) (reduced : ComparisonReduction.State)
    (types : ComparisonElimination.Result) (modes : SchemeModeSynthesis.Result)
    (report : ConcreteBackend.Report) : Evidence :=
  let action := s.runtimeAction reduced types modes
  { substitution := ComparisonPreparation.reconstruct s.original action
    assumptions := s.original.assumptions
    obligations := action.bounds s.original.sourceBounds
    body := (action.ty s.original.sourceType, .ofTy s.original.targetType)
    flexibleAtoms := modes.flexibleAtoms
    query := modes.query
    backend := report }

structure PropagationTrace (fuel : Nat) (s : Setup) (e : Evidence) where
  reduced : ComparisonReduction.State
  types : ComparisonElimination.Result
  modes : SchemeModeSynthesis.Result
  report : ConcreteBackend.Report
  known_eq : ComparisonBody.knownTotal fuel (s.input.assumptions ++ s.input.sourceBounds.assumptions)
    (ComparisonAnnotations.obligationExpressions s.input) = .success s.known
  reduced_eq : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced
  types_eq : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types
  modes_eq : SchemeModeSynthesis.run fuel s.modeIds types.query = .success modes
  report_eq : ConcreteBackend.decideFormula fuel modes.query = .success report
  report_valid : report.valid = true
  evidence_eq : e = s.evidence reduced types modes report

theorem propagate_trace {fuel p shapes shared before e}
    (h : propagate fuel p shapes shared before = .success e) :
    ∃ known, Nonempty (PropagationTrace fuel ⟨p, before, shapes, known, shared⟩ e) := by
  simp only [propagate, bind, pure, RunResult.bind] at h
  repeat' first | contradiction | cases h | split at h
  rename_i _ known hknown _ reduced hred _ types htypes _ modes hmodes _ report hreport hv
  refine ⟨known, ⟨{
    reduced := reduced, types := types, modes := modes, report := report
    known_eq := hknown, reduced_eq := hred, types_eq := htypes, modes_eq := hmodes
    report_eq := hreport, report_valid := ?_, evidence_eq := rfl }⟩⟩
  simpa using hv

theorem PropagationTrace.action_domains {fuel s e} (t : PropagationTrace fuel s e)
    (hb : (CompareSubstitution.ofSubstitution s.before).DomainsAbove
      s.original.firstType s.original.firstMode) :
    (s.runtimeAction t.reduced t.types t.modes).DomainsAbove
      s.original.firstType s.original.firstMode := by
  apply ComparisonExactContext.finish_domainsAbove hb
  constructor
  · intro entry he
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp he
    rcases List.mem_append.mp hp with hp | hp
    · have hn := List.mem_map_of_mem (f := Prod.fst) hp
      rw [ComparisonReduction.prepare_partial_domain t.reduced_eq] at hn
      exact (s.bare_range hn).1
    · obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hp
      have hn := List.mem_map_of_mem (f := Prod.fst) hmem
      simp only [Setup.templates, ComparisonSkeleton.allocate_domain] at hn
      exact (s.names_range hn).1
  · intro entry he
    simp only [Setup.runtimeAfter, Setup.runtimeModes, List.mem_append, List.mem_map] at he
    rcases he with (hp | ⟨old, hmem, rfl⟩) | hp
    · exact absorption_domain_lower (p := s.input) (total := s.total) hp
    · exact annotations_domain_lower (p := s.absorbed) (total := s.total) (entry := old) hmem
    · have hn := List.mem_map_of_mem (f := Prod.fst) hp
      rw [(SchemeModeSynthesis.run_domain t.modes_eq).2.1] at hn
      have hn := (List.mem_filter.mp hn).1
      simp only [List.mem_range'] at hn
      omega

theorem PropagationTrace.preparedSolution {fuel s e} (t : PropagationTrace fuel s e)
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hshape : (s.runtimeAction t.reduced t.types t.modes).WellShaped s.original.assumptions)
    (hbounds : AlgebraEntailsAll s.original.assumptions
      ((s.runtimeAction t.reduced t.types t.modes).bounds s.original.sourceBounds))
    (hbody : AlgebraSubtype s.original.assumptions
      ((s.runtimeAction t.reduced t.types t.modes).ty s.original.sourceType)
      (.ofTy s.original.targetType)) : PreparedSolution s.original e := by
  refine ⟨s.runtimeAction t.reduced t.types t.modes, ?_, ?_, ?_,
    t.action_domains hb.domainsAbove, hshape, hbounds, hbody⟩
  · exact congrArg Evidence.substitution t.evidence_eq
  · exact congrArg Evidence.obligations t.evidence_eq
  · exact congrArg Evidence.body t.evidence_eq

end ModalityInference.ComparisonChecker
