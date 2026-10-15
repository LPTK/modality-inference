import ModalityInference.Proofs.ComparisonPropagationResult
import ModalityInference.Proofs.ComparisonPropagationSemantic
import ModalityInference.Proofs.ComparisonCheckerSoundness

/-! A successful executable comparison returns a guarded internal witness for
the original public schemes. -/
namespace ModalityInference.ComparisonChecker

theorem propagate_solution {fuel : Nat} {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {before : Substitution} {shared : Bool} {e : Evidence}
    (hs : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved shapes))
    (hb : ComparisonExactContext.Scoped (SchemePreparation.prepare [] source target) before)
    (hbounded : before.Bounded (SchemePreparation.prepare [] source target).nextType
      (SchemePreparation.prepare [] source target).nextMode)
    (h : propagate fuel (SchemePreparation.prepare [] source target) shapes shared before = .success e) :
    PreparedSolution (SchemePreparation.prepare [] source target) e := by
  obtain ⟨known, ⟨trace⟩⟩ := propagate_trace h
  let s : Setup := ⟨SchemePreparation.prepare [] source target, before, shapes, known, shared⟩
  have htotal : ∀ m, s.total m = true → Submode s.original.assumptions
      (m.subst trace.modes.substitution.mode) (m.subst trace.modes.substitution.mode) := by
    intro m ht
    apply ComparisonGuardedTotal.isTotal_synthesized
      (p := s.work) (guards := s.input.sourceBounds) trace.known_eq trace.types_eq trace.modes_eq
      (s.synthesized_assumptions trace.modes_eq
        (SchemePreparation.prepare_assumptions_bounded_first [] source target))
    · intro c hc
      exact List.mem_append_left _ (List.mem_append_right _ hc)
    · exact ht
  have hsemantic := s.semantic_sound_of_total rfl hs hb hbounded
    htotal trace.reduced_eq trace.types_eq trace.modes_eq
  exact trace.solution_of_semantic rfl hs hb hbounded hsemantic.2.1 hsemantic.2.2

theorem run_solution {fuel : Nat} {source target : Scheme} {e : Evidence}
    (h : run fuel source target = .success e) :
    PreparedSolution (SchemePreparation.prepare [] source target) e :=
  run_solution_of_propagate
    (SchemePreparation.prepare_targetType_bounded [] source target)
    (fun _ _ _ hs _ _ _ hb hbounded hr => propagate_solution hs hb hbounded hr) h

theorem run_algebra_subsumes {fuel : Nat} {source target : Scheme} {e : Evidence}
    (h : run fuel source target = .success e) : AlgebraSubsumes [] source target :=
  (run_solution h).subsumes

end ModalityInference.ComparisonChecker
