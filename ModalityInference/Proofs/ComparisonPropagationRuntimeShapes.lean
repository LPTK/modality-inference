import ModalityInference.Proofs.ComparisonPropagationCore
import ModalityInference.Proofs.ComparisonPropagationTrace

/-! The actual reconstructed runtime action has compatible internal witnesses,
including every retained image and every ordinary context specialization. -/
namespace ModalityInference.ComparisonChecker

theorem Setup.runtimeImages_wellShaped (s : Setup) {source target : Scheme} {fuel reduced types}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types) :
    ∀ entry ∈ s.runtimeImages reduced types, entry.2.WellShaped s.original.assumptions := by
  have hleaf : ({ types := types.types } : CompareSubstitution).WellShaped s.original.assumptions :=
    fun entry hm => s.coreImages_wellShaped hp hs hb hbounded hr he entry
      (List.mem_append_right _ hm)
  intro entry hm
  rcases List.mem_append.mp hm with hm | hm
  · exact s.partial_wellShaped hp hs hb hr entry hm
  · obtain ⟨pair, _, rfl⟩ := List.mem_map.mp hm
    exact hleaf.ty pair.2

theorem Setup.runtimeAction_wellShaped (s : Setup) {source target : Scheme} {fuel reduced types modes}
    (hp : s.original = SchemePreparation.prepare [] source target)
    (hs : ComparisonShapeSolver.prepare fuel s.original = .success (.solved s.shapes))
    (hb : ComparisonExactContext.Scoped s.original s.before)
    (hbounded : s.before.Bounded s.original.nextType s.original.nextMode)
    (hr : ComparisonReduction.prepare fuel s.work s.templates s.bare s.known s.shared = .success reduced)
    (he : ComparisonElimination.run fuel s.work s.shapes s.templates (s.reduced reduced) = .success types) :
    (s.runtimeAction reduced types modes).WellShaped s.original.assumptions := by
  apply ComparisonExactContext.finish_wellShaped
  exact ComparisonElimination.imageAction_wellShaped
    (s.runtimeImages_wellShaped hp hs hb hbounded hr he) (s.runtimeModes modes)

end ModalityInference.ComparisonChecker
