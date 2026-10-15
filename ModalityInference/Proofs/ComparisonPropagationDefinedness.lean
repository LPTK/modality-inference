import ModalityInference.Proofs.ComparisonPropagationSetup
import ModalityInference.Proofs.ComparisonEliminationSoundness
import ModalityInference.Proofs.ComparisonCheckerScope

/-! Written source bounds avoid the separately reconstructed bare images.
Their remaining images are the defined witnesses of opaque group elimination. -/
namespace ModalityInference

namespace ComparisonElimination

theorem imageAction_type_defined_outside {Δ : Bounds} {earlier images : List (Nat × CompareTy)}
    {modes : Substitution} {v : TypeVar}
    (hskip : ∀ entry ∈ earlier, v ≠ .flex entry.1)
    (hi : ∀ entry ∈ images, (entry.2.subst CompareTy.var modes.mode).DefinedUnder Δ) :
    ((imageAction (earlier ++ images) modes).type v).DefinedUnder Δ := by
  rw [imageAction_type]
  cases v with
  | rigid n => simp [CompareSubstitution.type, CompareTy.subst, CompareTy.DefinedUnder,
      CompareTy.wellFormedBounds, ModeModels]
  | flex n =>
    have hn : earlier.lookup n = none := by
      apply List.lookup_eq_none_iff.mpr
      intro entry he
      apply bne_iff_ne.mpr
      intro heq
      exact hskip entry he (congrArg TypeVar.flex heq)
    simp only [CompareSubstitution.type, List.lookup_append, hn]
    cases he : images.lookup n with
    | none => simp [CompareTy.subst, CompareTy.DefinedUnder, CompareTy.wellFormedBounds,
        ModeModels]
    | some image =>
      obtain ⟨before, after, hs, _⟩ := List.lookup_eq_some_iff.mp he
      exact hi (n, image) (by simp [hs])

end ComparisonElimination

namespace ComparisonChecker

theorem Setup.templates_bare_avoids_bounds (s : Setup) :
    ∀ n ∈ s.bare, ∀ c ∈ s.templates.substitution.bounds s.work.sourceBounds,
      TypeVar.flex n ∉ c.typeVars :=
  ComparisonReduction.bounds_typeFree_subst (fun _ hn => s.bare_avoids_bounds hn)
    (ComparisonReduction.typeFree_type_of_images
      (ComparisonSkeleton.allocate_images_free s.work s.shapes s.names s.bare
        s.original.nextType s.annotations.nextMode (fun _ hn => (s.bare_range hn).2)))

theorem Setup.sourceBounds_defined (s : Setup) {reductionFuel eliminationFuel : Nat}
    {reduced residual : ComparisonReduction.State} {result : ComparisonElimination.Result}
    {modes : Substitution}
    (hred : ComparisonReduction.prepare reductionFuel s.work s.templates s.bare s.known s.shared =
      .success reduced)
    (hrun : ComparisonElimination.run eliminationFuel s.work s.shapes s.templates residual =
      .success result)
    (hm : ∀ v, Entails s.original.assumptions (.defined (modes.mode v))) :
    ∀ c ∈ s.templates.substitution.bounds s.work.sourceBounds, ∀ v ∈ c.typeVars,
      CompareTy.DefinedUnder
        ((ComparisonElimination.imageAction (reduced.partialTypes ++ result.types) modes).type v)
        s.original.assumptions := by
  intro c hc v hv
  apply ComparisonElimination.imageAction_type_defined_outside
  · intro entry he heq
    have hn : entry.1 ∈ s.bare := by
      rw [← ComparisonReduction.prepare_partial_domain hred]
      exact List.mem_map_of_mem (f := Prod.fst) he
    exact s.templates_bare_avoids_bounds entry.1 hn c hc (heq ▸ hv)
  · apply ComparisonElimination.run_defined_subst hrun CompareTy.var modes.mode
    · intro v _ _
      simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
    · exact hm

end ComparisonChecker

end ModalityInference
