import ModalityInference.Proofs.Resources
import ModalityInference.Proofs.PolymorphicCapture

/-! The original counterexample with ownership evidence indexed by its instance. -/
namespace ModalityInference.ResourceCapture
open PolymorphicCapture (value functionScheme assignment)

theorem interpreted (w : World) (m : Mode) :
    ResourceInterpretation w
      (.fn (.unit Mode.identity) (.credit m) Mode.identity) Mode.identity value
      {Location.heap 0} := by
  refine ⟨(PolymorphicCapture.interpreted assignment w).1, ?_,
    (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h), ?_⟩
  case refine_2 =>
    exact fun _ _ _ _ _ _ _ _ =>
      ⟨.credit (.heap 0), cellResources m (.heap 0), .var rfl,
        .credit trivial (Or.inr trivial),
        fun _ hl => Or.inl (Or.inl (cellResources_subset m (.heap 0) hl))⟩
  exact fun _ hl => (Set.mem_singleton_iff.mp hl).symm ▸
    References.closure (List.mem_singleton_self _) References.credit

theorem scheme_interpreted (ρ : GroundAssignment) (w : World) :
    ResourceSchemeInterpretation ρ w functionScheme value {Location.heap 0} := by
  refine ⟨(interpreted w Mode.identity).references, ?_⟩
  intro η t _ ht
  simp [PolymorphicCapture.functionScheme, PolymorphicCapture.creditScheme,
    Scheme.mono, TypeExpr.realize, ModExpr.eval, GroundTy.modal] at ht
  exact ht ▸ ⟨{Location.heap 0}, Set.Subset.rfl, interpreted w (η.modes (.flex 0))⟩

def uniqueAssignment : GroundAssignment :=
  {assignment with modes := fun v => if v = .flex 0 then Mode.identity else assignment.modes v}

theorem unique_instantiates : GroundInstantiates assignment functionScheme uniqueAssignment := by
  simp [GroundInstantiates, PolymorphicCapture.functionScheme, uniqueAssignment, GroundModels]
  exact fun _ h he => (h he).elim

/-- The same variable, environment, and evaluator as the recorded counterexample
now preserve the captured cell across the unique instance. -/
theorem variable_semantic (w : World) :
    ResourceSemanticEvaluation w [value] (.var 0)
      (.fn (.unit Mode.identity) (.credit Mode.identity) Mode.identity) {Location.heap 0} := by
  simpa only [ContextResources.singleton] using
    ResourceEnvironmentInterpretation.lookup
      (.singleton (scheme_interpreted assignment w)) (i := 0) rfl unique_instantiates rfl

end ModalityInference.ResourceCapture
