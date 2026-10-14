import ModalityInference.Proofs.GenerationCompletenessContext

/-! Fresh semantic witnesses for constructor-local allocation. -/
namespace ModalityInference

theorem InferenceState.freshTypes2_mode_model (s : InferenceState) (ρ : GroundAssignment)
    (a b : GroundTy) (m : Mode) : ∃ η : GroundAssignment,
    η.types (.flex s.nextType) = a ∧ η.types (.flex (s.nextType + 1)) = b ∧
    η.modes (.flex s.nextMode) = m ∧
    SolverGround.AgreesBelow η ρ s.nextType s.nextMode := by
  refine ⟨((ρ.setType (.flex s.nextType) a).setType (.flex (s.nextType + 1)) b).setMode
    (.flex s.nextMode) m, ?_, ?_, ?_, ?_, ?_⟩
  · simp [GroundAssignment.setType, GroundAssignment.setMode]
  · simp [GroundAssignment.setType, GroundAssignment.setMode]
  · simp [GroundAssignment.setMode]
  · intro v hv
    have h0 : v ≠ .flex s.nextType := by intro he; subst v; exact Nat.lt_irrefl _ hv
    have h1 : v ≠ .flex (s.nextType + 1) := by intro he; subst v; simp [TypeVar.index] at hv; omega
    simp [GroundAssignment.setType, GroundAssignment.setMode, h0, h1]
  · intro v hv
    have h0 : v ≠ .flex s.nextMode := by intro he; subst v; exact Nat.lt_irrefl _ hv
    simp [GroundAssignment.setMode, GroundAssignment.setType, h0]

end ModalityInference
