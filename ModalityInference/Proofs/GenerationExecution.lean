import ModalityInference.Inference
import ModalityInference.Proofs.Annotations

/-! Executable generation preserves source syntax and accumulated constraints. -/
namespace ModalityInference

private theorem prefix_trans_append {xs ys zs ws : List Constraint}
    (h₁ : xs <+: ys) (h₂ : ys ++ zs <+: ws) : xs <+: ws :=
  (List.prefix_append_of_prefix h₁).trans h₂

theorem generate_erases {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    r.term.erase = t := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals simp [Term.erase, Term.mapAnnotation]
    all_goals simp only [AnnotatedTerm.substTypes, ← Term.erase.eq_def, Term.erase_mapAnnotation]
    all_goals solve_by_elim (config := {maxDepth := 12}) [ih, And.intro]

theorem generate_constraints_prefix {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    s.constraints <+: r.state.constraints := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals aesop (add safe forward ih) (add safe forward List.IsPrefix.trans)
      (add safe forward prefix_trans_append)
      (add safe apply List.prefix_append_of_prefix)
      (add norm unfold [InferenceState.freshType, InferenceState.freshMode,
        InferenceState.emit, InferenceState.instantiate])

theorem infer_erases {fuel Γ t result} (h : infer fuel Γ t = .success result) :
    result.elaborated.erase = t := by
  simp only [infer, bind, pure, RunResult.bind] at h
  repeat' (split at h <;> try contradiction)
  cases h
  simpa [AnnotatedTerm.substTypes] using
    generate_erases ‹generate fuel _ t _ = .success _›

end ModalityInference
