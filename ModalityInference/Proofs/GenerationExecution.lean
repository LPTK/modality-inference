import ModalityInference.Inference

/-! Executable generation preserves source syntax and accumulated constraints. -/
namespace ModalityInference

private theorem prefix_trans_append {xs ys zs ws : List Constraint}
    (h₁ : xs <+: ys) (h₂ : ys ++ zs <+: ws) : xs <+: ws :=
  (List.prefix_append_of_prefix h₁).trans h₂

theorem generate_term {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    r.term = t := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals simp only [Term.lam.injEq, Term.app.injEq, Term.pair.injEq,
      Term.stackPair.injEq, Term.inl.injEq, Term.inr.injEq, Term.defn.injEq,
      Term.split.injEq, Term.case.injEq, Term.reuse.injEq, Term.region.injEq, true_and]
    all_goals solve_by_elim (config := {maxDepth := 12}) [ih, And.intro]

@[simp] theorem Term.erase_raw (t : RawTerm) : t.erase = t := by
  induction t <;> simp_all [Term.erase, Term.mapAnnotation]

theorem generate_erases {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    r.term.erase = t := by
  simpa using generate_term h

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

theorem infer_term {fuel Γ t result} (h : infer fuel Γ t = .success result) :
    result.elaborated = t := by
  simp only [infer, bind, pure, RunResult.bind] at h
  repeat' (split at h <;> try contradiction)
  cases h
  exact generate_term ‹generate fuel _ t _ = .success _›

theorem infer_erases {fuel Γ t result} (h : infer fuel Γ t = .success result) :
    result.elaborated.erase = t := by
  simpa using infer_term h

end ModalityInference
