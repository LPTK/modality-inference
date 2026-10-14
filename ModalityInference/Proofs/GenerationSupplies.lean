import ModalityInference.Proofs.GenerationExecution
import ModalityInference.Proofs.GenerationContexts
import ModalityInference.Proofs.SolverCounters
import ModalityInference.Proofs.SolverFlexible

/-! The generator keeps all generated identifiers below its allocation counters. -/
namespace ModalityInference

theorem generate_counters {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    s.nextType ≤ r.state.nextType ∧ s.nextMode ≤ r.state.nextMode := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals simp only [InferenceState.freshType, InferenceState.freshMode,
      InferenceState.emit, InferenceState.instantiate] at *
    all_goals grind only [→ solveFrom_counters]

theorem splitContext_flexible {Γ : AlgorithmicContext} (hΓ : Γ.Flexible) (X Y : Finset Nat) :
    AlgorithmicContext.Flexible (splitContext X Y Γ).1 ∧
      AlgorithmicContext.Flexible (splitContext X Y Γ).2 :=
  (splitContext_spec Γ X Y).flexible hΓ

theorem generate_flexible {fuel Γ t s r} (h : generate fuel Γ t s = .success r)
    (hΓ : AlgorithmicContext.Flexible Γ) (hs : s.constraints.Flexible) :
    r.type.Flexible ∧ r.state.constraints.Flexible := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    case defn rhs body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i hclosed _ rr hr _ solved hsolve _ br hb
      have hrr := ih hr AlgorithmicContext.flexible_nil Bounds.flexible_nil
      have hsol := solveFrom_flexible hrr.2 hsolve
      apply ih hb ?_ hs
      simpa [ContextEntry.Flexible, Scheme.Flexible, Scheme.generalize] using
        And.intro (And.intro (hsol.2.ty hrr.1) hsol.1) hΓ
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals try have hv :=
      (lookupScheme_flexible hΓ ‹lookupScheme Γ _ = .success _›).instantiate s.nextType s.nextMode
    all_goals simp [InferenceState.freshType, InferenceState.freshMode,
      InferenceState.emit, InferenceState.instantiate, TypeExpr.Flexible, ModExpr.Flexible,
      Constraint.Flexible, Bounds.flexible_append, Bounds.flexible_cons, Bounds.flexible_nil,
      ModExpr.bottom, Scheme.mono] at *
    all_goals grind only [splitContext_flexible, AlgorithmicContext.flexible_cons,
      TypeExpr.Flexible.wellFormedBounds,
      ContextEntry.Flexible, Scheme.Flexible, TypeExpr.Flexible, ModExpr.Flexible,
      Constraint.Flexible, Option.mem_def,
      Bounds.flexible_append, Bounds.flexible_cons, Bounds.flexible_nil]

theorem splitContext_bounded {Γ : AlgorithmicContext} {nt nm} (hΓ : Γ.Bounded nt nm)
    (X Y : Finset Nat) :
    AlgorithmicContext.Bounded nt nm (splitContext X Y Γ).1 ∧
      AlgorithmicContext.Bounded nt nm (splitContext X Y Γ).2 :=
  (splitContext_spec Γ X Y).bounded hΓ

theorem generate_bounded {fuel Γ t s r} (h : generate fuel Γ t s = .success r)
    (hΓ : AlgorithmicContext.Bounded s.nextType s.nextMode Γ)
    (hs : s.constraints.Bounded s.nextType s.nextMode) :
    r.type.Bounded r.state.nextType r.state.nextMode ∧
      r.state.constraints.Bounded r.state.nextType r.state.nextMode := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    case defn rhs body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i hclosed _ rr hr _ solved hsolve _ br hb
      have hrr := ih hr (AlgorithmicContext.bounded_nil _ _) (Bounds.bounded_nil _ _)
      have hsol := solveFrom_fresh hrr.2 hsolve
      have hcount := solveFrom_counters hsolve
      have hstart := generate_counters hr
      apply ih hb ?_ (hs.mono (hstart.1.trans hcount.1) (hstart.2.trans hcount.2))
      simpa [ContextEntry.Bounded, Scheme.Bounded, Scheme.generalize] using
        And.intro (And.intro (hsol.2.ty (hrr.1.mono hcount.1 hcount.2)) hsol.1)
          (hΓ.mono (hstart.1.trans hcount.1) (hstart.2.trans hcount.2))
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals try have hv :=
      (lookupScheme_bounded hΓ ‹lookupScheme Γ _ = .success _›).instantiate
    all_goals simp [InferenceState.freshType, InferenceState.freshMode,
      InferenceState.emit, InferenceState.instantiate, TypeExpr.Bounded, ModExpr.Bounded,
      Constraint.Bounded, ModExpr.bottom, Scheme.mono, TypeVar.index, ModVar.index] at *
    all_goals grind only [→ generate_counters, splitContext_bounded,
      TypeExpr.Bounded.wellFormedBounds,
      AlgorithmicContext.bounded_cons, ContextEntry.Bounded, Scheme.Bounded,
      TypeExpr.Bounded, ModExpr.Bounded, Constraint.Bounded, TypeVar.index, ModVar.index,
      Option.mem_def, Bounds.bounded_append, Bounds.bounded_cons, Bounds.bounded_nil,
      AlgorithmicContext.Bounded.mono, TypeExpr.Bounded.mono, Bounds.Bounded.mono]

end ModalityInference
