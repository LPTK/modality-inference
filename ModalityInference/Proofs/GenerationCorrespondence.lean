import ModalityInference.Proofs.GenerationSupplies
import ModalityInference.Proofs.SolverSoundness

/-! Executable generation implements the independent relational generation rules. -/
namespace ModalityInference

theorem generate_closed_solves {fuel rhs nt nm r solveFuel result}
    (hg : generate fuel [] rhs {nextType := nt, nextMode := nm} = .success r)
    (hs : solveFrom solveFuel r.state.nextType r.state.nextMode r.state.constraints = .success result) :
    Solves r.state.constraints result.bounds result.substitution :=
  ⟨solveFrom_solution (generate_bounded hg (AlgorithmicContext.bounded_nil _ _)
      (Bounds.bounded_nil _ _)).2 hs,
    solveFrom_consistency (generate_flexible hg AlgorithmicContext.flexible_nil Bounds.flexible_nil).2 hs⟩

theorem Solves.perm {cs ds residual σ} (h : Solves cs residual σ) (hp : cs.Perm ds) :
    Solves ds residual σ := by
  refine ⟨fun c hc => h.1 c ?_, h.2⟩
  exact (hp.map σ.constraint).mem_iff.mpr hc

private theorem perm_append_chain {base xs ys cs ds : List Constraint}
    (hx : xs.Perm (base ++ cs)) (hy : ys.Perm (xs ++ ds)) :
    ys.Perm (base ++ (cs ++ ds)) := by
  simpa only [List.append_assoc] using hy.trans (hx.append_right ds)

theorem generate_correspondence {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    ∃ cs, Generates Γ t r.type cs ∧ r.state.constraints.Perm (s.constraints ++ cs) := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    case defn rhs body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i hclosed _ rr hr _ solved hsolve _ br hb
      obtain ⟨cr, hgr, hpr⟩ := ih hr
      obtain ⟨cb, hgb, hpb⟩ := ih hb
      refine ⟨cb, .defn (by simpa using hclosed) hgr ?_ hgb, hpb⟩
      exact (generate_closed_solves hr hsolve).perm (by simpa using hpr)
    case split x body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rx hx _ rb hb
      obtain ⟨cx, hcx, hpx⟩ := ih hx
      obtain ⟨cb, hcb, hpb⟩ := ih hb
      refine ⟨_, .split (splitContext_spec Γ _ _) hcx hcb, ?_⟩
      have hp := hpb.trans ((hpx.append_right _).append_right cb)
      apply hp.trans
      simpa only [List.append_assoc] using
        List.perm_append_comm.append_left (s.constraints ++ cx)
    case case x l r =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rx hx _ rl hl _ rr hr
      obtain ⟨cx, hcx, hpx⟩ := ih hx
      obtain ⟨cl, hcl, hpl⟩ := ih hl
      obtain ⟨cr, hcr, hpr⟩ := ih hr
      refine ⟨_, .case (splitContext_spec Γ _ _) hcx hcl hcr, ?_⟩
      simp only [InferenceState.emit, InferenceState.freshType, InferenceState.freshMode,
        List.perm_iff_count, List.count_append, List.count_cons, List.count_nil] at hpx hpl hpr ⊢
      intro a
      rw [hpr, hpl, hpx]
      omega
    case var i =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ scheme hl
      refine ⟨_, .var (lookupScheme_sound hl)
        (scheme.freshSubstitution_instantiates s.nextType s.nextMode false), ?_⟩
      simp [InferenceState.instantiate, Scheme.instantiate, List.append_assoc]
    case unit => cases h; exact ⟨[], .unit, by simp⟩
    case lam annotation body =>
      cases annotation
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      obtain ⟨cs, hc, hp⟩ := ih ‹generate n _ _ _ = .success _›
      refine ⟨_, .lam hc, ?_⟩
      simpa only [InferenceState.emit, List.append_assoc] using hp.append_right _
    case inl x | inr x | region x =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      all_goals cases h
      all_goals obtain ⟨cs, hc, hp⟩ := ih ‹generate n _ _ _ = .success _›
      all_goals first
        | refine ⟨_, .inl hc, ?_⟩
        | refine ⟨_, .inr hc, ?_⟩
        | refine ⟨_, .region hc, ?_⟩
      all_goals simpa only [InferenceState.emit, InferenceState.freshType,
        InferenceState.freshMode, List.append_assoc] using hp.append_right _
    case app x y =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rx hx _ ry hy
      obtain ⟨cx, hcx, hpx⟩ := ih hx
      obtain ⟨cy, hcy, hpy⟩ := ih hy
      refine ⟨_, .app (m := ry.state.freshType.2.freshMode.1)
        (splitContext_spec Γ _ _) hcx hcy, ?_⟩
      simpa only [InferenceState.emit, InferenceState.freshType,
        InferenceState.freshMode, List.append_assoc] using
          (perm_append_chain hpx hpy).append_right _
    case pair x y | stackPair x y =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      all_goals cases h
      all_goals rename_i _ rx hx _ ry hy hstack
      all_goals obtain ⟨cx, hcx, hpx⟩ := ih hx
      all_goals obtain ⟨cy, hcy, hpy⟩ := ih hy
      all_goals first
        | refine ⟨_, .pair (splitContext_spec Γ _ _) hcx hcy, ?_⟩
        | refine ⟨_, .stackPair (splitContext_spec Γ _ _) hcx hcy, ?_⟩
      all_goals simpa only [InferenceState.emit, InferenceState.freshType,
        InferenceState.freshMode, List.append_assoc] using
          (perm_append_chain hpx hpy).append_right _
    case reuse k x y =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rk hk _ rx hx _ ry hy
      obtain ⟨ck, hck, hpk⟩ := ih hk
      obtain ⟨cx, hcx, hpx⟩ := ih hx
      obtain ⟨cy, hcy, hpy⟩ := ih hy
      refine ⟨_, .reuse (n := ry.state.freshType.2.freshType.2.freshMode.2.freshMode.1)
        (splitContext_spec Γ _ _) (splitContext_spec _ _ _) hck hcx hcy, ?_⟩
      simpa only [InferenceState.emit, InferenceState.freshType,
        InferenceState.freshMode, List.append_assoc] using
          (perm_append_chain (perm_append_chain hpk hpx) hpy).append_right _

end ModalityInference
