import ModalityInference.Proofs.GenerationHygiene
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

theorem generate_correspondence_hygienic {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    ∃ cs, ∃ hg : Generates Γ t r.type cs,
      r.state.constraints.Perm (s.constraints ++ cs) ∧
      (AlgorithmicContext.ModParamsBounded s.nextMode Γ → hg.Hygienic) := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    case defn rhs body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i hclosed _ rr hr _ solved hsolve _ br hb
      obtain ⟨cr, hgr, hpr, hhr⟩ := ih hr
      obtain ⟨cb, hgb, hpb, hhb⟩ := ih hb
      have hsol := (generate_closed_solves hr hsolve).perm (by simpa using hpr)
      refine ⟨cb, .defn (by simpa using hclosed) hgr hsol hgb, hpb, ?_⟩
      intro hΓ
      refine .defn (by simpa using hclosed) hsol
        (hhr (AlgorithmicContext.modParamsBounded_nil _)) (hhb ?_)
      refine AlgorithmicContext.modParamsBounded_binding.mpr ⟨?_, ?_⟩
      · intro a ha
        cases ha
        exact generate_closed_modParamsBounded hr hsolve
      · exact hΓ.mono ((generate_counters hr).2.trans (solveFrom_counters hsolve).2)
    case split x body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rx hx _ rb hb
      obtain ⟨cx, hcx, hpx, hhx⟩ := ih hx
      obtain ⟨cb, hcb, hpb, hhb⟩ := ih hb
      refine ⟨_, .split (splitContext_spec Γ _ _) hcx hcb, ?_, ?_⟩
      · have hp := hpb.trans ((hpx.append_right _).append_right cb)
        apply hp.trans
        simpa only [List.append_assoc] using
          List.perm_append_comm.append_left (s.constraints ++ cx)
      · intro hΓ
        have hc := splitContext_modParamsBounded hΓ x.freeVars (body.freeVars 3)
        refine .split (splitContext_spec Γ _ _) (hhx hc.1) (hhb ?_)
        simpa [InferenceState.emit, InferenceState.freshType, InferenceState.freshMode,
          Scheme.ModParamsBounded, Scheme.mono] using
            hc.2.mono ((generate_counters hx).2.trans (Nat.le_succ _))
    case case x l r =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rx hx _ rl hl _ rr hr
      obtain ⟨cx, hcx, hpx, hhx⟩ := ih hx
      obtain ⟨cl, hcl, hpl, hhl⟩ := ih hl
      obtain ⟨cr, hcr, hpr, hhr⟩ := ih hr
      refine ⟨_, .case (splitContext_spec Γ _ _) hcx hcl hcr, ?_, ?_⟩
      · simp only [InferenceState.emit, InferenceState.freshType, InferenceState.freshMode,
          List.perm_iff_count, List.count_append, List.count_cons, List.count_nil] at hpx hpl hpr ⊢
        intro a
        rw [hpr, hpl, hpx]
        omega
      · intro hΓ
        have hc := splitContext_modParamsBounded hΓ x.freeVars (l.freeVars 1 ∪ r.freeVars 1)
        refine .case (splitContext_spec Γ _ _) (hhx hc.1) (hhl ?_) (hhr ?_)
        · simpa [InferenceState.emit, InferenceState.freshType, InferenceState.freshMode,
            Scheme.ModParamsBounded, Scheme.mono] using
              hc.2.mono ((generate_counters hx).2.trans (Nat.le_succ _))
        · simpa [Scheme.ModParamsBounded, Scheme.mono] using
            hc.2.mono ((generate_counters hx).2.trans
              ((Nat.le_succ _).trans (generate_counters hl).2))
    case var i =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ scheme hl
      refine ⟨_, .var (lookupScheme_sound hl)
        (scheme.freshSubstitution_instantiates s.nextType s.nextMode false), ?_, ?_⟩
      · simp [InferenceState.instantiate, Scheme.instantiate, List.append_assoc]
      · exact fun _ => .var (lookupScheme_sound hl)
          (scheme.freshSubstitution_instantiates s.nextType s.nextMode false)
    case unit => cases h; exact ⟨[], .unit, by simp, fun _ => .unit⟩
    case lam annotation body =>
      cases annotation
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      obtain ⟨cs, hc, hp, hh⟩ := ih ‹generate n _ _ _ = .success _›
      refine ⟨_, .lam hc, ?_, ?_⟩
      · simpa only [InferenceState.emit, List.append_assoc] using hp.append_right _
      · intro hΓ
        refine .lam hΓ.fresh (hh ?_)
        simpa [InferenceState.freshType, InferenceState.freshMode,
          Scheme.ModParamsBounded, Scheme.mono] using hΓ.mono (Nat.le_succ _)
    case inl x | inr x | region x =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      all_goals cases h
      all_goals obtain ⟨cs, hc, hp, hh⟩ := ih ‹generate n _ _ _ = .success _›
      all_goals first
        | refine ⟨_, .inl hc, ?_, ?_⟩
        | refine ⟨_, .inr hc, ?_, ?_⟩
        | refine ⟨_, .region hc, ?_, ?_⟩
      all_goals try solve | simpa only [InferenceState.emit, InferenceState.freshType,
        InferenceState.freshMode, List.append_assoc] using hp.append_right _
      all_goals intro hΓ
      all_goals first
        | exact .inl (hh hΓ)
        | exact .inr (hh hΓ)
        | exact .region (hh hΓ)
    case app x y =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rx hx _ ry hy
      obtain ⟨cx, hcx, hpx, hhx⟩ := ih hx
      obtain ⟨cy, hcy, hpy, hhy⟩ := ih hy
      refine ⟨_, .app (m := ry.state.freshType.2.freshMode.1)
        (splitContext_spec Γ _ _) hcx hcy, ?_, ?_⟩
      · simpa only [InferenceState.emit, InferenceState.freshType,
          InferenceState.freshMode, List.append_assoc] using
            (perm_append_chain hpx hpy).append_right _
      · intro hΓ
        have hc := splitContext_modParamsBounded hΓ x.freeVars y.freeVars
        exact .app (splitContext_spec Γ _ _) (hhx hc.1)
          (hhy (hc.2.mono (generate_counters hx).2))
    case pair x y | stackPair x y =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      all_goals cases h
      all_goals rename_i _ rx hx _ ry hy hstack
      all_goals obtain ⟨cx, hcx, hpx, hhx⟩ := ih hx
      all_goals obtain ⟨cy, hcy, hpy, hhy⟩ := ih hy
      all_goals first
        | refine ⟨_, .pair (splitContext_spec Γ _ _) hcx hcy, ?_, ?_⟩
        | refine ⟨_, .stackPair (splitContext_spec Γ _ _) hcx hcy, ?_, ?_⟩
      all_goals try solve | simpa only [InferenceState.emit, InferenceState.freshType,
        InferenceState.freshMode, List.append_assoc] using
          (perm_append_chain hpx hpy).append_right _
      all_goals intro hΓ
      all_goals have hc := splitContext_modParamsBounded hΓ x.freeVars y.freeVars
      all_goals first
        | exact .pair (splitContext_spec Γ _ _) (hhx hc.1)
            (hhy (hc.2.mono (generate_counters hx).2))
        | exact .stackPair (splitContext_spec Γ _ _) (hhx hc.1)
            (hhy (hc.2.mono (generate_counters hx).2))
    case reuse k x y =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i _ rk hk _ rx hx _ ry hy
      obtain ⟨ck, hck, hpk, hhk⟩ := ih hk
      obtain ⟨cx, hcx, hpx, hhx⟩ := ih hx
      obtain ⟨cy, hcy, hpy, hhy⟩ := ih hy
      refine ⟨_, .reuse (n := ry.state.freshType.2.freshType.2.freshMode.2.freshMode.1)
        (splitContext_spec Γ _ _) (splitContext_spec _ _ _) hck hcx hcy, ?_, ?_⟩
      · simpa only [InferenceState.emit, InferenceState.freshType,
          InferenceState.freshMode, List.append_assoc] using
            (perm_append_chain (perm_append_chain hpk hpx) hpy).append_right _
      · intro hΓ
        have h1 := splitContext_modParamsBounded hΓ k.freeVars (x.freeVars ∪ y.freeVars)
        have h2 := splitContext_modParamsBounded h1.2 x.freeVars y.freeVars
        exact .reuse (splitContext_spec Γ _ _) (splitContext_spec _ _ _)
          (hhk h1.1) (hhx (h2.1.mono (generate_counters hk).2))
          (hhy (h2.2.mono ((generate_counters hk).2.trans (generate_counters hx).2)))


theorem generate_correspondence {fuel Γ t s r} (h : generate fuel Γ t s = .success r) :
    ∃ cs, Generates Γ t r.type cs ∧ r.state.constraints.Perm (s.constraints ++ cs) := by
  obtain ⟨cs, hg, hp, _⟩ := generate_correspondence_hygienic h
  exact ⟨cs, hg, hp⟩

/-- The public inference initializer supplies the lock-scope invariant for every
input context; no extra condition on source syntax or its schemes is needed. -/
theorem generate_initial_hygienic {fuel t r} {Γ : Context}
    (h : generate fuel (Γ.map ContextEntry.binding) t (initialInferenceState Γ) = .success r) :
    ∃ cs, ∃ hg : Generates (Γ.map ContextEntry.binding) t r.type cs,
      r.state.constraints.Perm cs ∧ hg.Hygienic := by
  obtain ⟨cs, hg, hp, hh⟩ := generate_correspondence_hygienic h
  exact ⟨cs, hg, by simpa [initialInferenceState] using hp,
    hh (initialInferenceState_modParamsBounded Γ)⟩

end ModalityInference
