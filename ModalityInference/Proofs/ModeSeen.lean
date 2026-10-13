import ModalityInference.Proofs.ModeOrientation
import ModalityInference.Proofs.SolverDefinedness

/-! Justification of visited modality constraints in the complete worklist. -/
namespace ModalityInference

def Constraint.IsModality : Constraint → Prop
  | .mode _ _ | .defined _ => True
  | _ => False

@[simp] theorem Constraint.normalize_isModality (c : Constraint) :
    c.normalize.IsModality ↔ c.IsModality := by
  cases c <;> rfl

theorem Constraint.modality_substitution {c : Constraint} (hc : c.IsModality)
    {σ : Substitution} (hm : σ.modes = []) : σ.constraint c = c := by
  have he : σ.mode = ModExpr.var := by
    funext v
    cases v <;> simp [Substitution.mode, hm]
  cases c <;> simp_all [Constraint.IsModality, Substitution.constraint, Constraint.subst]

def ModeOrientation.EntailsBelow (Δ cs : Bounds) (k : ModeOrientation.Rank) : Prop :=
  ∀ c ∈ cs, c.IsModality → ModeOrientation.Lt (ModeOrientation.rank c.normalize) k → Entails Δ c

/-- A visited modality constraint depends only on retained bounds and strictly
smaller normalized modality obligations, never on another occurrence of itself. -/
structure SolverState.ModeInvariant (s : SolverState) : Prop where
  modes : s.substitution.modes = []
  seen : ∀ c ∈ s.seen, c.IsModality → ∀ Δ, EntailsAll Δ s.bounds →
    ModeOrientation.EntailsBelow Δ s.pending (ModeOrientation.rank c) → Entails Δ c

theorem SolverState.ModeInvariant.mono {s t : SolverState} (hs : s.ModeInvariant)
    (hm : t.substitution.modes = []) (hb : s.bounds ⊆ t.bounds)
    (hp : s.pending ⊆ t.pending) (hv : t.seen ⊆ s.seen) : t.ModeInvariant :=
  ⟨hm, fun c hc hcm Δ hΔ hsmall => hs.seen c (hv hc) hcm Δ
    (fun d hd => hΔ d (hb hd)) (fun d hd hdm hlt => hsmall d (hp hd) hdm hlt)⟩

theorem SolverState.ModeInvariant.emit {s : SolverState} (hs : s.ModeInvariant)
    (r : RewriteRule) (cs : Bounds) : (s.emit r cs).ModeInvariant :=
  hs.mono (t := s.emit r cs) hs.modes (by simp [SolverState.emit])
    (fun _ hc => List.mem_append_right _ hc) (by simp [SolverState.emit])

theorem SolverState.ModeInvariant.retain {s : SolverState} (hs : s.ModeInvariant)
    (r : RewriteRule) (c : Constraint) : (s.retain r c).ModeInvariant := by
  apply hs.mono (t := s.retain r c) hs.modes ?_ (by simp [SolverState.retain])
    (by simp [SolverState.retain])
  simp only [SolverState.retain]
  split <;> simp

theorem SolverState.ModeInvariant.advance {s t : SolverState} (hs : s.ModeInvariant)
    {c rest} (hp : s.pending = c :: rest) (hm : t.substitution.modes = [])
    (hb : s.bounds ⊆ t.bounds) (hr : rest ⊆ t.pending)
    (hv : t.seen ⊆ (s.substitution.constraint c).normalize :: s.seen)
    (hc : (s.substitution.constraint c).normalize.IsModality →
      ∀ Δ, EntailsAll Δ t.bounds → ModeOrientation.EntailsBelow Δ t.pending
        (ModeOrientation.rank (s.substitution.constraint c).normalize) →
        Entails Δ (s.substitution.constraint c).normalize) : t.ModeInvariant := by
  refine ⟨hm, ?_⟩
  intro d hd hdm Δ hΔ hdsmall
  rcases List.mem_cons.mp (hv hd) with rfl | hd
  · exact hc hdm Δ hΔ hdsmall
  · apply hs.seen d hd hdm Δ (fun e he => hΔ e (hb he))
    intro e he hem hel
    rw [hp] at he
    rcases List.mem_cons.mp he with rfl | he
    · have hn := congrArg Constraint.normalize (Constraint.modality_substitution hem hs.modes)
      apply (Constraint.normalize_entails e Δ).mp
      rw [← hn]
      apply hc (by simpa only [hn, Constraint.normalize_isModality] using hem) Δ hΔ
      intro e he hem hel'
      apply hdsmall e he hem
      exact ModeOrientation.lt_trans hel' (by simpa only [hn] using hel)
    · exact hdsmall e (hr he) hem hel

theorem stepMode_modality_pending {s a b t} (h : stepMode s a b = .success t) :
    ∀ c ∈ t.pending, c ∈ s.pending ∨ c.IsModality := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp [SolverState.emit, SolverState.retain, recordModeBound,
    Constraint.IsModality, or_imp, forall_and]
  all_goals exact fun _ hc => Or.inl hc

theorem stepMode_separate_pending {s a b t} (h : stepMode s a b = .success t) :
    ∃ u, stepMode {s with pending := []} a b = .success u ∧
      t.pending = u.pending ++ s.pending ∧ t.bounds = u.bounds := by
  simp only [stepMode, bind, pure, RunResult.bind] at h ⊢
  repeat' split at h
  all_goals cases h
  all_goals simp only [*, SolverState.emit, SolverState.retain, recordModeBound, List.append_nil]
  all_goals exact ⟨_, rfl, rfl, rfl⟩

theorem stepMode_entails_below {s a b t Δ} (h : stepMode s a b = .success t)
    (hb : EntailsAll Δ t.bounds)
    (hp : ∀ c ∈ t.pending, c.IsModality →
      ModeOrientation.Lt (ModeOrientation.rank c.normalize) (ModeOrientation.rank (.mode a b)) →
      Entails Δ c) : Entails Δ (.mode a b) := by
  obtain ⟨u, hu, hpend, hbound⟩ := stepMode_separate_pending h
  apply stepMode_entails hu
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · apply hp c (hpend ▸ List.mem_append_left _ hc)
    · exact (stepMode_modality_pending hu c hc).resolve_left (by simp)
    · exact (ModeOrientation.stepMode_normalized_decreases hu c hc).resolve_left (by simp)
  · exact hb c (hbound ▸ hc)

theorem stepMode_frame {s a b t} (h : stepMode s a b = .success t) :
    s.pending ⊆ t.pending ∧ s.bounds ⊆ t.bounds ∧ t.seen = s.seen := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp [SolverState.emit, SolverState.retain, recordModeBound]
  all_goals first | (split <;> simp) | exact fun _ hc => by simp [hc]

theorem SolverState.skeleton_frame (s : SolverState) (a : Ty) :
    (s.skeleton a).2.pending = s.pending ∧ (s.skeleton a).2.bounds = s.bounds ∧
      (s.skeleton a).2.seen = s.seen := by
  cases a <;> exact ⟨rfl, rfl, rfl⟩

theorem stepType_frame {s a b t} (h : stepType s a b = .success t) :
    s.pending ⊆ t.pending ∧ s.bounds ⊆ t.bounds ∧ t.seen = s.seen := by
  simp only [stepType, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp [SolverState.emit, SolverState.retain]
  all_goals first | (split <;> simp) | (exact fun _ hc => by simp [hc]) | skip
  all_goals simp [(s.skeleton_frame _).1, (s.skeleton_frame _).2.1, (s.skeleton_frame _).2.2]

theorem SolverState.ModeInvariant.drop_seen {s : SolverState} (hs : s.ModeInvariant)
    {c rest} (hp : s.pending = c :: rest)
    (hv : (s.substitution.constraint c).normalize ∈ s.seen) :
    {s with pending := rest}.ModeInvariant := by
  apply hs.advance (t := {s with pending := rest}) hp hs.modes (by simp) (by simp) (by simp)
  intro hcm Δ hb hsmall
  apply hs.seen _ hv hcm Δ hb
  intro e he hem hel
  rw [hp] at he
  rcases List.mem_cons.mp he with rfl | he
  · have hn := congrArg Constraint.normalize (Constraint.modality_substitution hem hs.modes)
    simp only [hn, ModeOrientation.Lt, Prod.lex_def, lt_self_iff_false, false_or, and_false] at hel
  · exact hsmall e he hem hel

theorem SolverState.ModeInvariant.advance_nonmode {s : SolverState} (hs : s.ModeInvariant)
    {c rest} (hp : s.pending = c :: rest)
    (hc : ¬(s.substitution.constraint c).normalize.IsModality) :
    {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}.ModeInvariant := by
  apply hs.advance
    (t := {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}) hp hs.modes
    (by simp) (by simp) (by simp)
  exact fun h => False.elim (hc h)

theorem stepType_modeInvariant {s a b t} (hs : s.ModeInvariant)
    (h : stepType s a b = .success t) : t.ModeInvariant := by
  obtain ⟨hp, hb, hv⟩ := stepType_frame h
  exact hs.mono (by rw [stepType_substitution h]; exact hs.modes) hb hp (by simp [hv])

theorem stepMode_advance_modeInvariant {s t : SolverState} {c rest a b} (hs : s.ModeInvariant)
    (hp : s.pending = c :: rest) (he : (s.substitution.constraint c).normalize = .mode a b)
    (h : stepMode
      {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen} a b = .success t) :
    t.ModeInvariant := by
  obtain ⟨hp', hb, hv⟩ := stepMode_frame h
  apply hs.advance hp (by rw [stepMode_substitution h]; exact hs.modes) hb hp' (by simp [hv])
  rw [he]
  exact fun _ Δ hΔ hsmall => stepMode_entails_below h hΔ hsmall

theorem solverStep_modeInvariant {s t} (hs : s.ModeInvariant)
    (h : solverStep s = .success t) : t.ModeInvariant := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals first
    | exact stepType_modeInvariant
        (hs.advance_nonmode ‹s.pending = _ :: _› (by simp_all [Constraint.IsModality])) h
    | (refine stepMode_advance_modeInvariant hs ‹s.pending = _ :: _› ?_ h; assumption)
    | skip
  all_goals cases h
  all_goals try exact hs
  all_goals try apply SolverState.ModeInvariant.emit
  all_goals first
    | (apply hs.advance_nonmode ‹s.pending = _ :: _›; simp_all [Constraint.IsModality]; done)
    | exact hs.drop_seen ‹s.pending = _ :: _› (by simpa using ‹s.seen.contains _ = true›)
    | skip
  case h_2.isFalse.isFalse.refl =>
    exact ⟨hs.modes, by simp⟩
  case h_4.isTrue.isTrue.refl.hs =>
    rename_i pending c rest hp hseen normalized a he hfree heval
    apply hs.advance hp
    · exact hs.modes
    · simp
    · simp
    · simp
    · intro _ Δ _ _
      rw [he]
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp heval
      exact fun _ _ => Option.isSome_iff_exists.mpr ⟨m, a.eval_refinement (by simp) hm⟩
  case h_4.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a he hfree
    apply (hs.retain .defined (s.substitution.constraint c).normalize).advance hp
    · exact hs.modes
    · simp [SolverState.retain]
    · simp [SolverState.retain]
    · simp [SolverState.retain]
    · intro _ Δ hΔ _
      exact hΔ _ (s.mem_retain .defined (s.substitution.constraint c).normalize)

theorem runWorklist_modeInvariant {fuel s t} (hs : s.ModeInvariant)
    (h : runWorklist fuel s = .success t) : t.ModeInvariant ∧ t.pending = [] := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact ⟨hs, by simpa using ‹t.pending.isEmpty = true›⟩
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_modeInvariant hs ht) h

theorem runSolver_modeInvariant {fuel s t} (hs : s.ModeInvariant)
    (h : runSolver fuel s = .success t) : t.ModeInvariant ∧ t.pending = [] := by
  have hσ := runSolver_input_acyclic h
  simp only [runSolver, (s.substitution.checkAcyclic_iff).mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind] at h
  split at h <;> first | exact runWorklist_modeInvariant hs h | cases h

theorem SolverState.ModeInvariant.finished_seen {s : SolverState} (hs : s.ModeInvariant)
    (hp : s.pending = []) {c Δ} (hc : c ∈ s.seen) (hm : c.IsModality)
    (hΔ : EntailsAll Δ s.bounds) : Entails Δ c :=
  hs.seen c hc hm Δ hΔ (by simp [ModeOrientation.EntailsBelow, hp])

theorem SolverState.ModeInvariant.duplicate_entails {s : SolverState} (hs : s.ModeInvariant)
    {c rest Δ} (hp : s.pending = c :: rest) (hc : c.IsModality)
    (hv : (s.substitution.constraint c).normalize ∈ s.seen)
    (hΔ : EntailsAll Δ (rest ++ s.bounds)) : Entails Δ c := by
  have hdrop := hs.drop_seen hp hv
  have hn := congrArg Constraint.normalize (Constraint.modality_substitution hc hs.modes)
  apply (Constraint.normalize_entails c Δ).mp
  rw [← hn]
  apply hdrop.seen _ hv (by simpa only [hn, Constraint.normalize_isModality] using hc) Δ
    (fun d hd => hΔ d (List.mem_append_right _ hd))
  exact fun d hd _ _ => hΔ d (List.mem_append_left _ hd)

theorem runSolver_seen_entails {fuel s t Δ} (hm : s.substitution.modes = [])
    (hv : s.seen = []) (h : runSolver fuel s = .success t)
    (hΔ : EntailsAll Δ t.bounds) : ∀ c ∈ t.seen, c.IsModality → Entails Δ c := by
  obtain ⟨ht, hp⟩ := runSolver_modeInvariant ⟨hm, by simp [hv]⟩ h
  exact fun c hc hcm => ht.finished_seen hp hc hcm hΔ

end ModalityInference
