import ModalityInference.Proofs.TypeOrientation
import ModalityInference.Proofs.SolverUnbound

/-! Noncircular discharge of visited type constraints, allowing the intermediate
state between fresh shape expansion and equality elimination. -/
namespace ModalityInference

def TypeOrientation.EntailsBelow (Δ cs : Bounds) (k : Nat) : Prop :=
  ∀ c ∈ cs, c.typeRank < k → Entails Δ c

structure SolverState.TypeInvariant (s : SolverState) : Prop where
  seen : ∀ c ∈ s.seen, 0 < c.typeRank → ∀ Δ, EntailsAll Δ s.bounds →
    TypeOrientation.EntailsBelow Δ s.pending c.typeRank → Entails Δ c

def SolverState.TypeReady (s : SolverState) : Prop := s.TypeInvariant ∨ s.ClearsSeen

theorem SolverState.skeleton_with_pending (s : SolverState) (a : Ty) (cs : Bounds) :
    ({s with pending := cs}.skeleton a) =
      ((s.skeleton a).1, {(s.skeleton a).2 with pending := cs}) := by
  cases a <;> rfl

theorem stepType_separate_pending {s a b t} (h : stepType s a b = .success t) :
    ∃ u, stepType {s with pending := []} a b = .success u ∧
      t.pending = u.pending ++ s.pending ∧ t.bounds = u.bounds := by
  simp only [stepType, bind, pure, RunResult.bind, SolverState.skeleton_with_pending] at h ⊢
  repeat' split at h
  all_goals cases h
  all_goals try simp only [*]
  all_goals refine ⟨_, rfl, ?_, rfl⟩
  all_goals simp [SolverState.emit, SolverState.retain,
    (s.skeleton_frame a.outer.1).1, (s.skeleton_frame b.outer.1).1]

theorem stepType_entails_below_or_clears {s : SolverState} (hs : s.Fresh)
    {a b t} (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hf : ∀ k ∈ s.substitution.types.map Prod.fst,
      .flex k ∉ a.typeVars ∧ .flex k ∉ b.typeVars)
    (h : stepType s a b = .success t) :
    t.ClearsSeen ∨ ∀ Δ, EntailsAll Δ t.bounds →
      TypeOrientation.EntailsBelow Δ t.pending (Constraint.sub a b).typeRank →
      Entails Δ (.sub a b) := by
  rcases stepType_prefix_decreases_or_clears hs ha hb hf h with ht | ⟨cs, hp, hd⟩
  · exact Or.inl ht
  · obtain ⟨u, hu, hup, hub⟩ := stepType_separate_pending h
    have he : cs = u.pending := List.append_cancel_right (hp.symm.trans hup)
    exact Or.inr fun Δ hb hsmall => stepType_entails hu fun c hc =>
      (List.mem_append.mp hc).elim
        (fun hc => hsmall c (by simpa only [hup] using List.mem_append_left s.pending hc)
          (hd c (by simpa only [he] using hc)))
        (fun hc => hb c (by simpa only [hub] using hc))

theorem SolverState.TypeInvariant.advance {s t : SolverState} (hs : s.TypeInvariant)
    {c rest} (hp : s.pending = c :: rest) (hfix : s.substitution.constraint c = c)
    (hb : s.bounds ⊆ t.bounds) (hr : rest ⊆ t.pending)
    (hv : t.seen ⊆ (s.substitution.constraint c).normalize :: s.seen)
    (hc : ∀ Δ k, 0 < k → (s.substitution.constraint c).normalize.typeRank ≤ k →
      EntailsAll Δ t.bounds → TypeOrientation.EntailsBelow Δ t.pending k →
      Entails Δ (s.substitution.constraint c).normalize) : t.TypeInvariant := by
  refine ⟨fun d hd hpos Δ hΔ hsmall => ?_⟩
  rcases List.mem_cons.mp (hv hd) with rfl | hd
  · exact hc Δ _ hpos (Nat.le_refl _) hΔ hsmall
  · apply hs.seen d hd hpos Δ (fun e he => hΔ e (hb he))
    intro e he hel
    rcases List.mem_cons.mp (hp ▸ he) with rfl | he
    · exact (Constraint.normalize_entails e Δ).mp (by
        simpa only [hfix] using hc Δ d.typeRank hpos
          (by simpa only [hfix, Constraint.normalize_typeRank] using Nat.le_of_lt hel) hΔ hsmall)
    · exact hsmall e (hr he) hel

theorem SolverState.TypeInvariant.empty {s : SolverState} (hs : s.seen = []) : s.TypeInvariant :=
  ⟨by simp [hs]⟩

theorem SolverState.TypeInvariant.mono {s t : SolverState} (hs : s.TypeInvariant)
    (hb : s.bounds ⊆ t.bounds) (hp : s.pending ⊆ t.pending) (hv : t.seen ⊆ s.seen) :
    t.TypeInvariant :=
  ⟨fun c hc hpos Δ hΔ hsmall => hs.seen c (hv hc) hpos Δ
    (fun d hd => hΔ d (hb hd)) (fun d hd hl => hsmall d (hp hd) hl)⟩

theorem SolverState.TypeInvariant.drop_seen {s : SolverState} (hs : s.TypeInvariant)
    (hm : s.ModeInvariant) {c rest} (hp : s.pending = c :: rest)
    (hfix : s.substitution.constraint c = c)
    (hv : (s.substitution.constraint c).normalize ∈ s.seen) :
    {s with pending := rest}.TypeInvariant := by
  apply hs.advance (t := {s with pending := rest}) hp hfix (by simp) (by simp) (by simp)
  intro Δ k hk hle hΔ hsmall
  by_cases hcm : (s.substitution.constraint c).normalize.IsModality
  · exact (hm.drop_seen hp hv).seen _ hv hcm Δ hΔ fun d hd hdm _ =>
      hsmall d hd (by simpa only [(d.typeRank_zero).mpr hdm] using hk)
  · apply hs.seen _ hv (Nat.pos_of_ne_zero fun hz => hcm ((Constraint.typeRank_zero _).mp hz)) Δ hΔ
    intro d hd hl
    rcases List.mem_cons.mp (hp ▸ hd) with rfl | hd
    · simp only [hfix, Constraint.normalize_typeRank, Nat.lt_irrefl] at hl
    · exact hsmall d hd (hl.trans_le hle)

theorem stepType_advance_typeReady {s t : SolverState} (hs : s.TypeInvariant)
    (hu : s.Unbound) (hf : s.Fresh) (hσ : s.substitution.Acyclic)
    {c rest a b} (hp : s.pending = c :: rest)
    (he : (s.substitution.constraint c).normalize = .sub a b)
    (h : stepType {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}
      a b = .success t) : t.TypeReady := by
  rcases stepType_entails_below_or_clears
    (s := {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen})
    (hf.advance hp (by simp)) (he ▸ hf.normalized_head hp).1 (he ▸ hf.normalized_head hp).2
    (s.substitution.normalized_sub_fresh hσ he) h with ht | ht
  · exact Or.inr ht
  · obtain ⟨hr, hb, hv⟩ := stepType_frame h
    refine Or.inl (hs.advance hp ((hu.pending c (by simp [hp])).fixed hu.modes)
      hb hr (by simp [hv]) ?_)
    rw [he]
    exact fun Δ k _ hle hΔ hsmall => ht Δ hΔ fun d hd hl => hsmall d hd (hl.trans_le hle)

theorem stepMode_entails_typeBelow {s a b t Δ k} (h : stepMode s a b = .success t)
    (hk : 0 < k) (hb : EntailsAll Δ t.bounds)
    (hp : TypeOrientation.EntailsBelow Δ t.pending k) : Entails Δ (.mode a b) := by
  obtain ⟨u, hu, hpend, hbound⟩ := stepMode_separate_pending h
  apply stepMode_entails hu
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · apply hp c (hpend ▸ List.mem_append_left _ hc)
    simpa only [c.typeRank_zero.mpr
      ((stepMode_modality_pending hu c hc).resolve_left (by simp))] using hk
  · exact hb c (hbound ▸ hc)

theorem stepMode_advance_typeInvariant {s t : SolverState} (hs : s.TypeInvariant)
    (hu : s.Unbound) {c rest a b} (hp : s.pending = c :: rest)
    (he : (s.substitution.constraint c).normalize = .mode a b)
    (h : stepMode {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}
      a b = .success t) : t.TypeInvariant := by
  obtain ⟨hr, hb, hv⟩ := stepMode_frame h
  apply hs.advance hp ((hu.pending c (by simp [hp])).fixed hu.modes) hb hr (by simp [hv])
  rw [he]
  exact fun Δ k hk _ hΔ hsmall => stepMode_entails_typeBelow h hk hΔ hsmall

theorem solverStep_typeReady {s t} (hs : s.TypeReady) (hm : s.ModeInvariant)
    (hu : s.Unbound) (hf : s.Fresh) (hσ : s.substitution.Acyclic)
    (h : solverStep s = .success t) : t.TypeReady := by
  rcases hs with hs | ⟨c, rest, hp, hv, hclear⟩
  · simp only [solverStep, bind, pure, RunResult.bind] at h
    repeat' split at h
    all_goals first
      | exact stepType_advance_typeReady hs hu hf hσ ‹s.pending = _ :: _› (by assumption) h
      | exact Or.inl (stepMode_advance_typeInvariant hs hu ‹s.pending = _ :: _› (by assumption) h)
      | skip
    all_goals cases h
    all_goals try exact Or.inl hs
    all_goals try exact Or.inl (SolverState.TypeInvariant.empty rfl)
    all_goals try exact Or.inl ⟨(hs.drop_seen hm ‹s.pending = _ :: _›
      ((hu.pending _ (by simp [‹s.pending = _ :: _›])).fixed hu.modes)
      (by simpa using ‹s.seen.contains _ = true›)).seen⟩
    all_goals refine Or.inl (hs.advance ‹s.pending = _ :: _›
      ((hu.pending _ (by simp [‹s.pending = _ :: _›])).fixed hu.modes)
      (by first | exact List.Subset.refl _ | (simp only [SolverState.retain]; split <;> simp))
      (by simp [SolverState.emit, SolverState.retain])
      (by simp [SolverState.emit, SolverState.retain]) ?_)
    case h_1.refl =>
      rename_i pending c rest hp hseen normalized a b he
      intro Δ k _ hle _ hsmall
      rw [he] at hle ⊢
      have hab := hsmall (.sub a b) (by simp [SolverState.emit])
        (by simp only [Constraint.typeRank] at hle ⊢; omega)
      have hba := hsmall (.sub b a) (by simp [SolverState.emit])
        (by simp only [Constraint.typeRank] at hle ⊢; omega)
      exact ⟨hab.1, hba.1, hab.2⟩
    case h_4.isTrue.isTrue.refl =>
      rename_i pending c rest hp hseen normalized a he hfree heval
      intro Δ _ _ _ _ _
      rw [he]
      obtain ⟨m, heval⟩ := Option.isSome_iff_exists.mp heval
      exact fun _ _ => Option.isSome_iff_exists.mpr ⟨m, a.eval_refinement (by simp) heval⟩
    case h_4.isFalse.refl =>
      rename_i pending c rest hp hseen normalized a he hfree
      exact fun Δ _ _ _ hΔ _ => hΔ _ (s.mem_retain .defined (s.substitution.constraint c).normalize)
    case h_1.isTrue.refl | h_2.isTrue.refl =>
      rename_i pending c rest hp hseen normalized a v n he hrefl
      intro Δ _ _ _ _ _
      rw [he, beq_iff_eq.mp hrefl]
      exact ⟨.refl, .refl, by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩
    case h_2.isFalse.isTrue.refl =>
      rename_i pending c rest hp hseen normalized a v n he hrefl hoccurs
      intro Δ k _ hle _ hsmall
      rw [he] at hle ⊢
      have hleft := hsmall (.sub (.var (.flex n)) a) (by simp [SolverState.emit])
        (by simp only [Constraint.typeRank, TypeExpr.shapeSize] at hle ⊢; omega)
      have hright := hsmall (.sub a (.var (.flex n))) (by simp [SolverState.emit])
        (by simp only [Constraint.typeRank, TypeExpr.shapeSize] at hle ⊢; omega)
      exact ⟨hleft.1, hright.1, hleft.2.2⟩
  · exact Or.inl (SolverState.TypeInvariant.empty (hclear t h))

theorem runWorklist_typeReady {fuel s t} (hs : s.TypeReady) (hm : s.ModeInvariant)
    (hu : s.Unbound) (hf : s.Fresh) (hσ : s.substitution.Acyclic)
    (h : runWorklist fuel s = .success t) : t.TypeReady ∧ t.pending = [] := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact ⟨hs, by simpa using ‹t.pending.isEmpty = true›⟩
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_typeReady hs hm hu hf hσ ht) (solverStep_modeInvariant hm ht)
        (solverStep_unbound hu hf hσ ht) (solverStep_fresh hf ht) (solverStep_acyclic hσ ht) h

theorem runSolver_typeReady {fuel s t} (hs : s.TypeReady) (hm : s.ModeInvariant)
    (hu : s.Unbound) (hf : s.Fresh) (h : runSolver fuel s = .success t) :
    t.TypeReady ∧ t.pending = [] :=
  runWorklist_typeReady hs hm hu hf (runSolver_input_acyclic h) (runSolver_worklist h)

theorem SolverState.ClearsSeen.not_duplicate {s : SolverState} (hs : s.ClearsSeen)
    {c rest} (hp : s.pending = c :: rest) :
    (s.substitution.constraint c).normalize ∉ s.seen := by
  obtain ⟨d, tail, hd, hv, _⟩ := hs
  have hcd := (List.cons.inj (hp.symm.trans hd)).1
  simpa only [hcd] using hv

theorem SolverState.TypeReady.finished_invariant {s : SolverState} (hs : s.TypeReady)
    (hp : s.pending = []) : s.TypeInvariant := by
  rcases hs with hs | ⟨c, rest, hc, _, _⟩
  · exact hs
  · simp [hp] at hc

theorem SolverState.TypeReady.duplicate_entails {s : SolverState} (hs : s.TypeReady)
    (hm : s.ModeInvariant) {c rest Δ} (hp : s.pending = c :: rest)
    (hfix : s.substitution.constraint c = c)
    (hv : (s.substitution.constraint c).normalize ∈ s.seen)
    (hΔ : EntailsAll Δ (rest ++ s.bounds)) : Entails Δ c := by
  rcases hs with hs | hs
  · by_cases hcm : c.IsModality
    · exact hm.duplicate_entails hp hcm hv hΔ
    · apply (Constraint.normalize_entails c Δ).mp
      rw [← hfix]
      apply (hs.drop_seen hm hp hfix hv).seen _ hv
        (by rw [hfix, Constraint.normalize_typeRank]
            exact Nat.pos_of_ne_zero fun hz => hcm (c.typeRank_zero.mp hz)) Δ
        (fun d hd => hΔ d (List.mem_append_right _ hd))
      exact fun d hd _ => hΔ d (List.mem_append_left _ hd)
  · exact False.elim (hs.not_duplicate hp hv)

theorem SolverState.TypeInvariant.finished_seen {s : SolverState} (hs : s.TypeInvariant)
    (hp : s.pending = []) {c Δ} (hc : c ∈ s.seen) (hpos : 0 < c.typeRank)
    (hΔ : EntailsAll Δ s.bounds) : Entails Δ c :=
  hs.seen c hc hpos Δ hΔ (by simp [TypeOrientation.EntailsBelow, hp])

theorem SolverState.TypeReady.finished_seen {s : SolverState} (hs : s.TypeReady)
    (hm : s.ModeInvariant) (hp : s.pending = []) {c Δ} (hc : c ∈ s.seen)
    (hΔ : EntailsAll Δ s.bounds) : Entails Δ c := by
  by_cases hcm : c.IsModality
  · exact hm.finished_seen hp hc hcm hΔ
  · exact (hs.finished_invariant hp).finished_seen hp hc
      (Nat.pos_of_ne_zero fun hz => hcm (c.typeRank_zero.mp hz)) hΔ

theorem runSolver_all_seen_entails {fuel s t Δ} (hs : s.Fresh)
    (hσ : s.substitution = {}) (hv : s.seen = []) (h : runSolver fuel s = .success t)
    (hΔ : EntailsAll Δ t.bounds) : ∀ c ∈ t.seen, Entails Δ c := by
  have hm : s.ModeInvariant := ⟨by rw [hσ], by simp [hv]⟩
  have hu : s.Unbound := ⟨hm.modes,
    fun c _ => by rw [hσ]; exact c.unbound_empty,
    fun c _ => by rw [hσ]; exact c.unbound_empty,
    fun c _ => by rw [hσ]; exact c.unbound_empty⟩
  obtain ⟨ht, hp⟩ := runSolver_typeReady (Or.inl (SolverState.TypeInvariant.empty hv)) hm hu hs h
  exact fun c hc => ht.finished_seen (runSolver_modeInvariant hm h).1 hp hc hΔ

end ModalityInference
