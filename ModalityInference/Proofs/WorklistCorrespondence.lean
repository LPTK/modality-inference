import ModalityInference.Proofs.WorklistLocalRewriting
import ModalityInference.Proofs.Obligations

namespace ModalityInference.WorklistCorrespondence

theorem Deferred.postpone {s t : SolverState} {cs : Bounds} (hd : Deferred s cs)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t)
    (he : t.substitution = s.substitution) {c rest} (hp : s.pending = c :: rest) :
    Deferred t (c :: cs) := by
  have ht := hd.same hs hm hu hσ h he
  refine ⟨Bounds.bounded_cons.mpr ⟨(hf.pending c (by simp [hp])).mono
    (solverStep_counters h).1 (solverStep_counters h).2, ht.bounded⟩, ?_⟩
  intro Δ hΔ d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact solverStep_entails_of_same_substitution hs hm hu hσ h he hΔ d (by simp [hp])
  · exact ht.entails Δ hΔ d hd

theorem normalized_head {s : SolverState} {c rest} (hu : s.Unbound)
    (hp : s.pending = c :: rest) (cs : Bounds) :
    RewriteStar (config s cs)
      ⟨(s.substitution.constraint c).normalize :: (rest ++ cs), s.bounds, s.substitution⟩ := by
  have hfix := (hu.pending c (by simp [hp])).fixed hu.modes
  simpa only [config, hp, List.cons_append, hfix] using
    normalize c ⟨rest ++ cs, s.bounds, s.substitution⟩

theorem step {s t : SolverState} {cs : Bounds} (hd : Deferred s cs)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t) :
    ∃ ds, RewriteStar (config s cs) (config t ds) ∧ Deferred t ds := by
  have hrun := h
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  case h_2 =>
    rename_i pending c rest hp hseen normalized a b he
    have hsub := stepType_substitution h
    refine ⟨cs, ?_, hd.same hs hm hu hσ hrun hsub⟩
    have hstart := normalized_head hu hp cs
    rw [he] at hstart
    apply trans hstart
    have hbase := hf.advance hp (show (s.substitution.constraint c).normalize :: s.seen ⊆
      (s.substitution.constraint c).normalize :: s.seen by exact List.Subset.refl _)
    have hf' : ({s with pending := rest ++ cs, seen := (s.substitution.constraint c).normalize :: s.seen} : SolverState).Fresh :=
      ⟨Bounds.bounded_append.mpr ⟨hbase.pending, hd.bounded⟩,
        hbase.bounds, hbase.seen, hbase.substitution⟩
    have hh := stepType_rewrites hf' (he ▸ hf.normalized_head hp).1
      (he ▸ hf.normalized_head hp).2 (stepType_append h cs)
    exact hh
  case h_3 =>
    rename_i pending c rest hp hseen normalized a b he
    have hsub := stepMode_substitution h
    refine ⟨cs, ?_, hd.same hs hm hu hσ hrun hsub⟩
    have hstart := normalized_head hu hp cs
    rw [he] at hstart
    exact trans hstart (stepMode_rewrites (stepMode_append h cs))
  all_goals cases h
  all_goals try exact ⟨cs, .refl, hd⟩
  case isTrue.refl =>
    rename_i pending c rest hp hseen
    refine ⟨c :: cs, ?_, hd.postpone hs hm hu hf hσ hrun rfl hp⟩
    simpa only [config, hp, SolverState.emit, List.nil_append, List.cons_append] using
      permute (List.perm_middle (l₁ := rest) (a := c) (l₂ := cs)).symm
        ⟨[], s.bounds, s.substitution⟩
  case h_2.isFalse.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a v n he hsame hoccurs
    have hn : TypeVar.flex n ∉ a.typeVars := by simpa using hoccurs
    refine ⟨({types := [(n, a)]} : Substitution).bounds cs,
      substitute_deferred hu hσ hp he hn, ?_⟩
    exact hd.eliminate hu hf hp he hn rfl rfl (by rfl) (by rfl)
  all_goals refine ⟨cs, ?_, hd.same hs hm hu hσ hrun rfl⟩
  case h_1.refl =>
    rename_i pending c rest hp hseen normalized a b he
    have hstart := normalized_head hu hp cs
    rw [he] at hstart
    refine trans hstart (equivalent (cs := [.equiv a b])
      (ds := [.sub a b, .sub b a]) ?_ ⟨rest ++ cs, s.bounds, s.substitution⟩)
    intro Δ
    simp [EntailsAll, Entails, and_assoc, and_left_comm, and_comm]
  case h_4.isTrue.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a he hfree heval
    have hstart := normalized_head hu hp cs
    rw [he] at hstart
    apply trans hstart
    apply equivalent (cs := [.defined a]) (ds := []) (s := ⟨rest ++ cs, s.bounds, s.substitution⟩)
    intro Δ
    simp only [EntailsAll, List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff]
    refine ⟨fun _ _ => trivial, fun _ η _ => ?_⟩
    obtain ⟨m, heval⟩ := Option.isSome_iff_exists.mp heval
    exact Option.isSome_iff_exists.mpr ⟨m, a.eval_refinement (by simp) heval⟩
  case h_4.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a he hfree
    have hstart := normalized_head hu hp cs
    rw [he] at hstart
    simpa only [config, he, SolverState.retain] using
      trans hstart (retain {s with pending := rest ++ cs} .defined
        (.defined a) (by simp [Residual]))
  case h_1.isTrue.refl | h_2.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a v n he hrefl
    have hstart := normalized_head hu hp cs
    rw [he, beq_iff_eq.mp hrefl] at hstart
    apply trans hstart
    apply equivalent (cs := [.equal _ (.var _)]) (ds := []) (s := ⟨rest ++ cs, s.bounds, s.substitution⟩)
    intro Δ
    simp only [EntailsAll, List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff]
    exact ⟨fun _ _ => trivial, fun _ => ⟨.refl, .refl, by
      simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩⟩
  case h_2.isFalse.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a v n he hrefl hoccurs
    have hstart := normalized_head hu hp cs
    rw [he] at hstart
    apply trans hstart
    apply equivalent (cs := [.equal (.flex n) a])
      (ds := [.sub (.var (.flex n)) a, .sub a (.var (.flex n))])
      (s := ⟨rest ++ cs, s.bounds, s.substitution⟩)
    intro Δ
    simp [EntailsAll, Entails, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds,
      ModeModels, and_left_comm, and_comm]

end ModalityInference.WorklistCorrespondence

namespace ModalityInference.WorklistCorrespondence

theorem runWorklist_deferred {fuel s t} {cs : Bounds} (hd : Deferred s cs)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : runWorklist fuel s = .success t) :
    ∃ ds, RewriteStar (config s cs) (config t ds) ∧ Deferred t ds := by
  induction fuel generalizing s cs with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact ⟨cs, .refl, hd⟩
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      obtain ⟨middle, hstep, hmiddle⟩ := step hd hs hm hu hf hσ ht
      obtain ⟨last, hrest, hlast⟩ := ih hmiddle (solverStep_typeReady hs hm hu hf hσ ht)
        (solverStep_modeInvariant hm ht) (solverStep_unbound hu hf hσ ht)
        (solverStep_fresh hf ht) (solverStep_acyclic hσ ht) h
      exact ⟨last, trans hstep hrest, hlast⟩

theorem dischargeAll (s : RewriteConfig) {cs : Bounds} (hc : EntailsAll s.bounds cs) :
    RewriteStar {s with pending := cs} {s with pending := []} := by
  induction cs with
  | nil => exact .refl
  | cons c cs ih =>
    exact .step (Rewrites.discharge (s := {s with pending := cs}) (hc c (List.mem_cons_self)))
      (ih (fun d hd => hc d (List.mem_cons_of_mem _ hd)))

theorem runSolver_rewrites {fuel s t}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (hd : s.DefinedInvariant) (hr : Residual s.bounds)
    (h : runSolver fuel s = .success t) :
    RewriteStar ⟨s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩ := by
  obtain ⟨deferred, hsteps, hdeferred⟩ := runWorklist_deferred (Deferred.empty s)
    hs hm hu hf (runSolver_input_acyclic h) (runSolver_worklist h)
  obtain ⟨ht, hp⟩ := runSolver_definedInvariant hd h
  have hb : EntailsAll t.bounds t.bounds := ht.bounds_entails hp (runSolver_residual hr h)
  have hg : EntailsAll t.bounds deferred := hdeferred.entails t.bounds (by simpa [hp] using hb)
  refine trans (by simpa only [config, List.append_nil] using hsteps) ?_
  simpa only [config, hp, List.nil_append] using
    dischargeAll (⟨[], t.bounds, t.substitution⟩ : RewriteConfig) hg

end ModalityInference.WorklistCorrespondence

namespace ModalityInference

/-- Every successful structural worklist run, starting with fresh counters and
empty saved state, is an abstract guarded-rewriting derivation. -/
theorem runSolver_correspondence : Obligations.RunSolverCorrespondence := by
  intro fuel s t ht hm hσ hb hv h
  have hbounded : (s.pending ++ s.bounds).Bounded s.nextType s.nextMode :=
    (Bounds.bounded_iff _ _ _).mpr ⟨by simpa using ht, by simpa using hm⟩
  have hf : s.Fresh :=
    ⟨(Bounds.bounded_append.mp hbounded).1, (Bounds.bounded_append.mp hbounded).2,
      by simp [hv], by rw [hσ]; exact Substitution.bounded_empty _ _⟩
  have hu : s.Unbound := ⟨by simp [hσ],
    by simp [hσ, Constraint.Unbound], by simp [hb], by simp [hv]⟩
  apply WorklistCorrespondence.runSolver_rewrites (h := h)
  · exact Or.inl (SolverState.TypeInvariant.empty hv)
  · exact ⟨by simp [hσ], by simp [hv]⟩
  · exact hu
  · exact hf
  · exact ⟨by simp [hσ], by simp [hv, DefinedConstraints], by simp [hb]⟩
  · simp [hb, Residual]

end ModalityInference
