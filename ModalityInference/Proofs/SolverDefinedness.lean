import ModalityInference.Proofs.ResidualModels

/-! The solver retains definedness of the modalities in residual type bounds. -/
namespace ModalityInference

def DefinedConstraint (η : ModVar → Mode) : Constraint → Prop
  | .defined m => m.WellFormed η
  | _ => True

def DefinedConstraints (cs : Bounds) (η : ModVar → Mode) : Prop :=
  ∀ c ∈ cs, DefinedConstraint η c

/-- Previously visited definedness constraints follow from retained bounds.
Type-bound guards may still be pending, but only explicit definedness obligations
are used from that pending list. This makes duplicate discharge sound for the
invariant without assuming correctness of all other constraint reductions. -/
structure SolverState.DefinedInvariant (s : SolverState) : Prop where
  modes : s.substitution.modes = []
  seen : ∀ η, ModeModels s.bounds η → DefinedConstraints s.seen η
  bounds : ∀ η, ModeModels s.bounds η → DefinedConstraints s.pending η →
    ∀ a b, Constraint.sub a b ∈ s.bounds →
      ModeModels a.wellFormedBounds η ∧ ModeModels b.wellFormedBounds η

theorem DefinedConstraint.normalize_substitution {σ : Substitution} (hσ : σ.modes = [])
    (c : Constraint) (η : ModVar → Mode) :
    DefinedConstraint η (σ.constraint c).normalize ↔ DefinedConstraint η c := by
  have hm : σ.mode = ModExpr.var := by
    funext v
    cases v <;> simp [Substitution.mode, hσ]
  cases c <;> simp [Substitution.constraint, Constraint.subst, Constraint.normalize,
    DefinedConstraint, hm, ModExpr.WellFormed]
  rename_i v a
  cases v <;> simp
  rename_i n
  cases σ.types.lookup n <;> trivial

theorem SolverState.DefinedInvariant.emit {s : SolverState} (hs : s.DefinedInvariant)
    (r : RewriteRule) (cs : Bounds) : (s.emit r cs).DefinedInvariant :=
  ⟨hs.modes, hs.seen, fun η hη hp => hs.bounds η hη
    (fun c hc => hp c (by simp [SolverState.emit, hc]))⟩

theorem SolverState.DefinedInvariant.retain {s : SolverState} (hs : s.DefinedInvariant)
    {c : Constraint} (hc : ∀ a b, c ≠ .sub a b) (r : RewriteRule) :
    (s.retain r c).DefinedInvariant := by
  unfold SolverState.retain
  split
  · exact hs.emit r []
  · exact ⟨hs.modes, fun η hη => hs.seen η (fun d hd => hη d (List.mem_cons_of_mem _ hd)),
      fun η hη hp a b hab => hs.bounds η (fun d hd => hη d (List.mem_cons_of_mem _ hd))
        hp a b ((List.mem_cons.mp hab).resolve_left (Ne.symm (hc a b)))⟩

theorem SolverState.DefinedInvariant.advance {s : SolverState} (hs : s.DefinedInvariant)
    {c rest seen} (hp : s.pending = c :: rest)
    (hd : ∀ η, ModeModels s.bounds η → DefinedConstraint η (s.substitution.constraint c).normalize)
    (hv : seen ⊆ (s.substitution.constraint c).normalize :: s.seen) :
    {s with pending := rest, seen := seen}.DefinedInvariant := by
  refine ⟨hs.modes, ?_, ?_⟩
  · intro η hη d hh
    rcases List.mem_cons.mp (hv hh) with rfl | hh
    · exact hd η hη
    · exact hs.seen η hη d hh
  · intro η hη hr
    apply hs.bounds η hη
    rw [hp]
    rintro d hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact (DefinedConstraint.normalize_substitution hs.modes d η).mp (hd η hη)
    · exact hr d hd'

theorem SolverState.DefinedInvariant.retain_type {s : SolverState} (hs : s.DefinedInvariant)
    (x y : TypeVar) (l r : ModExpr) :
    ((s.retain .variableBound (.sub (.modal (.var x) l) (.modal (.var y) r))).emit
      .defined [.defined l, .defined r]).DefinedInvariant := by
  unfold SolverState.retain
  split
  · exact (hs.emit .variableBound []).emit _ _
  · refine ⟨hs.modes, ?_, ?_⟩
    · exact fun η hη => hs.seen η (fun c hc => hη c (List.mem_cons_of_mem _ hc))
    · intro η hη hp a b hab
      rcases List.mem_cons.mp hab with he | he
      · obtain ⟨rfl, rfl⟩ := Constraint.sub.inj he
        simpa [TypeExpr.wellFormedBounds, ModeModels, ModeSatisfies, DefinedConstraint] using
          And.intro (hp (.defined l) (by simp [SolverState.emit]))
            (hp (.defined r) (by simp [SolverState.emit]))
      · exact hs.bounds η (fun c hc => hη c (List.mem_cons_of_mem _ hc))
          (fun c hc => hp c (by simp [SolverState.emit, hc])) a b he

theorem SolverState.DefinedInvariant.skeleton {s : SolverState} (hs : s.DefinedInvariant)
    (a : Ty) : (s.skeleton a).2.DefinedInvariant := by
  cases a <;> exact ⟨hs.modes, hs.seen, hs.bounds⟩

theorem stepType_definedInvariant {s a b t} (hs : s.DefinedInvariant)
    (h : stepType s a b = .success t) : t.DefinedInvariant := by
  unfold stepType at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals first | exact hs.emit _ _ | exact hs.retain_type _ _ _ _ | skip
  all_goals apply SolverState.DefinedInvariant.emit
  all_goals
    have he := congrArg Prod.snd ‹s.skeleton _ = (_, _)›
    exact Eq.mp (congrArg SolverState.DefinedInvariant he) (hs.skeleton _)

theorem stepMode_definedInvariant {s a b t} (hs : s.DefinedInvariant)
    (h : stepMode s a b = .success t) : t.DefinedInvariant := by
  unfold stepMode at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals repeat' apply SolverState.DefinedInvariant.emit
  all_goals first | exact hs | exact hs.retain (by simp) _

theorem SolverState.mem_retain (s : SolverState) (r : RewriteRule) (c : Constraint) :
    c ∈ (s.retain r c).bounds := by
  simp only [SolverState.retain]
  split <;> simp_all

theorem solverStep_definedInvariant {s t} (hs : s.DefinedInvariant)
    (h : solverStep s = .success t) : t.DefinedInvariant := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals first
    | exact stepType_definedInvariant
        (hs.advance ‹s.pending = _ :: _› (by simp_all [DefinedConstraint]) (by simp)) h
    | exact stepMode_definedInvariant
        (hs.advance ‹s.pending = _ :: _› (by simp_all [DefinedConstraint]) (by simp)) h
    | skip
  all_goals cases h
  all_goals try exact hs
  all_goals try apply SolverState.DefinedInvariant.emit
  all_goals first
    | (apply hs.advance ‹s.pending = _ :: _› ?_ (by simp))
    | skip
  all_goals try solve | simp_all [DefinedConstraint]
  case h_4.isFalse.refl =>
    rename_i pending c rest hp hseen normalized m hc hm
    have ht := hs.retain (c := (s.substitution.constraint c).normalize)
      (by simp [hc]) .defined
    apply ht.advance hp ?_ (by simp [SolverState.retain])
    intro η hη
    simpa only [SolverState.retain, hc, DefinedConstraint, ModeSatisfies] using
      hη _ (s.mem_retain .defined (s.substitution.constraint c).normalize)
  case h_2.isFalse.isFalse.refl =>
    exact ⟨hs.modes, by simp [DefinedConstraints], by simp⟩
  · rename_i pending c rest hp hc
    intro η hη
    exact hs.seen η hη _ (by simpa using hc)
  · rename_i pending c rest hp hseen normalized m hc hfree heval
    simp only [hc, DefinedConstraint]
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp heval
    exact fun _ _ => Option.isSome_iff_exists.mpr ⟨n, m.eval_refinement (by simp) hn⟩

theorem runWorklist_definedInvariant {fuel s t} (hs : s.DefinedInvariant)
    (h : runWorklist fuel s = .success t) : t.DefinedInvariant ∧ t.pending = [] := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact ⟨hs, by simpa using ‹t.pending.isEmpty = true›⟩
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_definedInvariant hs ht) h

theorem runSolver_definedInvariant {fuel s t} (hs : s.DefinedInvariant)
    (h : runSolver fuel s = .success t) : t.DefinedInvariant ∧ t.pending = [] := by
  have hσ := runSolver_input_acyclic h
  simp only [runSolver, (s.substitution.checkAcyclic_iff).mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind] at h
  split at h <;> first | exact runWorklist_definedInvariant hs h | cases h

theorem solveFrom_typeBounds_defined {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) :
    ∀ η, ModeModels result.bounds η → ∀ a b, Constraint.sub a b ∈ result.bounds →
      ModeModels a.wellFormedBounds η ∧ ModeModels b.wellFormedBounds η := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  split at h <;> cases h
  obtain ⟨ht, hp⟩ := runSolver_definedInvariant
    ⟨rfl, by simp [DefinedConstraints], by simp⟩ hs
  exact fun η hη => ht.bounds η hη (by simp [hp, DefinedConstraints])

theorem solve_typeBounds_defined {fuel cs result} (h : solve fuel cs = .success result) :
    ∀ η, ModeModels result.bounds η → ∀ a b, Constraint.sub a b ∈ result.bounds →
      ModeModels a.wellFormedBounds η ∧ ModeModels b.wellFormedBounds η :=
  solveFrom_typeBounds_defined h

/-- The actual returned modes extend to a model of all residual constraints.
This does not assert entailment of the original input or construct the finite
closed syntactic substitution required by `BoundsSatisfiable`. -/
theorem solveFrom_ground_model {fuel nt nm cs result}
    (h : solveFrom fuel nt nm cs = .success result) :
    GroundModels (residualAssignment result.witness.total) result.bounds :=
  (solveFrom_residual h).groundModels (solveFrom_mode_witness h)
    (solveFrom_typeBounds_defined h _ (solveFrom_mode_witness h))

theorem solve_ground_model {fuel cs result} (h : solve fuel cs = .success result) :
    GroundModels (residualAssignment result.witness.total) result.bounds :=
  solveFrom_ground_model h

end ModalityInference
