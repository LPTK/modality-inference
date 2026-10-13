import ModalityInference.Proofs.FlexibleSupport
import ModalityInference.Proofs.SolverDefinedness
import ModalityInference.Proofs.GroundReification

/-! Flexible solver inputs have finite closed models of their residual bounds. -/
namespace ModalityInference

structure SolverState.Flexible (s : SolverState) : Prop where
  pending : s.pending.Flexible
  bounds : s.bounds.Flexible
  substitution : s.substitution.Flexible

theorem SolverState.Flexible.emit {s : SolverState} (hs : s.Flexible)
    (r : RewriteRule) {cs : Bounds} (hc : cs.Flexible) : (s.emit r cs).Flexible :=
  ⟨Bounds.flexible_append.mpr ⟨hc, hs.pending⟩, hs.bounds, hs.substitution⟩

theorem SolverState.Flexible.retain {s : SolverState} (hs : s.Flexible)
    (r : RewriteRule) {c : Constraint} (hc : c.Flexible) : (s.retain r c).Flexible := by
  unfold SolverState.retain
  split
  · exact ⟨hs.pending, hs.bounds, hs.substitution⟩
  · exact ⟨hs.pending, Bounds.flexible_cons.mpr ⟨hc, hs.bounds⟩, hs.substitution⟩

theorem SolverState.Flexible.skeleton {s : SolverState} (hs : s.Flexible)
    {a : Ty} (ha : a.Flexible) : (s.skeleton a).1.Flexible ∧ (s.skeleton a).2.Flexible := by
  cases a <;> refine ⟨?_, ⟨hs.pending, hs.bounds, hs.substitution⟩⟩
  all_goals simp_all [SolverState.skeleton, SolverState.freshType,
    SolverState.freshMode, TypeExpr.Flexible, ModExpr.Flexible]

theorem recordModeBound_flexible {s : SolverState} (hs : s.Flexible)
    {a b : ModExpr} (ha : a.Flexible) (hb : b.Flexible) : (recordModeBound s a b).Flexible :=
  hs.retain .modeBound (And.intro ha hb)

theorem stepMode_flexible {s a b t} (hs : SolverState.Flexible s)
    (ha : ModExpr.Flexible a) (hb : b.Flexible) (h : stepMode s a b = .success t) :
    t.Flexible := by
  unfold stepMode at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals repeat' first
    | apply recordModeBound_flexible
    | apply SolverState.Flexible.emit
    | apply SolverState.Flexible.retain
  all_goals first | exact hs | simp_all [Constraint.Flexible, ModExpr.Flexible]

theorem stepType_flexible {s a b t} (hs : SolverState.Flexible s)
    (ha : TypeExpr.Flexible a) (hb : b.Flexible) (h : stepType s a b = .success t) :
    t.Flexible := by
  have hla := ha.outer
  have hrb := hb.outer
  have hl := hla.2.normalize
  have hr := hrb.2.normalize
  unfold stepType at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals try solve
    | exact hs.emit _ (by simp_all [Constraint.Flexible, TypeExpr.Flexible,
        ModExpr.Flexible, ModExpr.top])
    | exact (hs.retain _ (by simp_all [Constraint.Flexible, TypeExpr.Flexible])).emit _
        (by simp_all [Constraint.Flexible])
  all_goals
    have hf := Eq.mp (congrArg (fun p : Ty × SolverState => p.1.Flexible ∧ p.2.Flexible)
      ‹s.skeleton _ = (_, _)›) (hs.skeleton (by simp_all))
    exact hf.2.emit _ (by simp_all [Constraint.Flexible, TypeExpr.Flexible])

theorem SolverState.Flexible.advance {s : SolverState} (hs : s.Flexible)
    {c rest seen} (hp : s.pending = c :: rest) :
    {s with pending := rest, seen := seen}.Flexible :=
  ⟨(Bounds.flexible_cons.mp (hp ▸ hs.pending)).2, hs.bounds, hs.substitution⟩

theorem SolverState.Flexible.normalized_head {s : SolverState} (hs : s.Flexible)
    {c rest} (hp : s.pending = c :: rest) : (s.substitution.constraint c).normalize.Flexible :=
  (hs.substitution.constraint (Bounds.flexible_cons.mp (hp ▸ hs.pending)).1).normalize

theorem solverStep_flexible {s t} (hs : SolverState.Flexible s)
    (h : solverStep s = .success t) : t.Flexible := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals try have hc := hs.normalized_head ‹s.pending = _ :: _›
  all_goals first
    | exact stepType_flexible (hs.advance ‹s.pending = _ :: _›)
        (by simp_all [Constraint.Flexible]) (by simp_all [Constraint.Flexible]) h
    | exact stepMode_flexible (hs.advance ‹s.pending = _ :: _›)
        (by simp_all [Constraint.Flexible]) (by simp_all [Constraint.Flexible]) h
    | skip
  all_goals cases h
  all_goals try exact hs
  all_goals try solve
    | exact hs.advance ‹s.pending = _ :: _›
    | exact (hs.advance ‹s.pending = _ :: _›).emit _
        (by simp_all [Constraint.Flexible, TypeExpr.Flexible])
    | exact (hs.advance ‹s.pending = _ :: _›).retain _ (by simp_all [Constraint.Flexible])
    | simp_all [Constraint.Flexible]
  simp only [‹(s.substitution.constraint _).normalize = .equal _ _›, Constraint.Flexible] at hc
  refine ⟨(Substitution.flexible_singleType hc.2).bounds ?_, Bounds.flexible_nil,
    hs.substitution.extendType hc.2⟩
  exact Bounds.flexible_append.mpr ⟨Bounds.flexible_append.mpr
    ⟨(hs.advance (seen := []) ‹s.pending = _ :: _›).pending, hs.bounds⟩,
    hc.2.wellFormedBounds⟩

theorem runWorklist_flexible {fuel s t} (hs : SolverState.Flexible s)
    (h : runWorklist fuel s = .success t) : t.Flexible := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h; exact hs
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_flexible hs ht) h

theorem runSolver_flexible {fuel s t} (hs : SolverState.Flexible s)
    (h : runSolver fuel s = .success t) : t.Flexible := by
  have hσ := runSolver_input_acyclic h
  simp only [runSolver, (s.substitution.checkAcyclic_iff).mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind] at h
  split at h <;> first | exact runWorklist_flexible hs h | cases h

theorem solveFrom_flexible {fuel nt nm cs result} (hf : Bounds.Flexible cs)
    (h : solveFrom fuel nt nm cs = .success result) :
    result.bounds.Flexible ∧ result.substitution.Flexible := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  split at h <;> cases h
  have ht := runSolver_flexible ⟨hf, Bounds.flexible_nil, Substitution.flexible_empty⟩ hs
  exact ⟨ht.bounds, ht.substitution⟩

theorem solve_flexible {fuel cs result} (hf : Bounds.Flexible cs)
    (h : solve fuel cs = .success result) :
    result.bounds.Flexible ∧ result.substitution.Flexible := solveFrom_flexible hf h

/-- A successful flexible solve has the finite closed syntactic witness required
by declarative consistency, including all residual type constraints. -/
theorem solveFrom_consistency {fuel nt nm cs result} (hf : Bounds.Flexible cs)
    (h : solveFrom fuel nt nm cs = .success result) : BoundsSatisfiable result.bounds :=
  let hh := result.bounds.flexible_iff.mp (solveFrom_flexible hf h).1
  (solveFrom_ground_model h).boundsSatisfiable hh.1 hh.2

end ModalityInference
