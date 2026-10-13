import ModalityInference.Proofs.SolverFresh

/-! Structural decrease of ordinary type steps and the cache reset after expansion. -/
namespace ModalityInference

/-- Modal wrappers do not contribute to structural type size. -/
def TypeExpr.shapeSize : Ty → Nat
  | .var _ | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b => a.shapeSize + b.shapeSize + 1
  | .modal a _ => a.shapeSize

theorem TypeExpr.shapeSize_pos (a : Ty) : 0 < a.shapeSize := by
  induction a <;> simp_all [shapeSize]

@[simp] theorem TypeExpr.outer_shapeSize (a : Ty) : a.outer.1.shapeSize = a.shapeSize := by
  induction a <;> simp_all [outer, shapeSize]

@[simp] theorem TypeExpr.normalize_shapeSize (a : Ty) : a.normalize.shapeSize = a.shapeSize := by
  induction a <;> simp_all [normalize, shapeSize]
  split <;> simp_all [shapeSize]
  split <;> simp_all [shapeSize]

def Constraint.typeRank : Constraint → Nat
  | .sub a b => 2 * (a.shapeSize + b.shapeSize)
  | .equiv a b => 2 * (a.shapeSize + b.shapeSize) + 1
  | .equal _ a => 2 * (1 + a.shapeSize) + 1
  | .mode _ _ | .defined _ => 0

@[simp] theorem Constraint.normalize_typeRank (c : Constraint) : c.normalize.typeRank = c.typeRank := by
  cases c <;> simp [normalize, typeRank]

@[simp] theorem Constraint.typeRank_zero (c : Constraint) : c.typeRank = 0 ↔ c.IsModality := by
  cases c <;> simp [typeRank, IsModality, Nat.mul_eq_zero, Nat.add_eq_zero,
    Nat.ne_of_gt (TypeExpr.shapeSize_pos _)]

/-- An intermediate expansion cannot discharge its head from the cache, and its
next successful transition resets that cache. -/
def SolverState.ClearsSeen (s : SolverState) : Prop :=
  ∃ c rest, s.pending = c :: rest ∧
    (s.substitution.constraint c).normalize ∉ s.seen ∧
    ∀ t, solverStep s = .success t → t.seen = []

theorem SolverState.Fresh.skeleton_clearsSeen {s : SolverState} (hs : s.Fresh)
    {a n} (ha : Shape a (s.skeleton a).1) (hn : n < s.nextType)
    (hkey : n ∉ s.substitution.types.map Prod.fst) (old : Constraint) :
    ((s.skeleton a).2.emit .expand [.equal (.flex n) (s.skeleton a).1, old]).ClearsSeen := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simpa only [SolverState.emit, SolverState.skeleton_substitution,
      (s.skeleton_frame a).2.2, hs.skeleton_equal_normalized ha hkey] using
      hs.skeleton_equal_not_seen (.flex n) a
  · intro t ht
    exact congrArg SolverState.seen (RunResult.success.inj
      ((hs.skeleton_eliminated ha hn hkey old).symm.trans ht)).symm

theorem SolverState.Fresh.outer_skeleton_clearsSeen {s : SolverState} (hs : s.Fresh)
    {a b : Ty} {n} (ha : a.Bounded s.nextType s.nextMode)
    (he : a.outer.1 = .var (.flex n))
    (hf : ∀ k ∈ s.substitution.types.map Prod.fst, .flex k ∉ a.typeVars)
    (hb : ∀ v, b.outer.1 ≠ .var v) (old : Constraint) :
    ((s.skeleton b.outer.1).2.emit .expand
      [.equal (.flex n) (s.skeleton b.outer.1).1, old]).ClearsSeen :=
  hs.skeleton_clearsSeen (s.skeleton_shape hb b.outer_not_modal)
    (by simpa only [he, TypeExpr.Bounded, TypeVar.index] using ha.outer.1)
    (fun hk => hf n hk (TypeExpr.outer_var_mem he)) old

theorem stepType_decreases_or_clears {s : SolverState} (hs : s.Fresh)
    {a b t} (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hf : ∀ k ∈ s.substitution.types.map Prod.fst,
      .flex k ∉ a.typeVars ∧ .flex k ∉ b.typeVars)
    (h : stepType s a b = .success t) :
    t.ClearsSeen ∨ ∀ c ∈ t.pending, c ∈ s.pending ∨ c.typeRank < (Constraint.sub a b).typeRank := by
  unfold stepType at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals try solve
    | left
      simpa only [*, Prod.fst, Prod.snd] using
        hs.outer_skeleton_clearsSeen (b := b) ha (by simp_all)
          (fun k hk => (hf k hk).1) (by simp_all)
          (.sub (.modal a.outer.1 a.outer.2.normalize) (.modal b.outer.1 b.outer.2.normalize))
    | left
      simpa only [*, Prod.fst, Prod.snd] using
        hs.outer_skeleton_clearsSeen (b := a) hb (by simp_all)
          (fun k hk => (hf k hk).2) (by simp_all)
          (.sub (.modal a.outer.1 a.outer.2.normalize) (.modal b.outer.1 b.outer.2.normalize))
  all_goals right
  all_goals simp [SolverState.emit, SolverState.retain, Constraint.typeRank,
    ← a.outer_shapeSize, ← b.outer_shapeSize, *, TypeExpr.shapeSize, or_imp, forall_and]
  all_goals grind

theorem solverStep_sub_decreases_or_clears {s : SolverState} (hs : s.Fresh)
    (hσ : s.substitution.Acyclic) {c rest a b t} (hp : s.pending = c :: rest)
    (he : (s.substitution.constraint c).normalize = .sub a b)
    (h : stepType {s with pending := rest, seen := .sub a b :: s.seen} a b = .success t) :
    t.ClearsSeen ∨ ∀ d ∈ t.pending, d ∈ rest ∨ d.typeRank < (Constraint.sub a b).typeRank := by
  exact stepType_decreases_or_clears
    (hs.advance hp (by simp [he]))
    (he ▸ hs.normalized_head hp).1 (he ▸ hs.normalized_head hp).2
    (s.substitution.normalized_sub_fresh hσ he) h

end ModalityInference
