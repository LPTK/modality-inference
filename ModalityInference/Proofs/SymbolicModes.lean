import ModalityInference.SymbolicModes
import ModalityInference.Proofs.HornPropagation

/-! The symbolic schedule evaluates to the generic Horn least fixed point at
every rigid interpretation, yielding one uniform expression witness. -/
namespace ModalityInference.SymbolicModes

def interpret (σ : Nat → Bool) (env : Mapping BoolExpr n) : Mapping Bool n :=
  Vector.ofFn fun i => (env.get i).eval σ

def interpretLeft (σ : Nat → Bool) : LeftExpr BoolExpr n → LeftExpr Bool n
  | .var i => .var i
  | .const c => .const (c.eval σ)
  | .meet a b => .meet (interpretLeft σ a) (interpretLeft σ b)
  | .join a b => .join (interpretLeft σ a) (interpretLeft σ b)

def interpretRight (σ : Nat → Bool) : RightExpr BoolExpr n → RightExpr Bool n
  | .var i => .var i
  | .const c => .const (c.eval σ)
  | .meet a b => .meet (interpretRight σ a) (interpretRight σ b)
  | .imply a b => .imply (interpretLeft σ a) (interpretRight σ b)

@[simp] theorem interpret_get (σ : Nat → Bool) (env : Mapping BoolExpr n) (i : Fin n) :
    (interpret σ env).get i = (env.get i).eval σ := by
  simp [interpret, Vector.get]

theorem left_eval (σ : Nat → Bool) (env : Mapping BoolExpr n) (l : LeftExpr BoolExpr n) :
    (left env l).eval σ = LeftExpr.eval (interpret σ env) (interpretLeft σ l) := by
  induction l <;> simp_all [left, BoolExpr.eval, interpretLeft, LeftExpr.eval]

theorem right_eval (σ : Nat → Bool) (env : Mapping BoolExpr n) (r : RightExpr BoolExpr n) :
    (right env r).eval σ = RightExpr.eval (interpret σ env) (interpretRight σ r) := by
  induction r <;> simp_all [right, BoolExpr.eval, interpretRight, RightExpr.eval, left_eval]
  cases LeftExpr.eval (interpret σ env) (interpretLeft σ ‹LeftExpr BoolExpr n›) <;>
    cases RightExpr.eval (interpret σ env) (interpretRight σ ‹RightExpr BoolExpr n›) <;> rfl

theorem update_eval (σ : Nat → Bool) (env : Mapping BoolExpr n) (c : BoolExpr)
    (r : RightExpr BoolExpr n) :
    interpret σ (update env c r) =
      RightExpr.update (interpret σ env) (c.eval σ) (interpretRight σ r) := by
  induction r generalizing c
  case var i =>
    apply Vector.ext
    intro j hj
    by_cases h : (⟨j, hj⟩ : Fin n) = i <;>
      simp [interpret, update, interpretRight, RightExpr.update, Mapping.update, Vector.get,
        h, BoolExpr.eval]
  case const => rfl
  case meet a b iha ihb =>
    simp only [update, interpretRight, RightExpr.update]
    rw [← iha, ← ihb]
    apply Vector.ext
    intro j hj
    simp [interpret, Vector.get, Max.max, BoolExpr.eval]
    cases ((update env c a).get ⟨j, hj⟩).eval σ <;>
      cases ((update env c b).get ⟨j, hj⟩).eval σ <;> rfl
  case imply a b ih =>
    simpa [update, interpretRight, RightExpr.update, BoolExpr.eval, left_eval] using
      ih (.and c (left env a))

theorem iterate_eval (σ : Nat → Bool) (r : RightExpr BoolExpr n) (k : Nat) :
    interpret σ (iterate r k) =
      RightExpr.iterate k (Mapping.const Bool n false) true (interpretRight σ r) := by
  induction k <;> simp_all [iterate, update_eval, RightExpr.iterate, BoolExpr.eval]
  apply Vector.ext
  simp [interpret, Mapping.const, Vector.get, BoolExpr.eval]

theorem solve_eval (σ : Nat → Bool) (r : RightExpr BoolExpr n) :
    interpret σ (solve r) = RightExpr.hornSolve true (interpretRight σ r) := by
  rw [solve, iterate_eval, RightExpr.hornSolve, RightExpr.iterate_opt_eq_iterate]
  rfl

theorem residual_eval (σ : Nat → Bool) (r : RightExpr BoolExpr n) :
    (residual r).eval σ =
      RightExpr.eval (RightExpr.hornSolve true (interpretRight σ r)) (interpretRight σ r) := by
  rw [residual, right_eval, solve_eval]

/-- One finite symbolic witness works for every rigid interpretation. -/
theorem residual_satisfiable_iff (σ : Nat → Bool) (r : RightExpr BoolExpr n) :
    (residual r).eval σ = true ↔
      ∃ env, RightExpr.eval env (interpretRight σ r) = true := by
  rw [residual_eval, HornPropagation.hornSolve_satisfiable_iff]

theorem solve_minimal (σ : Nat → Bool) (r : RightExpr BoolExpr n)
    (env : Mapping Bool n) (h : RightExpr.eval env (interpretRight σ r) = true) :
    interpret σ (solve r) ≤ env := by
  rw [solve_eval]
  exact RightExpr.hornSolve_minimal _ _ true (by simp [h])

def overlay (flex : List Nat) (env : Mapping Bool flex.length) (σ : Nat → Bool)
    (v : Nat) : Bool :=
  ((ConcreteBackend.atomFin flex v).map env.get).getD (σ v)

theorem eval_congr (e : BoolExpr) {σ τ : Nat → Bool}
    (h : ∀ v ∈ e.atoms, σ v = τ v) : e.eval σ = e.eval τ := by
  induction e <;> simp_all [BoolExpr.eval, BoolExpr.atoms, or_imp, forall_and]

theorem rigid_eval {flex e} (h : rigid flex e = true)
    (σ : Nat → Bool) (env : Mapping Bool flex.length) :
    e.eval (overlay flex env σ) = e.eval σ := by
  apply eval_congr e
  intro v hv
  have hn : v ∉ flex := by simpa using (List.all_eq_true.mp h v hv)
  simp [overlay, ConcreteBackend.atomFin, hn]

theorem positive_eval {flex e r} (h : positive flex e = some r)
    (σ : Nat → Bool) (env : Mapping Bool flex.length) :
    LeftExpr.eval env (interpretLeft σ r) = e.eval (overlay flex env σ) := by
  induction e generalizing r <;> rw [positive] at h
  all_goals split at h
  all_goals try (cases h; exact (rigid_eval ‹_ = true› σ env).symm)
  case const.isFalse b hr => cases h; rfl
  case atom.isFalse v hr =>
    cases hi : ConcreteBackend.atomFin flex v <;> simp [hi] at h
    cases h; simp [interpretLeft, LeftExpr.eval, BoolExpr.eval, overlay, hi]
  case and.isFalse a b iha ihb hr | or.isFalse a b iha ihb hr =>
    cases ha : positive flex a <;> cases hb : positive flex b <;> simp [ha, hb] at h
    all_goals cases h; simp only [interpretLeft, LeftExpr.eval, BoolExpr.eval, iha ha, ihb hb]; rfl
  case imp.isFalse => cases h

theorem horn_eval {flex e r} (h : horn flex e = some r)
    (σ : Nat → Bool) (env : Mapping Bool flex.length) :
    RightExpr.eval env (interpretRight σ r) = e.eval (overlay flex env σ) := by
  induction e generalizing r <;> rw [horn] at h
  all_goals split at h
  all_goals try (cases h; exact (rigid_eval ‹_ = true› σ env).symm)
  case const.isFalse b hr => cases h; rfl
  case atom.isFalse v hr =>
    cases hi : ConcreteBackend.atomFin flex v <;> simp [hi] at h
    cases h; simp [interpretRight, RightExpr.eval, BoolExpr.eval, overlay, hi]
  case and.isFalse a b iha ihb hr =>
    cases ha : horn flex a <;> cases hb : horn flex b <;> simp [ha, hb] at h
    cases h; simp only [interpretRight, RightExpr.eval, BoolExpr.eval, iha ha, ihb hb]; rfl
  case imp.isFalse a b iha ihb hr =>
    cases ha : positive flex a <;> cases hb : horn flex b <;> simp [ha, hb] at h
    cases h
    simp only [interpretRight, RightExpr.eval, BoolExpr.eval, positive_eval ha, ihb hb]
    cases a.eval (overlay flex env σ) <;> cases b.eval (overlay flex env σ) <;> rfl
  case or.isFalse => cases h

theorem eliminate_correct {flex e s} (h : eliminate flex e = some s) (σ : Nat → Bool) :
    s.obligation.eval σ = true ↔
      ∃ env, e.eval (overlay flex env σ) = true := by
  cases hr : horn flex e <;> simp [eliminate, hr] at h
  cases h
  rw [residual_satisfiable_iff]
  exact exists_congr fun env => by rw [horn_eval hr]

theorem eliminate_witness {flex e s} (h : eliminate flex e = some s) (σ : Nat → Bool) :
    e.eval (fun v => (s.substitute v).eval σ) = s.obligation.eval σ := by
  cases hr : horn flex e <;> simp [eliminate, hr] at h
  cases h
  rw [residual, right_eval, horn_eval hr]
  apply eval_congr e
  intro v _
  cases hi : ConcreteBackend.atomFin flex v <;>
    simp [Elimination.substitute, overlay, hi, BoolExpr.eval]

/-- Rigid assumptions are retained as hypotheses; elimination never solves them. -/
theorem eliminate_under_assumptions {flex e s} (h : eliminate flex e = some s)
    (assumptions : BoolExpr) :
    (∀ σ, assumptions.eval σ = true → s.obligation.eval σ = true) ↔
      ∀ σ, assumptions.eval σ = true → ∃ env, e.eval (overlay flex env σ) = true := by
  simp only [eliminate_correct h]

end ModalityInference.SymbolicModes
