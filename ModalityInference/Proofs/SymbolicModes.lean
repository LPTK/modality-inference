import ModalityInference.SymbolicModes
import ModalityInference.Proofs.HornPropagation
import ModalityInference.Proofs.PartialSubstitution

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


theorem reifyAtom_eval {axis i m} (h : reifyAtom axis i = some m)
    (η : ModVar → Mode) :
    m.eval (some ∘ η) = some (axis.embed (encodeModes η i)) := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize he : i % 3 = k at hi
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals cases axis <;> simp [reifyAtom, he] at h
  all_goals cases h
  all_goals simp [ModExpr.eval, Mode.join, Mode.future, Mode.close, Mode.closeInv,
    ModExpr.epsilon, Mode.identity, Axis.embed, encodeModes, atomVariable, he]

theorem reify_eval {axis e m} (h : reify axis e = some m) (η : ModVar → Mode) :
    m.eval (some ∘ η) = some (axis.embed (e.eval (encodeModes η))) := by
  induction e generalizing m
  case const b => cases h; rfl
  case atom i => exact reifyAtom_eval h η
  case and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    cases ha : reify axis a <;> cases hb : reify axis b <;> simp [reify, ha, hb] at h
    all_goals cases h
    all_goals cases axis <;>
      simp [ModExpr.eval, iha ha, ihb hb, Axis.embed, Mode.compose, Mode.join, Mode.meet,
        Mode.leftResidual, Mode.rightResidual, BoolExpr.eval]

theorem Elimination.mode_eval {flex} {s : Elimination flex} {v m}
    (h : s.mode v = some m) (η : ModVar → Mode) :
    m.eval (some ∘ η) = some
      ⟨(s.substitute (v.atomIndex 0)).eval (encodeModes η),
        (s.substitute (v.atomIndex 1)).eval (encodeModes η),
        (s.substitute (v.atomIndex 2)).eval (encodeModes η)⟩ := by
  cases hl : reify .locality (s.substitute (v.atomIndex 0)) <;>
    cases ha : reify .affinity (s.substitute (v.atomIndex 1)) <;>
    cases hu : reify .uniqueness (s.substitute (v.atomIndex 2)) <;>
    simp [Elimination.mode, hl, ha, hu] at h
  cases h
  simp [ModExpr.eval, reify_eval hl η, reify_eval ha η, reify_eval hu η,
    Axis.embed, Mode.compose]

def Axis.Supports : Axis → Nat → Prop
  | .locality, i => i % 3 = 0
  | _, i => i % 3 ≠ 0

theorem reifyAtom_supported (axis : Axis) (i : Nat) :
    (∃ m, reifyAtom axis i = some m) ↔ axis.Supports i := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize he : i % 3 = k at hi
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals cases axis <;> simp [reifyAtom, Axis.Supports, he]

theorem reify_supported (axis : Axis) (e : BoolExpr) :
    (∃ m, reify axis e = some m) ↔ ∀ i ∈ e.atoms, axis.Supports i := by
  induction e
  case const b => simp [reify, BoolExpr.atoms]
  case atom i => simpa [reify, BoolExpr.atoms] using reifyAtom_supported axis i
  case and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    cases ha : reify axis a <;> cases hb : reify axis b <;>
      simp_all [reify, BoolExpr.atoms, or_imp, forall_and]

def LeftRigid (flex : List Nat) : LeftExpr BoolExpr n → Prop
  | .var _ => True
  | .const c => rigid flex c = true
  | .meet a b | .join a b => LeftRigid flex a ∧ LeftRigid flex b

def RightRigid (flex : List Nat) : RightExpr BoolExpr n → Prop
  | .var _ => True
  | .const c => rigid flex c = true
  | .meet a b => RightRigid flex a ∧ RightRigid flex b
  | .imply a b => LeftRigid flex a ∧ RightRigid flex b

@[simp] theorem rigid_and (flex : List Nat) (a b : BoolExpr) :
    rigid flex (.and a b) = true ↔ rigid flex a = true ∧ rigid flex b = true := by
  simp [rigid, BoolExpr.atoms, List.all_eq_true, or_imp, forall_and]

@[simp] theorem rigid_or (flex : List Nat) (a b : BoolExpr) :
    rigid flex (.or a b) = true ↔ rigid flex a = true ∧ rigid flex b = true := by
  simp [rigid, BoolExpr.atoms, List.all_eq_true, or_imp, forall_and]

@[simp] theorem rigid_imp (flex : List Nat) (a b : BoolExpr) :
    rigid flex (.imp a b) = true ↔ rigid flex a = true ∧ rigid flex b = true := by
  simp [rigid, BoolExpr.atoms, List.all_eq_true, or_imp, forall_and]

theorem positive_rigid {flex e r} (h : positive flex e = some r) : LeftRigid flex r := by
  induction e generalizing r <;> rw [positive] at h
  all_goals split at h
  all_goals try (cases h; exact ‹rigid _ _ = true›)
  case const.isFalse b hr => cases h; simp [LeftRigid, rigid, BoolExpr.atoms]
  case atom.isFalse v hr =>
    cases hi : ConcreteBackend.atomFin flex v <;> simp [hi] at h
    cases h; trivial
  case and.isFalse a b iha ihb hr | or.isFalse a b iha ihb hr =>
    cases ha : positive flex a <;> cases hb : positive flex b <;> simp [ha, hb] at h
    all_goals cases h; exact ⟨iha ha, ihb hb⟩
  case imp.isFalse => cases h

theorem horn_rigid {flex e r} (h : horn flex e = some r) : RightRigid flex r := by
  induction e generalizing r <;> rw [horn] at h
  all_goals split at h
  all_goals try (cases h; exact ‹rigid _ _ = true›)
  case const.isFalse b hr => cases h; simp [RightRigid, rigid, BoolExpr.atoms]
  case atom.isFalse v hr =>
    cases hi : ConcreteBackend.atomFin flex v <;> simp [hi] at h
    cases h; trivial
  case and.isFalse a b iha ihb hr =>
    cases ha : horn flex a <;> cases hb : horn flex b <;> simp [ha, hb] at h
    cases h; exact ⟨iha ha, ihb hb⟩
  case imp.isFalse a b iha ihb hr =>
    cases ha : positive flex a <;> cases hb : horn flex b <;> simp [ha, hb] at h
    cases h; exact ⟨positive_rigid ha, ihb hb⟩
  case or.isFalse => cases h

theorem left_rigid {flex : List Nat} {env : Mapping BoolExpr n}
    (he : ∀ i, rigid flex (env.get i) = true) {l : LeftExpr BoolExpr n}
    (hl : LeftRigid flex l) : rigid flex (left env l) = true := by
  induction l <;> simp_all [left, LeftRigid]

theorem right_rigid {flex : List Nat} {env : Mapping BoolExpr n}
    (he : ∀ i, rigid flex (env.get i) = true) {r : RightExpr BoolExpr n}
    (hr : RightRigid flex r) : rigid flex (right env r) = true := by
  induction r <;> simp_all [right, RightRigid, left_rigid he]

theorem update_rigid {flex : List Nat} {env : Mapping BoolExpr n}
    (he : ∀ i, rigid flex (env.get i) = true) {c : BoolExpr} (hc : rigid flex c = true)
    {r : RightExpr BoolExpr n} (hr : RightRigid flex r) :
    ∀ i, rigid flex ((update env c r).get i) = true := by
  induction r generalizing c
  case var j =>
    intro i
    by_cases hi : i = j
    · simpa [update, Vector.get, hi, hc] using he j
    · simpa [update, Vector.get, hi] using he i
  case const => exact he
  case meet a b iha ihb =>
    intro i
    simpa [update, Vector.get] using
      (rigid_or flex _ _).mpr ⟨iha hc hr.1 i, ihb hc hr.2 i⟩
  case imply a b ih =>
    exact ih ((rigid_and flex _ _).mpr ⟨hc, left_rigid he hr.1⟩) hr.2

theorem iterate_rigid {flex : List Nat} {r : RightExpr BoolExpr n}
    (hr : RightRigid flex r) (k : Nat) :
    ∀ i, rigid flex ((iterate r k).get i) = true := by
  induction k
  case zero => simp [iterate, Mapping.get_const, rigid, BoolExpr.atoms]
  case succ k ih => exact update_rigid ih (by simp [rigid, BoolExpr.atoms]) hr

theorem eliminate_rigid {flex e s} (h : eliminate flex e = some s) :
    (∀ i, rigid flex (s.values.get i) = true) ∧ rigid flex s.obligation = true := by
  cases hr : horn flex e <;> simp [eliminate, hr] at h
  cases h
  exact ⟨iterate_rigid (horn_rigid hr) _, right_rigid (iterate_rigid (horn_rigid hr) _)
    (horn_rigid hr)⟩

theorem eliminate_no_flexible_atoms {flex e s} (h : eliminate flex e = some s) :
    (∀ i v, v ∈ (s.values.get i).atoms → v ∉ flex) ∧
      ∀ v, v ∈ s.obligation.atoms → v ∉ flex := by
  simpa [rigid, List.all_eq_true] using eliminate_rigid h

inductive RelativePositive (flex : List Nat) : BoolExpr → Prop where
  | rigid {e} : rigid flex e = true → RelativePositive flex e
  | atom (v) : RelativePositive flex (.atom v)
  | and {a b} : RelativePositive flex a → RelativePositive flex b → RelativePositive flex (.and a b)
  | or {a b} : RelativePositive flex a → RelativePositive flex b → RelativePositive flex (.or a b)

inductive RelativeHorn (flex : List Nat) : BoolExpr → Prop where
  | rigid {e} : rigid flex e = true → RelativeHorn flex e
  | atom (v) : RelativeHorn flex (.atom v)
  | and {a b} : RelativeHorn flex a → RelativeHorn flex b → RelativeHorn flex (.and a b)
  | imp {a b} : RelativePositive flex a → RelativeHorn flex b → RelativeHorn flex (.imp a b)

theorem positive_supported {flex e r} (h : positive flex e = some r) :
    RelativePositive flex e := by
  induction e generalizing r <;> rw [positive] at h
  all_goals split at h
  all_goals try exact .rigid ‹rigid _ _ = true›
  case const.isFalse b hr => exact .rigid (by simp [rigid, BoolExpr.atoms])
  case atom.isFalse v hr => exact .atom v
  case and.isFalse a b iha ihb hr | or.isFalse a b iha ihb hr =>
    cases ha : positive flex a <;> cases hb : positive flex b <;> simp [ha, hb] at h
    all_goals first | exact .and (iha ha) (ihb hb) | exact .or (iha ha) (ihb hb)
  case imp.isFalse => cases h

theorem horn_supported {flex e r} (h : horn flex e = some r) : RelativeHorn flex e := by
  induction e generalizing r <;> rw [horn] at h
  all_goals split at h
  all_goals try exact .rigid ‹rigid _ _ = true›
  case const.isFalse b hr => exact .rigid (by simp [rigid, BoolExpr.atoms])
  case atom.isFalse v hr => exact .atom v
  case and.isFalse a b iha ihb hr =>
    cases ha : horn flex a <;> cases hb : horn flex b <;> simp [ha, hb] at h
    exact .and (iha ha) (ihb hb)
  case imp.isFalse a b iha ihb hr =>
    cases ha : positive flex a <;> cases hb : horn flex b <;> simp [ha, hb] at h
    exact .imp (positive_supported ha) (ihb hb)
  case or.isFalse => cases h

theorem positive_complete {flex e} (h : RelativePositive flex e) :
    ∃ r, positive flex e = some r := by
  induction h
  case rigid e hr => exact ⟨.const e, by rw [positive.eq_def, hr]; rfl⟩
  case atom v =>
    by_cases hr : rigid flex (.atom v) = true
    · exact ⟨.const (.atom v), by simp [positive, hr]⟩
    · have hv : v ∈ flex := by simpa [rigid, BoolExpr.atoms] using hr
      obtain ⟨i, hi⟩ := HornPropagation.atomFin_exists hv
      exact ⟨.var i, by simp [positive, hr, hi]⟩
  case and a b ha hb iha ihb | or a b ha hb iha ihb =>
    obtain ⟨ra, hra⟩ := iha
    obtain ⟨rb, hrb⟩ := ihb
    all_goals simp [positive, hra, hrb]
    all_goals split <;> simp

theorem horn_complete {flex e} (h : RelativeHorn flex e) :
    ∃ r, horn flex e = some r := by
  induction h
  case rigid e hr => exact ⟨.const e, by rw [horn.eq_def, hr]; rfl⟩
  case atom v =>
    by_cases hr : rigid flex (.atom v) = true
    · exact ⟨.const (.atom v), by simp [horn, hr]⟩
    · have hv : v ∈ flex := by simpa [rigid, BoolExpr.atoms] using hr
      obtain ⟨i, hi⟩ := HornPropagation.atomFin_exists hv
      exact ⟨.var i, by simp [horn, hr, hi]⟩
  case and a b ha hb iha ihb =>
    obtain ⟨ra, hra⟩ := iha
    obtain ⟨rb, hrb⟩ := ihb
    simp [horn, hra, hrb]
    split <;> simp
  case imp a b ha hb ihb =>
    obtain ⟨ra, hra⟩ := positive_complete ha
    obtain ⟨rb, hrb⟩ := ihb
    simp [horn, hra, hrb]
    split <;> simp

theorem positive_iff (flex : List Nat) (e : BoolExpr) :
    (∃ r, positive flex e = some r) ↔ RelativePositive flex e :=
  ⟨fun ⟨_, h⟩ => positive_supported h, positive_complete⟩

theorem horn_iff (flex : List Nat) (e : BoolExpr) :
    (∃ r, horn flex e = some r) ↔ RelativeHorn flex e :=
  ⟨fun ⟨_, h⟩ => horn_supported h, horn_complete⟩

theorem eliminate_iff (flex : List Nat) (e : BoolExpr) :
    (∃ s, eliminate flex e = some s) ↔ RelativeHorn flex e := by
  rw [← horn_iff]
  cases hr : horn flex e <;> simp [eliminate, hr]

theorem RelativePositive.of_positive (flex : List Nat) {e : BoolExpr} (h : e.IsPositive) :
    RelativePositive flex e := by
  induction h
  case const => exact .rigid (by simp [SymbolicModes.rigid, BoolExpr.atoms])
  case atom => exact .atom _
  case and a b ha hb iha ihb => exact .and iha ihb
  case or a b ha hb iha ihb => exact .or iha ihb

theorem RelativeHorn.of_horn (flex : List Nat) {e : BoolExpr} (h : e.IsHorn) :
    RelativeHorn flex e := by
  induction h
  case const => exact .rigid (by simp [SymbolicModes.rigid, BoolExpr.atoms])
  case atom => exact .atom _
  case and a b ha hb iha ihb => exact .and iha ihb
  case imp a b ha hb ihb => exact .imp (.of_positive flex ha) ihb

/-- Reification turns the symbolic vector into a single syntactic modality
substitution. Original definedness guards are included in `boundsModeFormula`. -/
theorem eliminate_modal_correct {flex cs s}
    (h : eliminate flex (boundsModeFormula cs) = some s)
    (ms : ModVar → ModExpr) (hm : ∀ v, s.mode v = some (ms v)) (η : ModVar → Mode) :
    s.obligation.eval (encodeModes η) = true ↔
      ModeModels (cs.map (Constraint.subst TypeExpr.var ms)) η := by
  let σ := fun i => (s.substitute i).eval (encodeModes η)
  have hv : (fun v => (ms v).eval (some ∘ η)) = some ∘ projectedModes σ :=
    funext fun v => Elimination.mode_eval (hm v) η
  have hc (c : Constraint) : ModeSatisfies η (c.subst TypeExpr.var ms) ↔
      ModeSatisfies (projectedModes σ) c := by
    cases c <;> simp only [Constraint.subst, ModeSatisfies, ModExpr.Below,
      ModExpr.WellFormed, ModExpr.eval_subst, hv]
  have he := boundsModeFormula_correct cs σ
  rw [eliminate_witness h (encodeModes η)] at he
  rw [he]
  simp only [ModeModels, List.forall_mem_map, hc]

theorem reifyAtom_vars {axis i m} (h : reifyAtom axis i = some m) :
    m.vars = {atomVariable i} := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize he : i % 3 = k at hi
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals cases axis <;> simp [reifyAtom, he] at h
  all_goals cases h; simp [ModExpr.vars, ModExpr.epsilon]

/-- Reification introduces no variables beyond those named by source atoms. -/
theorem reify_variables {axis e m} (h : reify axis e = some m) :
    ∀ v ∈ m.vars, ∃ i ∈ e.atoms, atomVariable i = v := by
  induction e generalizing m
  case const b => cases h; simp [ModExpr.vars]
  case atom i => simp [reifyAtom_vars h, BoolExpr.atoms]
  case and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    cases ha : reify axis a <;> cases hb : reify axis b <;> simp [reify, ha, hb] at h
    all_goals cases h
    all_goals cases axis <;> simp only [ModExpr.vars, Finset.mem_union]
    all_goals intro v hv
    all_goals rcases hv with hv | hv
    all_goals first
      | exact let ⟨i, hi, he⟩ := iha ha v hv
          ⟨i, by simp [BoolExpr.atoms, hi], he⟩
      | exact let ⟨i, hi, he⟩ := ihb hb v hv
          ⟨i, by simp [BoolExpr.atoms, hi], he⟩

end ModalityInference.SymbolicModes
