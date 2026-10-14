import ModalityInference.Proofs.SolverFlexible
import ModalityInference.Proofs.ModeConsistency
import ModalityInference.Proofs.ConstraintModels

/-! Unbounded syntactic growth from redundant modality-bound propagation. -/
namespace ModalityInference.ModePropagation

def formerRecord (s : SolverState) (a b : ModExpr) : SolverState :=
  let more := s.bounds.flatMap fun c => match c with
    | .mode x y =>
      (if y == a then [Constraint.mode x b] else []) ++
      (if b == x then [Constraint.mode a y] else [])
    | _ => []
  (s.retain .modeBound (.mode a b)).emit .modeBound more

def formerMode (s : SolverState) (a b : ModExpr) : RunResult SolverState := do
  let guard := [Constraint.defined a, Constraint.defined b]
  if a.freeVariables.isEmpty && b.freeVariables.isEmpty then
    if checkModeConstraint (fun _ => none) (.mode a b) then return s.emit .constant []
    else return ← .rejected "false or undefined concrete modality inequality"
  if a == b then return s.emit .hypothesis guard
  match a, b with
  | .join x y, _ => return s.emit .andOr [.mode x b, .mode y b]
  | _, .meet x y => return s.emit .andOr [.mode a x, .mode a y]
  | .var _, _ | _, .var _ => return (formerRecord s a b).emit .defined guard
  | .leftResidual x y, _ =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar b.minVar then
      return s.emit .sub1 (guard ++ [.mode x (.compose y b)])
    -- A tie with the right operand would permit two swaps followed by duplicate
    -- discharge of an unresolved inequality. Keep that constraint for projection.
    else if ModExpr.minimumLE y.minVar x.minVar && y.minVar != x.minVar &&
        ModExpr.minimumLE y.minVar b.minVar && y.minVar != b.minVar then
      return s.emit .sub2 (guard ++ [.mode (.leftResidual x b) y])
    else return s.retain .projection (.mode a b)
  | _, .rightResidual x y =>
    if ModExpr.minimumLE y.minVar x.minVar &&
        ModExpr.minimumLE y.minVar a.minVar && y.minVar != a.minVar then
      return s.emit .imp1 (guard ++ [.mode (.compose a x) y])
    else if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar a.minVar &&
        x.minVar != y.minVar && x.minVar != a.minVar then
      return s.emit .imp2 (guard ++ [.mode x (.rightResidual a y)])
    else return s.retain .projection (.mode a b)
  | .compose x y, _ =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar b.minVar then
      return s.emit .left1 (guard ++ [.mode x (.rightResidual y b)])
    else if ModExpr.minimumLE y.minVar x.minVar && y.minVar != x.minVar &&
        ModExpr.minimumLE y.minVar b.minVar then
      return s.emit .left2 (guard ++ [.mode y (.rightResidual x b)])
    else return s.retain .projection (.mode a b)
  | _, .compose x y =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar a.minVar &&
        x.minVar != a.minVar then
      return s.emit .right1 (guard ++ [.mode (.leftResidual a y) x])
    else if ModExpr.minimumLE y.minVar x.minVar && ModExpr.minimumLE y.minVar a.minVar &&
        y.minVar != x.minVar && y.minVar != a.minVar then
      return s.emit .right2 (guard ++ [.mode (.leftResidual a x) y])
    else return s.retain .projection (.mode a b)
  | .close x, _ =>
    if ModExpr.minimumLE x.minVar b.minVar && x.minVar != b.minVar then
      return s.emit .close (guard ++ [.mode (.closeInv b) x])
    else return s.retain .projection (.mode a b)
  | _, _ => return s.retain .projection (.mode a b)


def formerStep (s : SolverState) : RunResult SolverState :=
  match s.pending with
  | [] => solverStep s
  | c :: rest =>
    let c := (s.substitution.constraint c).normalize
    if s.seen.contains c then solverStep s else
    match c with
    | .mode a b => formerMode {s with pending := rest, seen := c :: s.seen} a b
    | _ => solverStep s

def formerWorklist : Nat → SolverState → RunResult SolverState
  | 0, _ => .exhausted
  | fuel + 1, s => if s.pending.isEmpty then .success s else do
      let next ← formerStep s
      formerWorklist fuel next

def modeVar : ModExpr := .var (.flex 0)
def lower : ModExpr := .leftResidual modeVar (.const Mode.global)
def upper : Nat → ModExpr
  | 0 => .compose modeVar (.const Mode.many)
  | n + 1 => .compose (.const Mode.global) (upper n)

def loopBounds : Nat → Bounds
  | 0 => [.defined (upper 0), .mode modeVar (upper 0), .defined modeVar,
      .defined lower, .mode lower modeVar]
  | n + 1 => .defined (upper (n+1)) :: .mode modeVar (upper (n+1)) :: loopBounds n

def loopSeen : Nat → Bounds
  | 0 => loopBounds 0
  | n + 1 => .defined (upper (n+1)) :: .mode modeVar (upper (n+1)) ::
      .mode lower (upper n) :: loopSeen n

def loopState (n : Nat) (trace : List RewriteRule) : SolverState :=
  {pending := [.mode lower (upper n)], bounds := loopBounds n, seen := loopSeen n,
   nextMode := 1, trace := trace}

theorem upper_injective : Function.Injective upper := by
  intro n k h
  induction n generalizing k <;> cases k <;> simp_all [upper, modeVar]
  solve_by_elim

@[simp] theorem upper_eq {n k : Nat} : upper n = upper k ↔ n = k := upper_injective.eq_iff

@[simp] theorem upper_ne_var (n : Nat) (v : ModVar) : upper n ≠ .var v := by
  cases n <;> simp [upper]

@[simp] theorem upper_ne_lower (n : Nat) : upper n ≠ lower := by
  cases n <;> simp [upper, lower]

@[simp] theorem var_ne_upper (v : ModVar) (n : Nat) : .var v ≠ upper n :=
  (upper_ne_var n v).symm

@[simp] theorem lower_ne_upper (n : Nat) : lower ≠ upper n := (upper_ne_lower n).symm

@[simp] theorem upper_seen (k n : Nat) :
    Constraint.mode modeVar (upper k) ∈ loopSeen n ↔ k ≤ n := by
  induction n <;> simp_all [loopSeen, loopBounds, lower, modeVar, eq_comm]
  omega

@[simp] theorem defined_upper_seen (k n : Nat) :
    Constraint.defined (upper k) ∈ loopSeen n ↔ k ≤ n := by
  induction n <;> simp_all [loopSeen, loopBounds, modeVar, eq_comm]
  omega

@[simp] theorem lower_seen (k n : Nat) :
    Constraint.mode lower (upper k) ∈ loopSeen n ↔ k < n := by
  induction n <;> simp_all [loopSeen, loopBounds, lower, modeVar, eq_comm]
  omega

@[simp] theorem upper_bound (k n : Nat) :
    Constraint.mode modeVar (upper k) ∈ loopBounds n ↔ k ≤ n := by
  induction n <;> simp_all [loopBounds, lower, modeVar, eq_comm]
  omega

@[simp] theorem defined_upper_bound (k n : Nat) :
    Constraint.defined (upper k) ∈ loopBounds n ↔ k ≤ n := by
  induction n <;> simp_all [loopBounds, modeVar, eq_comm]
  omega

@[simp] theorem defined_var_seen (n : Nat) : Constraint.defined modeVar ∈ loopSeen n := by
  induction n <;> simp_all [loopSeen, loopBounds]

@[simp] theorem defined_lower_seen (n : Nat) : Constraint.defined lower ∈ loopSeen n := by
  induction n <;> simp_all [loopSeen, loopBounds]

@[simp] theorem upper_variables (n : Nat) : (upper n).freeVariables = [.flex 0] := by
  induction n <;> simp_all [upper, modeVar, ModExpr.freeVariables]

@[simp] theorem upper_eval_none (n : Nat) : (upper n).eval (fun _ => none) = none := by
  induction n <;> simp_all [upper, modeVar, ModExpr.eval]

@[simp] theorem upper_normalize (n : Nat) : (upper n).normalize = upper n := by
  induction n <;> simp_all [upper, modeVar, ModExpr.normalize, ModExpr.foldConstants,
    ModExpr.eval, Mode.global, Mode.identity, Mode.many]

@[simp] theorem upper_min (n : Nat) : (upper n).minVar = some 0 := by
  simp [ModExpr.minVar]

@[simp] theorem upper_subst (n : Nat) : (upper n).subst ({} : Substitution).mode = upper n := by
  induction n <;> simp_all [upper, modeVar, ModExpr.subst, Substitution.mode]

@[simp] theorem propagated (n k : Nat) :
    (loopBounds n).flatMap (fun c => match c with
      | .mode x y =>
        (if y == modeVar then [Constraint.mode x (upper k)] else []) ++
        (if upper k == x then [Constraint.mode modeVar y] else [])
      | _ => []) = [.mode lower (upper k)] := by
  induction n <;> simp_all [loopBounds, modeVar, lower]
  exact upper_ne_lower _

theorem lower_step (s : SolverState) (n : Nat) :
    formerMode s lower (upper n) = .success (s.emit .sub1
      [.defined lower, .defined (upper n), .mode modeVar (upper (n+1))]) := by
  cases n <;> simp [formerMode, lower, modeVar, upper, ModExpr.freeVariables,
    ModExpr.minVar, ModExpr.minimumLE, bind, pure, RunResult.bind]

theorem upper_step (s : SolverState) (n : Nat) :
    formerMode s modeVar (upper n) = .success ((formerRecord s modeVar (upper n)).emit
      .defined [.defined modeVar, .defined (upper n)]) := by
  cases n <;> simp [formerMode, modeVar, upper, ModExpr.freeVariables,
    bind, pure, RunResult.bind]

@[simp] theorem lower_normalize : lower.normalize = lower := rfl
@[simp] theorem lower_subst : lower.subst ({} : Substitution).mode = lower := rfl
@[simp] theorem var_normalize : modeVar.normalize = modeVar := rfl
@[simp] theorem var_subst : modeVar.subst ({} : Substitution).mode = modeVar := rfl
@[simp] theorem var_variables : modeVar.freeVariables = [.flex 0] := rfl

@[simp] theorem propagated_eq (n k : Nat) :
    (loopBounds n).flatMap (fun c => match c with
      | .mode x y =>
        (if y = modeVar then [Constraint.mode x (upper k)] else []) ++
        (if upper k = x then [Constraint.mode modeVar y] else [])
      | _ => []) = [.mode lower (upper k)] := by
  simpa only [beq_iff_eq] using propagated n k

theorem loop_unroll (fuel n : Nat) (trace : List RewriteRule) :
    formerWorklist (fuel + 6) (loopState n trace) =
      formerWorklist fuel (loopState (n+1)
        ([.defined, .hypothesis, .defined, .modeBound, .modeBound,
          .hypothesis, .hypothesis, .sub1] ++ trace)) := by
  simp [formerWorklist, loopState, formerStep, solverStep, Substitution.constraint,
    Constraint.subst, Constraint.normalize, SolverState.emit, SolverState.retain,
    lower_step, upper_step, formerRecord, bind, pure, RunResult.bind,
    show ¬n + 1 ≤ n by omega]
  rfl

theorem loop_short (fuel n : Nat) (trace : List RewriteRule) (hf : fuel < 6) :
    formerWorklist fuel (loopState n trace) = .exhausted := by
  rcases fuel with _ | _ | _ | _ | _ | _ | fuel
  all_goals first
    | omega
    | simp [formerWorklist, loopState, formerStep, solverStep, Substitution.constraint,
        Constraint.subst, Constraint.normalize, SolverState.emit, SolverState.retain,
        lower_step, upper_step, formerRecord, bind, pure, RunResult.bind,
        show ¬n + 1 ≤ n by omega]

theorem loop_exhausted (fuel n : Nat) (trace : List RewriteRule) :
    formerWorklist fuel (loopState n trace) = .exhausted := by
  induction fuel using Nat.strong_induction_on generalizing n trace with
  | h fuel ih =>
    by_cases hf : fuel < 6
    · exact loop_short fuel n trace hf
    · rw [show fuel = (fuel - 6) + 6 by omega, loop_unroll]
      exact ih (fuel - 6) (by omega) _ _

def bounds : Bounds := [.mode lower modeVar, .mode modeVar (upper 0)]
def initialState : SolverState := {pending := bounds, nextMode := 1}

theorem entry_unroll (fuel : Nat) : ∃ trace,
    formerWorklist (fuel + 6) initialState = formerWorklist fuel (loopState 0 trace) :=
  ⟨_, rfl⟩

theorem former_worklist_exhausted (fuel : Nat) :
    formerWorklist fuel initialState = .exhausted := by
  rcases fuel with _ | _ | _ | _ | _ | _ | fuel
  all_goals try rfl
  obtain ⟨trace, h⟩ := entry_unroll fuel
  exact h.trans (loop_exhausted fuel 0 trace)

/-- The former validated worklist entry, including the finite-shape precheck. -/
def formerRunSolver (fuel : Nat) (s : SolverState) : RunResult SolverState := do
  if !s.substitution.checkAcyclic then
    return ← .rejected "initial solver substitution is cyclic, duplicated, or not normalized"
  checkShapes fuel (s.pending ++ s.bounds)
  formerWorklist fuel s

/-- The former complete solve of this concrete, flexible input. -/
def formerSolve (fuel : Nat) : RunResult Solved := do
  let s ← formerRunSolver fuel initialState
  let witness ← satisfiableModes fuel s.bounds
  return ⟨s.substitution, s.bounds, witness, s.nextType, s.nextMode, s.trace.reverse⟩

theorem former_run_exhausted (fuel : Nat) :
    formerRunSolver fuel initialState = .exhausted := by
  cases fuel with
  | zero => rfl
  | succ fuel => exact former_worklist_exhausted (fuel + 1)

theorem former_solve_exhausted (fuel : Nat) : formerSolve fuel = .exhausted := by
  simp [formerSolve, former_run_exhausted, bind, RunResult.bind]

theorem no_former_termination :
    ¬ ∃ n, ∀ fuel ≥ n, formerRunSolver fuel initialState ≠ .exhausted :=
  fun ⟨n, hn⟩ => hn n le_rfl (former_run_exhausted n)

theorem former_no_eventual_success :
    ¬ ∃ n, ∀ fuel ≥ n, ∃ result, formerSolve fuel = .success result := by
  simp [former_solve_exhausted]
  exact fun n => ⟨n, le_rfl⟩

theorem flexible : bounds.Flexible := by
  simp [bounds, lower, upper, modeVar, Constraint.Flexible, ModExpr.Flexible]

theorem ground_model : GroundModels (residualAssignment (fun _ => Mode.bottom)) bounds := by
  simp [GroundModels, bounds, GroundSatisfies, ModExpr.Below, ModExpr.eval, lower, upper,
    modeVar, residualAssignment, Mode.leftResidual, Mode.le, Mode.global, Mode.many,
    Mode.bottom, Mode.compose]

theorem satisfiable : BoundsSatisfiable bounds :=
  let hf := bounds.flexible_iff.mp flexible
  ground_model.boundsSatisfiable hf.1 hf.2

theorem corrected_succeeds (fuel : Nat) :
    ∃ result, solve (fuel + 100) bounds = .success result := by
  let s : SolverState := match runSolver 100
      {pending := bounds, nextType := bounds.freshTypeIndex, nextMode := bounds.freshModeIndex} with
    | .success s => s
    | _ => {pending := []}
  have hh : (boundsModeFormula s.bounds).IsHorn := by repeat' constructor
  have hf : HornPropagation.requiredFuel (boundsModeFormula s.bounds) ≤ (fuel + 100) := by
    simp only [HornPropagation.requiredFuel, HornPropagation.domain, List.length_mergeSort]
    change 83 ≤ fuel + 100
    omega
  obtain ⟨model, hm⟩ := (HornPropagation.checkFormula_satisfiable_iff hh hf).mpr
    ⟨fun n => n % 3 == 2, by decide⟩
  have hw : satisfiableModes (fuel + 100) s.bounds =
      .success (ModeAssignment.ofBooleans s.bounds model.eval) := by
    rw [satisfiableModes, ModeConsistency.solve_of_polarized hh]
    simp [HornPropagation.satisfiableModes, hm, bind, pure, RunResult.bind]
  refine ⟨⟨s.substitution, s.bounds, ModeAssignment.ofBooleans s.bounds model.eval,
    s.nextType, s.nextMode, s.trace.reverse⟩, ?_⟩
  change (do
    let w ← satisfiableModes (fuel + 100) s.bounds
    pure (⟨s.substitution, s.bounds, w, s.nextType, s.nextMode, s.trace.reverse⟩ : Solved)) = _
  simp only [hw, bind, pure, RunResult.bind]

theorem corrected_eventual_success :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel bounds = .success result :=
  ⟨100, fun fuel hf => by
    simpa only [Nat.sub_add_cancel hf] using corrected_succeeds (fuel - 100)⟩

theorem record_entails (s : SolverState) (a b : ModExpr) (Δ : Bounds) :
    EntailsAll Δ ((formerRecord s a b).pending ++ (formerRecord s a b).bounds) ↔
      EntailsAll Δ ((recordModeBound s a b).pending ++ (recordModeBound s a b).bounds) := by
  simp only [formerRecord, recordModeBound, SolverState.emit, EntailsAll,
    List.mem_append, or_imp, forall_and]
  refine ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨?_, h.1⟩, h.2⟩⟩
  have hb : Entails Δ (.mode a b) ∧ EntailsAll Δ s.bounds := by
    by_cases hc : Constraint.mode a b ∈ s.bounds <;> simp_all [SolverState.retain, EntailsAll]
  simp only [List.mem_flatMap, forall_exists_index, and_imp]
  intro c d hd hc
  cases d <;> simp only [List.not_mem_nil] at hc
  rcases List.mem_append.mp hc with hc | hc
  all_goals split_ifs at hc <;> simp_all only [beq_iff_eq, List.mem_singleton, List.not_mem_nil]
  all_goals first | exact Submode.trans (hb.2 _ hd) hb.1 | exact Submode.trans hb.1 (hb.2 _ hd)

theorem record_groundModels (s : SolverState) (a b : ModExpr) (ρ : GroundAssignment) :
    GroundModels ρ ((formerRecord s a b).pending ++ (formerRecord s a b).bounds) ↔
      GroundModels ρ ((recordModeBound s a b).pending ++ (recordModeBound s a b).bounds) :=
  GroundModels.entailment_equivalence (record_entails s a b) ρ

end ModalityInference.ModePropagation
