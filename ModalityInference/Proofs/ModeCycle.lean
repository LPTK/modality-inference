import ModalityInference.Proofs.SolverFlexible
import ModalityInference.Proofs.ModeConsistency

/-! A tied minimum allowed residual swaps to erase a false inequality. -/
namespace ModalityInference.ModeCycle

/-- The modality transition before strict orientation of the `sub2` swap. -/
def formerMode (s : SolverState) (a b : ModExpr) : RunResult SolverState := do
  let guard := [Constraint.defined a, Constraint.defined b]
  if a.freeVariables.isEmpty && b.freeVariables.isEmpty then
    if checkModeConstraint (fun _ => none) (.mode a b) then return s.emit .constant []
    else return ← .rejected "false or undefined concrete modality inequality"
  if a == b then return s.emit .hypothesis guard
  match a, b with
  | .join x y, _ => return s.emit .andOr [.mode x b, .mode y b]
  | _, .meet x y => return s.emit .andOr [.mode a x, .mode a y]
  | .var _, _ | _, .var _ => return (recordModeBound s a b).emit .defined guard
  | .leftResidual x y, _ =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar b.minVar then
      return s.emit .sub1 (guard ++ [.mode x (.compose y b)])
    else if ModExpr.minimumLE y.minVar x.minVar && y.minVar != x.minVar &&
        ModExpr.minimumLE y.minVar b.minVar then
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

def formerSolve (fuel : Nat) (cs : Bounds) : RunResult Solved := do
  checkShapes fuel cs
  let s ← formerWorklist fuel
    {pending := cs, nextType := cs.freshTypeIndex, nextMode := cs.freshModeIndex}
  let witness ← satisfiableModes fuel s.bounds
  return ⟨s.substitution, s.bounds, witness, s.nextType, s.nextMode, s.trace.reverse⟩

def modeVar : ModExpr := .var (.flex 0)
def left : ModExpr := .compose modeVar (.const Mode.bottom)
def right : ModExpr := .compose modeVar (.const Mode.many)
def inequality : Constraint := .mode (.leftResidual (.const Mode.absorbing) left) right
def bounds : Bounds := [inequality, .mode modeVar (.const Mode.identity)]

theorem former_succeeds : ∃ result, formerSolve 100 bounds = .success result ∧
    result.substitution = {} ∧
    satisfiableModes 100 result.bounds = .success result.witness := by
  let s : SolverState := match formerWorklist 100
      {pending := bounds, nextType := bounds.freshTypeIndex, nextMode := bounds.freshModeIndex} with
    | .success s => s
    | _ => {pending := []}
  have hh : (boundsModeFormula s.bounds).IsHorn := by repeat' constructor
  have hf : HornPropagation.requiredFuel (boundsModeFormula s.bounds) ≤ 100 := by
    simp only [HornPropagation.requiredFuel, HornPropagation.domain, List.length_mergeSort]
    decide
  obtain ⟨model, hm⟩ := (HornPropagation.checkFormula_satisfiable_iff hh hf).mpr
    ⟨fun n => n % 3 == 2, by decide⟩
  have hw : satisfiableModes 100 s.bounds =
      .success (ModeAssignment.ofBooleans s.bounds model.eval) := by
    rw [satisfiableModes, ModeConsistency.solve_of_polarized hh]
    simp [HornPropagation.satisfiableModes, hm, bind, pure, RunResult.bind]
  refine ⟨⟨s.substitution, s.bounds, ModeAssignment.ofBooleans s.bounds model.eval,
    s.nextType, s.nextMode, s.trace.reverse⟩, ?_, rfl, hw⟩
  change (do
    let w ← satisfiableModes 100 s.bounds
    pure (⟨s.substitution, s.bounds, w, s.nextType, s.nextMode, s.trace.reverse⟩ : Solved)) = _
  simp only [hw, bind, pure, RunResult.bind]

theorem no_model (η : ModVar → Mode) : ¬ ModeModels bounds η := by
  intro h
  simp [ModeModels, bounds, ModeSatisfies, inequality, ModExpr.Below, ModExpr.eval,
    modeVar, left, right, Mode.leftResidual, Mode.compose, Mode.absorbing,
    Mode.bottom, Mode.many, Mode.identity, Mode.le] at h

theorem unsatisfiable : ¬ BoundsSatisfiable bounds :=
  fun h => let ⟨ρ, hρ⟩ := h.ground; no_model ρ.modes hρ.modeModels

theorem former_unsound : ∃ result, formerSolve 100 bounds = .success result ∧
    ¬ Solution bounds result.bounds result.substitution := by
  obtain ⟨result, hs, hσ, hm⟩ := former_succeeds
  refine ⟨result, hs, fun h => no_model result.witness.total ?_⟩
  rw [hσ] at h
  simpa [ModeModels, bounds, ModeSatisfies, inequality] using
    And.intro ((h inequality (by decide)).denote (satisfiableModes_sound hm))
      ((h (.mode modeVar (.const Mode.identity)) (by decide)).denote (satisfiableModes_sound hm))

theorem corrected_retains (s : SolverState) :
    stepMode s (.leftResidual (.const Mode.absorbing) left) right =
      .success (s.retain .projection inequality) := rfl

theorem corrected_rejects (fuel : Nat) :
    solve (fuel + 100) bounds = .rejected "inconsistent modality bounds" := by
  let s : SolverState := match runSolver 100
      {pending := bounds, nextType := bounds.freshTypeIndex, nextMode := bounds.freshModeIndex} with
    | .success s => s
    | _ => {pending := []}
  have hh : (boundsModeFormula s.bounds).IsHorn := by repeat' constructor
  have hf : HornPropagation.requiredFuel (boundsModeFormula s.bounds) ≤ fuel + 100 := by
    simp only [HornPropagation.requiredFuel, HornPropagation.domain, List.length_mergeSort]
    change 73 ≤ fuel + 100
    omega
  have hn : ¬ ∃ σ, (boundsModeFormula s.bounds).eval σ = true := by
    rintro ⟨σ, hσ⟩
    have hm := (boundsModeFormula_correct s.bounds σ).mp hσ
    apply no_model (projectedModes σ)
    intro c hc
    apply hm c
    change c ∈ [.defined modeVar, .mode modeVar (.const Mode.identity), inequality]
    simp only [bounds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  have hw : satisfiableModes (fuel + 100) s.bounds =
      .rejected "inconsistent modality bounds" := by
    rw [satisfiableModes, ModeConsistency.solve_of_polarized hh]
    simp [HornPropagation.satisfiableModes,
      (HornPropagation.checkFormula_rejected_iff hh hf).mpr hn, bind, RunResult.bind]
  change (do
    let w ← satisfiableModes (fuel + 100) s.bounds
    pure (⟨s.substitution, s.bounds, w, s.nextType, s.nextMode, s.trace.reverse⟩ : Solved)) = _
  simp only [hw, bind, RunResult.bind]

end ModalityInference.ModeCycle
