import ModalityInference.Proofs.SolverFlexible
import ModalityInference.Proofs.ModeConsistency

/-! Modal self-equality has finite solutions despite a syntactic occurrence. -/
namespace ModalityInference

theorem Entails.equal_subtypes {Δ v t} :
    Entails Δ (.equal v t) ↔ EntailsAll Δ [.sub (.var v) t, .sub t (.var v)] := by
  simp [EntailsAll, Entails, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds,
    ModeModels, and_left_comm, and_comm]

theorem Rewrites.equal_subtypes (s : RewriteConfig) (v : TypeVar) (t : Ty) :
    Rewrites {s with pending := .equal v t :: s.pending}
      {s with pending := .sub (.var v) t :: .sub t (.var v) :: s.pending} := by
  simpa using (Rewrites.equivalence (s := s) (cs := [.equal v t])
    (ds := [.sub (.var v) t, .sub t (.var v)])
    (fun Δ => by simpa [EntailsAll] using (Entails.equal_subtypes (Δ := Δ) (v := v) (t := t))))

namespace ModalEquality

/-- Restore the former occurs-rejection branch; all other transitions are the
unchanged executable transitions. Duplicate discharge still takes precedence. -/
def formerStep (s : SolverState) : RunResult SolverState :=
  match s.pending with
  | [] => solverStep s
  | c :: _ =>
    let c := (s.substitution.constraint c).normalize
    if s.seen.contains c then solverStep s else
    match c with
    | .equal (.flex n) t =>
      if t == .var (.flex n) then solverStep s
      else if t.typeVariables.contains (.flex n) then .rejected "occurs check failed"
      else solverStep s
    | _ => solverStep s

def formerWorklist : Nat → SolverState → RunResult SolverState
  | 0, _ => .exhausted
  | fuel + 1, s => if s.pending.isEmpty then .success s else do
      let next ← formerStep s
      formerWorklist fuel next

/-- The former solve entry with its empty, hence validated, initial substitution. -/
def formerSolve (fuel : Nat) (cs : Bounds) : RunResult Solved := do
  checkShapes fuel cs
  let s ← formerWorklist fuel
    {pending := cs, nextType := cs.freshTypeIndex, nextMode := cs.freshModeIndex}
  let witness ← satisfiableModes fuel s.bounds
  return ⟨s.substitution, s.bounds, witness, s.nextType, s.nextMode, s.trace.reverse⟩

def bounds : Bounds := [.equal (.flex 0) (.modal (.var (.flex 0)) (.const Mode.bottom))]

def model : GroundAssignment := residualAssignment (fun _ => Mode.identity)

theorem flexible : bounds.Flexible := by
  simp [bounds, Constraint.Flexible, TypeExpr.Flexible, ModExpr.Flexible]

theorem ground_model : GroundModels model bounds := by
  intro c hc
  simp only [bounds, List.mem_singleton] at hc
  subst c
  exact ⟨.unit Mode.absorbing, rfl, .refl, .refl⟩

theorem satisfiable : BoundsSatisfiable bounds :=
  let hf := bounds.flexible_iff.mp flexible
  ground_model.boundsSatisfiable hf.1 hf.2

theorem former_rejects (fuel : Nat) :
    formerSolve (fuel + 2) bounds = .rejected "occurs check failed" := by
  rfl

theorem former_never_succeeds (fuel : Nat) : ∀ result, formerSolve fuel bounds ≠ .success result := by
  cases fuel with
  | zero => simp [formerSolve, checkShapes, checkShapePairs, bind, RunResult.bind]
  | succ fuel =>
    cases fuel with
    | zero => intro result h; cases h
    | succ fuel => simp [show fuel + 1 + 1 = fuel + 2 from rfl, former_rejects]

theorem former_no_eventual_success :
    ¬ ∃ n, ∀ fuel ≥ n, ∃ result, formerSolve fuel bounds = .success result := by
  rintro ⟨n, hn⟩
  obtain ⟨result, hr⟩ := hn n (by omega)
  exact former_never_succeeds n result hr

theorem corrected_succeeds (fuel : Nat) :
    ∃ result, solve (fuel + 12) bounds = .success result := by
  let s : SolverState := match runSolver 12
      {pending := bounds, nextType := bounds.freshTypeIndex, nextMode := bounds.freshModeIndex} with
    | .success s => s
    | _ => {pending := []}
  have hh : (boundsModeFormula s.bounds).IsHorn := by repeat' constructor
  have hf : HornPropagation.requiredFuel (boundsModeFormula s.bounds) ≤ (fuel + 12) := by
    simp only [HornPropagation.requiredFuel, HornPropagation.domain, List.length_mergeSort]
    change 6 ≤ fuel + 12
    omega
  obtain ⟨model, hm⟩ := (HornPropagation.checkFormula_satisfiable_iff hh hf).mpr
    ⟨fun n => n % 3 == 2, by decide⟩
  have hw : satisfiableModes (fuel + 12) s.bounds =
      .success (ModeAssignment.ofBooleans s.bounds model.eval) := by
    rw [satisfiableModes, ModeConsistency.solve_of_polarized hh]
    simp [HornPropagation.satisfiableModes, hm, bind, pure, RunResult.bind]
  refine ⟨⟨s.substitution, s.bounds, ModeAssignment.ofBooleans s.bounds model.eval,
    s.nextType, s.nextMode, s.trace.reverse⟩, ?_⟩
  change (do
    let w ← satisfiableModes (fuel + 12) s.bounds
    pure (⟨s.substitution, s.bounds, w, s.nextType, s.nextMode, s.trace.reverse⟩ : Solved)) = _
  simp only [hw, bind, pure, RunResult.bind]

theorem corrected_eventual_success :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel bounds = .success result := by
  refine ⟨12, ?_⟩
  intro fuel hf
  simpa only [Nat.sub_add_cancel hf] using corrected_succeeds (fuel - 12)

end ModalEquality
end ModalityInference
