import ModalityInference.Proofs.HornPropagation
import ModalityInference.Proofs.Mode

/-! The finite coordinate schedule used for modality consistency. Its state is a
Boolean valuation; symbolic residual bounds are retained separately. -/
namespace ModalityInference.PropagationSchedule

open HornPropagation

/-- Start at the least valuation and propagate all currently activated demands. -/
def iterate (r : RightExpr Bool n) : Nat → Mapping Bool n
  | 0 => Mapping.const Bool n false
  | k + 1 => RightExpr.update (iterate r k) true r

@[simp] theorem iterate_zero (r : RightExpr Bool n) :
    iterate r 0 = Mapping.const Bool n false := rfl

@[simp] theorem iterate_succ (r : RightExpr Bool n) (k : Nat) :
    iterate r (k + 1) = RightExpr.update (iterate r k) true r := rfl

theorem iterate_eq_generic (r : RightExpr Bool n) (k : Nat) :
    iterate r k = RightExpr.iterate k (Mapping.const Bool n false) true r := by
  induction k <;> simp_all [iterate, RightExpr.iterate]

theorem iterate_eq_hornSolve (r : RightExpr Bool n) :
    iterate r n = RightExpr.hornSolve true r := by
  simp [RightExpr.hornSolve, RightExpr.iterate_opt_eq_iterate, iterate_eq_generic]

theorem iterate_stabilizes (r : RightExpr Bool n) : iterate r (n + 1) = iterate r n := by
  simpa only [iterate_eq_generic] using
    RightExpr.iterate_stabilizes (Mapping.const Bool n false) true r

theorem iterate_fixpoint (r : RightExpr Bool n) :
    RightExpr.update (iterate r n) true r = iterate r n := iterate_stabilizes r

theorem iterate_mono (r : RightExpr Bool n) {k l} (h : k ≤ l) :
    iterate r k ≤ iterate r l := by
  simpa only [iterate_eq_generic] using
    RightExpr.iterate_le_of_le (Mapping.const Bool n false) true r h

theorem iterate_least_fixpoint (r : RightExpr Bool n) (env : Mapping Bool n)
    (h : RightExpr.update env true r = env) : iterate r n ≤ env := by
  simpa only [iterate_eq_hornSolve] using RightExpr.hornSolve_least_fixpoint true r env h

/-- At saturation, atomic conclusions hold and every activated constant test passes. -/
def Saturated (r : RightExpr Bool n) (env : Mapping Bool n) : Prop :=
  AtomicObligations env true r ∧ RightExpr.eval_for_consts env r = true

theorem saturated_iff (r : RightExpr Bool n) (env : Mapping Bool n) :
    Saturated r env ↔ RightExpr.eval env r = true := by
  simpa only [Saturated, Bool.le_iff_imp, true_implies] using
    (eval_iff_atomicObligations_and_constants r env true).symm

/-- Exact correspondence between the executable result and the finite schedule. -/
theorem checkFormula_schedule_iff {e fuel model} :
    checkFormula fuel e = .success model ↔
      requiredFuel e ≤ fuel ∧ ∃ r, horn (domain e) e = some r ∧
        Saturated r (iterate r (domain e).length) ∧
        model = ⟨domain e, iterate r (domain e).length⟩ := by
  simpa only [saturated_iff, iterate_eq_hornSolve] using
    (checkFormula_success_iff (e := e) (fuel := fuel) (model := model))

theorem iterate_atomicObligations (r : RightExpr Bool n) :
    AtomicObligations (iterate r n) true r :=
  (update_fixed_iff_atomicObligations r (iterate r n) true).mp (iterate_fixpoint r)

theorem iterate_saturated_iff_constants (r : RightExpr Bool n) :
    Saturated r (iterate r n) ↔ RightExpr.eval_for_consts (iterate r n) r = true :=
  ⟨And.right, fun h => ⟨iterate_atomicObligations r, h⟩⟩

theorem iterate_satisfiable_iff (r : RightExpr Bool n) :
    Saturated r (iterate r n) ↔ ∃ env, RightExpr.eval env r = true := by
  simpa only [saturated_iff, iterate_eq_hornSolve] using hornSolve_satisfiable_iff r

theorem formula_schedule_satisfiable_iff {e atoms r} (hr : horn atoms e = some r) :
    Saturated r (iterate r atoms.length) ↔ ∃ σ, e.eval σ = true :=
  (iterate_satisfiable_iff r).trans (horn_satisfiable_iff hr).symm

theorem checkFormula_at_schedule_iff {e fuel r}
    (hr : horn (domain e) e = some r) (hf : requiredFuel e ≤ fuel) :
    checkFormula fuel e = .success ⟨domain e, iterate r (domain e).length⟩ ↔
      ∃ σ, e.eval σ = true := by
  simpa [checkFormula_schedule_iff, hr, hf] using formula_schedule_satisfiable_iff hr

theorem checkFormula_iteration {e fuel model} (h : checkFormula fuel e = .success model) :
    ∃ r, horn model.atoms e = some r ∧ model.values = iterate r model.atoms.length := by
  obtain ⟨_, r, hr, _, rfl⟩ := checkFormula_schedule_iff.mp h
  exact ⟨r, hr, rfl⟩

/-- This transitivity statement includes the existence of values for all operands,
so no lower or upper expression's partial-definedness guard is discarded. -/
theorem below_trans {η l m r} (hl : ModExpr.Below η l m) (hr : ModExpr.Below η m r) :
    ModExpr.Below η l r :=
  match hl, hr with
  | ⟨a, _b, ha, hb, hab⟩, ⟨_b', c, hb', hc, hbc⟩ =>
    ⟨a, c, ha, hc, Mode.le_trans hab ((Option.some.inj (hb.symm.trans hb')).symm ▸ hbc)⟩

/-- Every recorded lower/upper pair has its semantic cross-consequence in a model. -/
theorem lower_upper {cs η l v r} (h : ModeModels cs η)
    (hl : Constraint.mode l (.var v) ∈ cs) (hr : Constraint.mode (.var v) r ∈ cs) :
    ModExpr.Below η l r := below_trans (h _ hl) (h _ hr)

theorem checkFormula_modeModels {cs fuel model}
    (h : checkFormula fuel (boundsModeFormula cs) = .success model) :
    ModeModels cs (projectedModes model.eval) :=
  (boundsModeFormula_correct cs model.eval).mp (checkFormula_sound h)

theorem checkFormula_lower_upper {cs fuel model l v r}
    (h : checkFormula fuel (boundsModeFormula cs) = .success model)
    (hl : Constraint.mode l (.var v) ∈ cs) (hr : Constraint.mode (.var v) r ∈ cs) :
    ModExpr.Below (projectedModes model.eval) l r := lower_upper (checkFormula_modeModels h) hl hr

theorem iterate_least_model (r : RightExpr Bool n) (env : Mapping Bool n)
    (h : RightExpr.eval env r = true) : iterate r n ≤ env :=
  iterate_least_fixpoint r env (RightExpr.update_fixpoint r env true
    (Bool.le_iff_imp.mpr (fun _ => h)))

/-- Adding a cross-consequence changes neither the models nor their definedness. -/
theorem lower_upper_extension_iff {cs η l v r}
    (hl : Constraint.mode l (.var v) ∈ cs) (hr : Constraint.mode (.var v) r ∈ cs) :
    ModeModels (Constraint.mode l r :: cs) η ↔ ModeModels cs η :=
  ⟨fun h c hc => h c (List.mem_cons_of_mem _ hc),
    fun h c hc => (List.mem_cons.mp hc).elim
      (fun he => he ▸ lower_upper h hl hr) (h c)⟩

theorem satisfiableModes_lower_upper {cs fuel assignment l v r}
    (h : HornPropagation.satisfiableModes fuel cs = .success assignment)
    (hl : Constraint.mode l (.var v) ∈ cs) (hr : Constraint.mode (.var v) r ∈ cs) :
    ModExpr.Below assignment.total l r := by
  cases hm : checkFormula fuel (boundsModeFormula cs) <;>
    simp [HornPropagation.satisfiableModes, hm, bind, RunResult.bind] at h
  cases h
  exact lower_upper (ModeAssignment.ofBooleans_models (checkFormula_sound hm)) hl hr

end ModalityInference.PropagationSchedule
