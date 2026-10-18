import ModalityInference.Subsumption

/-! Synchronous Horn propagation with one scalar join per conclusion.
Antecedents read the input valuation while conclusions accumulate separately.
The compiler replacement preserves the existing decision procedure exactly. -/

namespace RightExpr

private theorem mapping_ext {left right : Mapping α n}
    (h : ∀ i, left.get i = right.get i) : left = right := by
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

/-- One synchronous pass accumulates conclusions in `output`, while every
antecedent reads the fixed input valuation. -/
def updateAccum [HeytingAlgebra α] (input : Mapping α n) (c : α) :
    RightExpr α n → Mapping α n → Mapping α n
  | .var i, output => Mapping.update output i c
  | .const _, output => output
  | .meet a b, output => updateAccum input c b (updateAccum input c a output)
  | .imply a b, output => updateAccum input (c ⊓ a.eval input) b output

theorem updateAccum_eq [HeytingAlgebra α] (r : RightExpr α n)
    (input output : Mapping α n) (c : α) (h : input ≤ output) :
    updateAccum input c r output = output ⊔ update input c r := by
  induction r generalizing output c with
  | var i =>
    apply mapping_ext
    intro j
    by_cases he : j = i
    · subst i
      simp only [updateAccum, update, Mapping.get_sup, Mapping.get_update_same]
      rw [← sup_assoc, sup_eq_left.mpr (h j)]
    · simp only [updateAccum, update, Mapping.get_sup, Mapping.get_update_diff _ _ _ _ he]
      exact (sup_eq_left.mpr (h j)).symm
  | const c' =>
    apply mapping_ext
    intro j
    simp only [updateAccum, update, Mapping.get_sup]
    exact (sup_eq_left.mpr (h j)).symm
  | meet a b iha ihb =>
    rw [updateAccum, iha output c h]
    rw [ihb _ c (fun j => (h j).trans (Mapping.le_sup_left _ _ j))]
    apply mapping_ext
    intro j
    simp only [update, Mapping.get_sup, sup_assoc]
  | imply a b ih =>
    exact ih output (c ⊓ a.eval input) h

def updateLinear [HeytingAlgebra α] (input : Mapping α n) (c : α) (r : RightExpr α n) : Mapping α n :=
  updateAccum input c r input

theorem updateLinear_eq [HeytingAlgebra α] (input : Mapping α n) (c : α) (r : RightExpr α n) :
    updateLinear input c r = update input c r := by
  rw [updateLinear, updateAccum_eq r input input c (fun _ => le_rfl)]
  apply mapping_ext
  intro j
  simp only [Mapping.get_sup]
  exact sup_eq_right.mpr (update_le r input c j)

end RightExpr

namespace RightExpr

def iterateLinear [HeytingAlgebra α] (k : Nat) (input : Mapping α n) (c : α)
    (r : RightExpr α n) : Mapping α n :=
  match k with
  | 0 => input
  | k + 1 => iterateLinear k (updateLinear input c r) c r

theorem iterateLinear_eq [HeytingAlgebra α] (k : Nat) (input : Mapping α n) (c : α)
    (r : RightExpr α n) : iterateLinear k input c r = iterate k input c r := by
  induction k generalizing input with
  | zero => rfl
  | succ k ih =>
    simp only [iterateLinear, ih, updateLinear_eq, iterate_update_comm, iterate]

def hornSolveLinear [HeytingAlgebra α] (c : α) (r : RightExpr α n) : Mapping α n :=
  iterateLinear n (Mapping.const α n ⊥) c r

theorem hornSolveLinear_eq [HeytingAlgebra α]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (c : α) (r : RightExpr α n) : hornSolveLinear c r = hornSolve c r := by
  simp only [hornSolveLinear, hornSolve, iterateLinear_eq, iterate_opt_eq_iterate]

end RightExpr

namespace Equation

def decideLinear [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)] (eq : Equation α n) : Bool :=
  let S := RightExpr.hornSolveLinear ⊤ eq.right
  if eq.right.eval S ≤ (LeftCanonical.fromLeftExpr S eq.left).meetConst then true else false

theorem decideLinear_correct [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)] (eq : Equation α n) :
    decideLinear eq = decide eq := by
  simp only [decideLinear, RightExpr.hornSolveLinear_eq, decide, find_counterexample, solveSingleVar]
  split <;> rfl

@[csimp] theorem decide_eq_decideLinear : @decide = @decideLinear := by
  funext α n _ _ _ eq
  exact (decideLinear_correct eq).symm

end Equation
