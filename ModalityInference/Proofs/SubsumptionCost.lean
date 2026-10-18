import ModalityInference.SubsumptionLinear

/-! Scalar-operation certificates for the synchronous decision procedure.
A binary join, meet, implication, or order test costs one operation. Valuation
lookup, finite-map administration, and construction of constants are not scalar
operations. The measured interpreters follow the executable worker's control
flow and return its result together with the exact scalar count. -/
namespace ModalityCost

def leftSize : LeftExpr α n → Nat
  | .var _ | .const _ => 1
  | .join a b | .meet a b => 1 + leftSize a + leftSize b

def rightSize : RightExpr α n → Nat
  | .var _ | .const _ => 1
  | .meet a b => 1 + rightSize a + rightSize b
  | .imply a b => 1 + leftSize a + rightSize b

def leftOps : LeftExpr α n → Nat
  | .var _ | .const _ => 0
  | .join a b | .meet a b => leftOps a + leftOps b + 1

def rightOps : RightExpr α n → Nat
  | .var _ | .const _ => 0
  | .meet a b => rightOps a + rightOps b + 1
  | .imply a b => leftOps a + rightOps b + 1

def updateOps : RightExpr α n → Nat
  | .var _ => 1
  | .const _ => 0
  | .meet a b => updateOps a + updateOps b
  | .imply a b => leftOps a + 1 + updateOps b

def canonicalOps : LeftExpr α n → Nat
  | .var _ | .const _ => 0
  | .join a b => canonicalOps a + canonicalOps b + 6
  | .meet a b => canonicalOps a + canonicalOps b + 2

def evalLeft [HeytingAlgebra α] (input : Mapping α n) : LeftExpr α n → α × Nat
  | .var i => (input.get i, 0)
  | .const c => (c, 0)
  | .join a b =>
    let left := evalLeft input a
    let right := evalLeft input b
    (left.1 ⊔ right.1, left.2 + right.2 + 1)
  | .meet a b =>
    let left := evalLeft input a
    let right := evalLeft input b
    (left.1 ⊓ right.1, left.2 + right.2 + 1)

theorem evalLeft_spec [HeytingAlgebra α] (input : Mapping α n) (a : LeftExpr α n) :
    evalLeft input a = (a.eval input, leftOps a) := by
  induction a <;> simp_all [evalLeft, LeftExpr.eval, leftOps]

def evalRight [HeytingAlgebra α] (input : Mapping α n) : RightExpr α n → α × Nat
  | .var i => (input.get i, 0)
  | .const c => (c, 0)
  | .meet a b =>
    let left := evalRight input a
    let right := evalRight input b
    (left.1 ⊓ right.1, left.2 + right.2 + 1)
  | .imply a b =>
    let left := evalLeft input a
    let right := evalRight input b
    (left.1 ⇨ right.1, left.2 + right.2 + 1)

theorem evalRight_spec [HeytingAlgebra α] (input : Mapping α n) (a : RightExpr α n) :
    evalRight input a = (a.eval input, rightOps a) := by
  induction a <;> simp_all [evalRight, evalLeft_spec, RightExpr.eval, rightOps]

def propagate [HeytingAlgebra α] (input : Mapping α n) (c : α) :
    RightExpr α n → Mapping α n → Mapping α n × Nat
  | .var i, output => (Mapping.update output i c, 1)
  | .const _, output => (output, 0)
  | .meet a b, output =>
    let left := propagate input c a output
    let right := propagate input c b left.1
    (right.1, left.2 + right.2)
  | .imply a b, output =>
    let left := evalLeft input a
    let right := propagate input (c ⊓ left.1) b output
    (right.1, left.2 + 1 + right.2)

theorem propagate_spec [HeytingAlgebra α] (input : Mapping α n) (c : α)
    (a : RightExpr α n) (output : Mapping α n) :
    propagate input c a output = (a.updateAccum input c output, updateOps a) := by
  induction a generalizing output c <;>
    simp_all [propagate, evalLeft_spec, RightExpr.updateAccum, updateOps]

def iterate [HeytingAlgebra α] (k : Nat) (input : Mapping α n) (c : α)
    (a : RightExpr α n) : Mapping α n × Nat :=
  match k with
  | 0 => (input, 0)
  | k + 1 =>
    let step := propagate input c a input
    let rest := iterate k step.1 c a
    (rest.1, step.2 + rest.2)

theorem iterate_spec [HeytingAlgebra α] (k : Nat) (input : Mapping α n) (c : α)
    (a : RightExpr α n) :
    iterate k input c a = (RightExpr.iterateLinear k input c a, k * updateOps a) := by
  induction k generalizing input with
  | zero => simp [iterate, RightExpr.iterateLinear]
  | succ k ih =>
    simp [iterate, propagate_spec, ih, RightExpr.iterateLinear, RightExpr.updateLinear,
      Nat.add_mul, Nat.add_comm]

def canonical [HeytingAlgebra α] (input : Mapping α n) : LeftExpr α n → LeftCanonical α × Nat
  | .var i => (⟨⊥, input.get i⟩, 0)
  | .const c => (⟨⊤, c⟩, 0)
  | .join a b =>
    let left := canonical input a
    let right := canonical input b
    (⟨(left.1.joinConst ⊔ right.1.joinConst) ⊓
        (left.1.joinConst ⊔ right.1.meetConst) ⊓
        (left.1.meetConst ⊔ right.1.joinConst),
      left.1.meetConst ⊔ right.1.meetConst⟩,
      left.2 + right.2 + 6)
  | .meet a b =>
    let left := canonical input a
    let right := canonical input b
    (⟨left.1.joinConst ⊓ right.1.joinConst, left.1.meetConst ⊓ right.1.meetConst⟩,
      left.2 + right.2 + 2)

theorem canonical_spec [HeytingAlgebra α] (input : Mapping α n) (a : LeftExpr α n) :
    canonical input a = (LeftCanonical.fromLeftExpr input a, canonicalOps a) := by
  induction a <;> simp_all [canonical, LeftCanonical.fromLeftExpr, canonicalOps]

def decideMeasured [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    (eq : Equation α n) : Bool × Nat :=
  let solved := iterate n (Mapping.const α n ⊥) ⊤ eq.right
  let right := evalRight solved.1 eq.right
  let left := canonical solved.1 eq.left
  (if right.1 ≤ left.1.meetConst then true else false,
    solved.2 + right.2 + left.2 + 1)

theorem decideMeasured_spec [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)] (eq : Equation α n) :
    decideMeasured eq = (Equation.decideLinear eq,
      n * updateOps eq.right + rightOps eq.right + canonicalOps eq.left + 1) := by
  simp only [decideMeasured, iterate_spec, evalRight_spec, canonical_spec,
    Equation.decideLinear, RightExpr.hornSolveLinear]

theorem leftOps_le (a : LeftExpr α n) : leftOps a ≤ leftSize a := by
  induction a <;> simp_all [leftOps, leftSize] <;> omega

theorem rightOps_le (a : RightExpr α n) : rightOps a ≤ rightSize a := by
  induction a <;> simp_all only [rightOps, rightSize]
  all_goals try omega
  rename_i l r ih
  have hl := leftOps_le l
  omega

theorem updateOps_le (a : RightExpr α n) : updateOps a ≤ rightSize a := by
  induction a <;> simp_all only [updateOps, rightSize]
  all_goals try omega
  rename_i l r ih
  have hl := leftOps_le l
  omega

theorem canonicalOps_le (a : LeftExpr α n) : canonicalOps a ≤ 6 * leftSize a := by
  induction a <;> simp_all [canonicalOps, leftSize] <;> omega

end ModalityCost

namespace Equation

/-- The actual synchronous decision traversal uses at most this many primitive
Heyting operations, including its final order test. The extra hypothesis-size
term covers the zero-variable case and the final evaluation. -/
theorem decideLinear_operation_bound [HeytingAlgebra α]
    [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)] (eq : Equation α n) :
    (ModalityCost.decideMeasured eq).1 = decide eq ∧
    (ModalityCost.decideMeasured eq).2 ≤
      (n + 1) * ModalityCost.rightSize eq.right + 6 * ModalityCost.leftSize eq.left + 1 := by
  rw [ModalityCost.decideMeasured_spec, decideLinear_correct]
  refine ⟨rfl, ?_⟩
  have hu := Nat.mul_le_mul_left n (ModalityCost.updateOps_le eq.right)
  have hr := ModalityCost.rightOps_le eq.right
  have hl := ModalityCost.canonicalOps_le eq.left
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end Equation
