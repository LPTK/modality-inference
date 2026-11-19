import ModalityInference.ComparisonObserverRangeFormula
import ModalityInference.Proofs.ComparisonObserverMachineFormula

/-! Exact evaluation of symbolic range operations and finite table lookup. -/
namespace ModalityInference.ComparisonObserverRangeFormula

open ComparisonObserverMachineFormula ComparisonStructuralLayout

@[simp] theorem lookup_eval {count} (values : ComparisonObserverRangeEncoding.Bits count → BoolExpr)
    (input : Bits count) (world : Nat → Bool) :
    (lookup values input).eval world = (values (eval input world)).eval world := by
  induction count with
  | zero => exact congrArg (fun x => (values x).eval world) (Subsingleton.elim _ _)
  | succ n ih =>
    simp only [lookup, mux_eval, ih]
    have he : Fin.cases ((input 0).eval world) (eval (fun i => input i.succ) world) = eval input world :=
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)
    cases hx : (input 0).eval world <;>
      simpa only [hx, Bool.false_eq_true, if_false, if_true] using
        congrArg (fun x => (values x).eval world) he

variable {count : Nat} (data : Fin count → Fields count) (world : Nat → Bool)

@[simp] theorem op_eval (k : Constructor) (x y : Bits count) :
    eval (op data k x y) world =
      ComparisonObserverRangeEncoding.op (decode data world) k (eval x world) (eval y world) := by
  funext i
  simp only [eval, op, mux_eval, successor_eval,
    ComparisonObserverRangeEncoding.op, ComparisonObserverMachine.sign]
  cases k.dual <;> cases hl : ((data i).left k).eval world <;>
    simp [decode, hl, BoolExpr.eval]

@[simp] theorem admitted_eval (x : Bits count) :
    (admitted data x).eval world =
      ComparisonObserverRangeEncoding.admitted (decode data world) (eval x world) := by
  simp only [admitted, all_map_eval, rangeAt_eval, ComparisonObserverRangeEncoding.admitted, eval]

@[simp] theorem unit_eval :
    eval (unit data) world = ComparisonObserverRangeEncoding.unit (decode data world) := rfl

@[simp] theorem credit_eval :
    eval (credit data) world = ComparisonObserverRangeEncoding.credit (decode data world) := rfl

@[simp] theorem atom_eval (types : List TypeVar) (v : TypeVar) :
    eval (atom data types v) world = ComparisonObserverRangeEncoding.atom (decode data world) types v :=
  funext (fun i => ComparisonObserverMachineFormula.atom_eval types data i v world)

@[simp] theorem modal_eval (names : List ModVar) (m : ModExpr) (x : Bits count) :
    eval (modal data names m x) world =
      ComparisonObserverRangeEncoding.modal (decode data world) names m (eval x world) :=
  funext (fun i => action_eval names data i m (x i) world)

omit data in
@[simp] theorem le_eval (x y : Bits count) :
    (le x y).eval world = ComparisonObserverRangeEncoding.le (eval x world) (eval y world) := by
  simp only [le, all_map_eval, BoolExpr.eval, ComparisonObserverRangeEncoding.le, eval]

omit data in
@[simp] theorem equal_eval (x y : Bits count) :
    (equal x y).eval world = ComparisonObserverRangeEncoding.equal (eval x world) (eval y world) := by
  simp only [equal, all_map_eval, ComparisonObserverMachineFormula.equal_eval,
    ComparisonObserverRangeEncoding.equal, eval]

omit data in
@[simp] theorem join_eval (x y : Bits count) :
    eval (join x y) world = ComparisonObserverRangeEncoding.join (eval x world) (eval y world) := rfl

omit data in
@[simp] theorem meet_eval (x y : Bits count) :
    eval (meet x y) world = ComparisonObserverRangeEncoding.meet (eval x world) (eval y world) := rfl

end ModalityInference.ComparisonObserverRangeFormula
