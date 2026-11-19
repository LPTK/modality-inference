import ModalityInference.ComparisonExecutableTableFormula
import ModalityInference.Proofs.ComparisonObserverMachineFormula

/-! Exact evaluation of constructor-table formulas against the executable
checker on the rows selected by the same Boolean assignment. -/
namespace ModalityInference.ComparisonExecutableTableFormula

open ComparisonExecutableTables ComparisonObserverMachineFormula

variable {M A O : Type*} (observations : List O) (embed : A → O → BoolExpr)
  (le : M → M → Bool) (p q : Bool) (world : Nat → Bool)

@[simp] theorem below_eval (x y : O → BoolExpr) :
    (below observations x y).eval world =
      ComparisonExecutableTables.below observations (fun o => (x o).eval world)
        (fun o => (y o).eval world) := by
  simp [below, ComparisonExecutableTables.below, BoolExpr.eval]

@[simp] theorem direction_eval (x y : O → BoolExpr) :
    (direction observations p x y).eval world =
      ComparisonExecutableTables.direction observations p (fun o => (x o).eval world)
        (fun o => (y o).eval world) := by
  cases p <;> simp [direction, ComparisonExecutableTables.direction]

@[simp] theorem compatible_eval (a b : Row M A) :
    (compatible observations embed le p q a b).eval world =
      ComparisonExecutableTables.compatible observations (fun a o => (embed a o).eval world)
        le p q a b := by
  simp [compatible, ComparisonExecutableTables.compatible, BoolExpr.eval]

theorem check_eval (rows : List (Row M A)) (present : Row M A → BoolExpr) :
    (check observations embed le p q rows present).eval world =
      ComparisonExecutableTables.check observations (fun a o => (embed a o).eval world)
        le p q (selected rows present world) := by
  simp only [check, all_map_eval, BoolExpr.eval, compatible_eval,
    ComparisonExecutableTables.check, selected, List.all_filter]

private theorem any_map_eval {α : Type*} (xs : List α) (f : α → BoolExpr) :
    (BoolExpr.any (xs.map f)).eval world = xs.any (fun x => (f x).eval world) := by
  induction xs <;> simp_all [BoolExpr.any, BoolExpr.eval]

theorem extend_eval (rows : List (Row M A)) (present : Row M A → BoolExpr)
    (m : M) (x y : O → BoolExpr) (o : O) :
    (extend observations embed le p q rows present m x y o).eval world =
      ComparisonExecutableTables.extend observations (fun a o => (embed a o).eval world)
        le p q (selected rows present world) m
        (fun o => (x o).eval world) (fun o => (y o).eval world) o := by
  simp only [extend, any_map_eval, BoolExpr.eval, direction_eval,
    ComparisonExecutableTables.extend, selected, List.any_filter]

end ModalityInference.ComparisonExecutableTableFormula
