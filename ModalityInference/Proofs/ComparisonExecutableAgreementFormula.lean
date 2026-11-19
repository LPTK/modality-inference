import ModalityInference.ComparisonExecutableAgreementFormula
import ModalityInference.Proofs.ComparisonExecutableTableFormula

/-! Exact semantics of guarded symbolic embedding checks. The image operations
are related to the original algebra operations before checking the finite carrier. -/
namespace ModalityInference.ComparisonExecutableAgreementFormula

open ComparisonObserverMachineFormula

variable {D M O : Type*} (world : Nat → Bool)

structure Realizes (E : Images D M O) (F : ComparisonExecutableAgreement.Operations D M O)
    (j : D → Vector M O) : Prop where
  domainLe : ∀ x y, (E.domainLe x y).eval world = F.domainLe x y
  join : ∀ x y, decode world (E.join x y) = decode world (j (F.join x y))
  meet : ∀ x y, decode world (E.meet x y) = decode world (j (F.meet x y))
  action : ∀ m x, decode world (E.action m x) = decode world (j (F.action m x))
  prod : ∀ x y, decode world (E.prod x y) = decode world (j (F.prod x y))
  sum : ∀ x y, decode world (E.sum x y) = decode world (j (F.sum x y))
  fn : ∀ x y, decode world (E.fn x y) = decode world (j (F.fn x y))
  vectorProd : ∀ x y, decode world (E.vectorProd (j x) (j y)) =
    F.vectorProd (decode world (j x)) (decode world (j y))
  vectorSum : ∀ x y, decode world (E.vectorSum (j x) (j y)) =
    F.vectorSum (decode world (j x)) (decode world (j y))
  vectorFn : ∀ x y, decode world (E.vectorFn (j x) (j y)) =
    F.vectorFn (decode world (j x)) (decode world (j y))

@[simp] theorem vectorEq_eval (indices : List M) (observations : List O) (x y : Vector M O) :
    (vectorEq indices observations x y).eval world =
      ComparisonExecutableAgreement.vectorEq indices observations (decode world x) (decode world y) :=
  by simp [vectorEq, ComparisonExecutableAgreement.vectorEq, decode]

@[simp] theorem vectorBelow_eval (indices : List M) (observations : List O) (x y : Vector M O) :
    (vectorBelow indices observations x y).eval world =
      ComparisonExecutableAgreement.vectorBelow indices observations (decode world x) (decode world y) :=
  by
    simp only [vectorBelow, all_map_eval, ComparisonExecutableTableFormula.below_eval,
      ComparisonExecutableAgreement.vectorBelow]
    rfl

@[simp] theorem guarded_eval (values : List D) (allowed test : D → BoolExpr) :
    (guarded values allowed test).eval world =
      (values.filter fun x => (allowed x).eval world).all (fun x => (test x).eval world) := by
  simp [guarded, BoolExpr.eval, List.all_filter]

@[simp] theorem decode_or (x y : Vector M O) :
    decode world (fun m o => .or (x m o) (y m o)) =
      fun m o => decode world x m o || decode world y m o := rfl

@[simp] theorem decode_and (x y : Vector M O) :
    decode world (fun m o => .and (x m o) (y m o)) =
      fun m o => decode world x m o && decode world y m o := rfl

@[simp] theorem decode_shift (mul : M → M → M) (m : M) (x : Vector M O) :
    decode world (fun n => x (mul m n)) = fun n => decode world x (mul m n) := rfl

theorem check_eval (values : List D) (indices : List M) (observations : List O)
    (allowed : D → BoolExpr) (E : Images D M O) (F : ComparisonExecutableAgreement.Operations D M O)
    (j : D → Vector M O) (h : Realizes world E F j) :
    (check values indices observations allowed F.indexLe F.mul E j).eval world =
      ComparisonExecutableAgreement.check (values.filter fun x => (allowed x).eval world)
        indices observations F (fun x => decode world (j x)) := by
  simp only [check, indexCheck, latticeCheck, reflectCheck, actionCheck, constructorCheck,
    BoolExpr.eval, all_map_eval, guarded_eval, vectorEq_eval, vectorBelow_eval,
    ComparisonExecutableTableFormula.below_eval, h.domainLe, h.join, h.meet, h.action,
    h.prod, h.sum, h.fn, h.vectorProd, h.vectorSum, h.vectorFn, decode_or, decode_and, decode_shift,
    ComparisonExecutableAgreement.check, ComparisonExecutableAgreement.indexCheck,
    ComparisonExecutableAgreement.latticeCheck, ComparisonExecutableAgreement.reflectCheck,
    ComparisonExecutableAgreement.actionCheck, ComparisonExecutableAgreement.constructorCheck]
  rfl

end ModalityInference.ComparisonExecutableAgreementFormula
