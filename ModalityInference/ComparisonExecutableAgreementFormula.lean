import ModalityInference.ComparisonExecutableAgreement
import ModalityInference.ComparisonExecutableTableFormula

/-! Symbolic validation of a defined-algebra embedding. Domain membership is a
formula, so checks are guarded over a fixed finite carrier. -/
namespace ModalityInference.ComparisonExecutableAgreementFormula

abbrev Vector (M O : Type*) := M → O → BoolExpr

def decode {M O : Type*} (world : Nat → Bool) (x : Vector M O) :
    ComparisonExecutableAgreement.Vector M O := fun m o => (x m o).eval world

structure Images (D M O : Type*) where
  domainLe : D → D → BoolExpr
  join : D → D → Vector M O
  meet : D → D → Vector M O
  action : M → D → Vector M O
  prod : D → D → Vector M O
  sum : D → D → Vector M O
  fn : D → D → Vector M O
  vectorProd : Vector M O → Vector M O → Vector M O
  vectorSum : Vector M O → Vector M O → Vector M O
  vectorFn : Vector M O → Vector M O → Vector M O

def vectorEq {M O : Type*} (indices : List M) (observations : List O)
    (x y : Vector M O) : BoolExpr :=
  .all (indices.map fun m => .all (observations.map fun o => .equal (x m o) (y m o)))

def vectorBelow {M O : Type*} (indices : List M) (observations : List O)
    (x y : Vector M O) : BoolExpr :=
  .all (indices.map fun m => ComparisonExecutableTableFormula.below observations (x m) (y m))

def guarded {D : Type*} (values : List D) (allowed : D → BoolExpr) (test : D → BoolExpr) : BoolExpr :=
  .all (values.map fun x => .imp (allowed x) (test x))

variable {D M O : Type*} (values : List D) (indices : List M) (observations : List O)
  (allowed : D → BoolExpr) (indexLe : M → M → Bool) (mul : M → M → M)
  (E : Images D M O) (j : D → Vector M O)

def indexCheck : BoolExpr := guarded values allowed fun x =>
  .all (indices.map fun m => .all (indices.map fun n =>
    .imp (.const (indexLe m n)) (ComparisonExecutableTableFormula.below observations (j x m) (j x n))))

def latticeCheck : BoolExpr := guarded values allowed fun x => guarded values allowed fun y =>
  .and (vectorEq indices observations (E.join x y) (fun m o => .or (j x m o) (j y m o)))
    (vectorEq indices observations (E.meet x y) (fun m o => .and (j x m o) (j y m o)))

def reflectCheck : BoolExpr := guarded values allowed fun x => guarded values allowed fun y =>
  .imp (vectorBelow indices observations (j x) (j y)) (E.domainLe x y)

def actionCheck : BoolExpr := .all (indices.map fun m => guarded values allowed fun x =>
  vectorEq indices observations (fun n => j x (mul m n)) (E.action m x))

def constructorCheck (image : D → D → Vector M O)
    (vectorOp : Vector M O → Vector M O → Vector M O) : BoolExpr :=
  guarded values allowed fun x => guarded values allowed fun y =>
    vectorEq indices observations (vectorOp (j x) (j y)) (image x y)

def check : BoolExpr :=
  .and (.and (.and (.and (.and (.and
    (indexCheck values indices observations allowed indexLe j)
    (latticeCheck values indices observations allowed E j))
    (reflectCheck values indices observations allowed E j))
    (actionCheck values indices observations allowed mul E j))
    (constructorCheck values indices observations allowed j E.prod E.vectorProd))
    (constructorCheck values indices observations allowed j E.sum E.vectorSum))
    (constructorCheck values indices observations allowed j E.fn E.vectorFn)

end ModalityInference.ComparisonExecutableAgreementFormula
