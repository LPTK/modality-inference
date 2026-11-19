import ModalityInference.ComparisonExecutableTables

/-! Exhaustive finite checks for the defined-algebra embedding. Operations
and all enumeration lists are supplied explicitly. -/
namespace ModalityInference.ComparisonExecutableAgreement

abbrev Vector (M O : Type*) := M → O → Bool

structure Operations (D M O : Type*) where
  domainLe : D → D → Bool
  indexLe : M → M → Bool
  join : D → D → D
  meet : D → D → D
  mul : M → M → M
  action : M → D → D
  prod : D → D → D
  sum : D → D → D
  fn : D → D → D
  vectorProd : Vector M O → Vector M O → Vector M O
  vectorSum : Vector M O → Vector M O → Vector M O
  vectorFn : Vector M O → Vector M O → Vector M O

def vectorEq {M O : Type*} (indices : List M) (observations : List O)
    (x y : Vector M O) : Bool :=
  indices.all fun m => observations.all fun o => x m o == y m o

def vectorBelow {M O : Type*} (indices : List M) (observations : List O)
    (x y : Vector M O) : Bool :=
  indices.all fun m => ComparisonExecutableTables.below observations (x m) (y m)

variable {D M O : Type*} (values : List D) (indices : List M) (observations : List O)
  (E : Operations D M O) (j : D → Vector M O)

def indexCheck : Bool := values.all fun x => indices.all fun m => indices.all fun n =>
  !E.indexLe m n || ComparisonExecutableTables.below observations (j x m) (j x n)

def latticeCheck : Bool := values.all fun x => values.all fun y =>
  vectorEq indices observations (j (E.join x y)) (fun m o => j x m o || j y m o) &&
  vectorEq indices observations (j (E.meet x y)) (fun m o => j x m o && j y m o)

def reflectCheck : Bool := values.all fun x => values.all fun y =>
  !vectorBelow indices observations (j x) (j y) || E.domainLe x y

def actionCheck : Bool := indices.all fun m => values.all fun x =>
  vectorEq indices observations (fun n => j x (E.mul m n)) (j (E.action m x))

def constructorCheck (op : D → D → D)
    (vectorOp : Vector M O → Vector M O → Vector M O) : Bool :=
  values.all fun x => values.all fun y =>
    vectorEq indices observations (vectorOp (j x) (j y)) (j (op x y))

def check : Bool :=
  indexCheck values indices observations E j && latticeCheck values indices observations E j &&
  reflectCheck values indices observations E j && actionCheck values indices observations E j &&
  constructorCheck values indices observations j E.prod E.vectorProd &&
  constructorCheck values indices observations j E.sum E.vectorSum &&
  constructorCheck values indices observations j E.fn E.vectorFn

end ModalityInference.ComparisonExecutableAgreement
