import ModalityInference.ComparisonExecutableTables

/-! Symbolic checks and extensions of selected constructor rows. Each potential
row has a presence formula; no choice of rows or Boolean assignment is enumerated. -/
namespace ModalityInference.ComparisonExecutableTableFormula

open ComparisonExecutableTables

def below {O : Type*} (observations : List O) (x y : O → BoolExpr) : BoolExpr :=
  .all (observations.map fun o => .imp (x o) (y o))

def direction {O : Type*} (observations : List O) (reverse : Bool)
    (x y : O → BoolExpr) : BoolExpr :=
  if reverse then below observations y x else below observations x y

def compatible {M A O : Type*} (observations : List O) (embed : A → O → BoolExpr)
    (le : M → M → Bool) (p q : Bool) (a b : Row M A) : BoolExpr :=
  .imp (.and (.and (.const (le a.index b.index))
    (direction observations p (embed a.left) (embed b.left)))
    (direction observations q (embed a.right) (embed b.right)))
    (below observations (embed a.result) (embed b.result))

def selected {M A : Type*} (rows : List (Row M A))
    (present : Row M A → BoolExpr) (world : Nat → Bool) : List (Row M A) :=
  rows.filter fun r => (present r).eval world

def check {M A O : Type*} (observations : List O) (embed : A → O → BoolExpr)
    (le : M → M → Bool) (p q : Bool) (rows : List (Row M A))
    (present : Row M A → BoolExpr) : BoolExpr :=
  .all (rows.map fun a => .imp (present a) (.all (rows.map fun b =>
    .imp (present b) (compatible observations embed le p q a b))))

def extend {M A O : Type*} (observations : List O) (embed : A → O → BoolExpr)
    (le : M → M → Bool) (p q : Bool) (rows : List (Row M A))
    (present : Row M A → BoolExpr) (m : M) (x y : O → BoolExpr) : O → BoolExpr :=
  fun o => .any (rows.map fun r => .and (present r)
    (.and (.and (.and (.const (le r.index m)) (direction observations p (embed r.left) x))
      (direction observations q (embed r.right) y)) (embed r.result o)))

end ModalityInference.ComparisonExecutableTableFormula
