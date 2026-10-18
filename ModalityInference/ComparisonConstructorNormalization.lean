import ModalityInference.ComparisonAlgebra

/-! Deterministic distribution of a binary constructor over two finite lattice
expressions. Entries already present in a child basis are retained as atoms;
the domain sign selects the contravariant function-domain operations. -/
namespace ModalityInference.ComparisonConstructorNormalization

open ComparisonAlgebra

def right (op : CompareTy → CompareTy → CompareTy) (basis : List CompareTy)
    (a b : CompareTy) : Option CompareTy :=
  if basis.contains b then some (op a b)
  else match b with
    | .join b d => do return .join (← right op basis a b) (← right op basis a d)
    | .meet b d => do return .meet (← right op basis a b) (← right op basis a d)
    | _ => none

def lift (op : CompareTy → CompareTy → CompareTy) (sign : Bool → Bool)
    (left rightBasis : List CompareTy) (a b : CompareTy) : Option CompareTy :=
  if left.contains a then right op rightBasis a b
  else match a with
    | .join a c => do
        return typeOp (sign true)
          (← lift op sign left rightBasis a b) (← lift op sign left rightBasis c b)
    | .meet a c => do
        return typeOp (sign false)
          (← lift op sign left rightBasis a b) (← lift op sign left rightBasis c b)
    | _ => none

end ModalityInference.ComparisonConstructorNormalization
