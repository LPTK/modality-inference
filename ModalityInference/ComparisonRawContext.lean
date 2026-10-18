import ModalityInference.ComparisonAlgebra

/-! Conservative removal of literal reflexive type assumptions. Scalar facts
are retained verbatim; partial annotations acquire no additional guard. -/
namespace ModalityInference.ComparisonRawContext

def keep : Constraint → Bool
  | .sub a b | .equiv a b => decide (a ≠ b)
  | .equal v a => decide (a ≠ .var v)
  | _ => true

def prune (Δ : Bounds) : Bounds := Δ.filter keep

end ModalityInference.ComparisonRawContext
