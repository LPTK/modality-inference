import ModalityInference.Declarative

/-! The scalar projection of guarded source bounds used to certify conditional
totality without changing the declared rigid type assumptions. -/

namespace ModalityInference.ComparisonGuardedTotal

def scalarBounds (bounds : Bounds) : Bounds :=
  bounds.assumptions.filter fun c => match c with
    | .mode _ _ | .defined _ => true
    | _ => false

end ModalityInference.ComparisonGuardedTotal
