import ModalityInference.Rewriting

/-! Recognition of the declared-bound fragment decided by joint comparison. -/
namespace ModalityInference

def residualBound : Constraint → Bool
  | .sub a b => match a.outer, b.outer with
    | (.var _, _), (.var _, _) => true
    | _, _ => false
  | .mode _ _ | .defined _ => true
  | _ => false

def residualBounds (bounds : Bounds) : Bool := bounds.all residualBound

end ModalityInference
