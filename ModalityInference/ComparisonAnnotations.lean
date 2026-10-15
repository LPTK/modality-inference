import ModalityInference.ComparisonBody
import ModalityInference.ComparisonShapeSolver
import ModalityInference.ComparisonModalSpine

/-! Collect direct body-only modality requests at an identical fixed base.
Every original body obligation remains for checking after adaptation. -/
namespace ModalityInference.ComparisonAnnotations

def expressions : Ty → List ModExpr
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b => expressions a ++ expressions b
  | .modal a m => m :: expressions a

def hasPartial (total : ModExpr → Bool) (t : Ty) : Bool :=
  (expressions t).any (fun m => !total m)

def fixed (p : SchemePreparation.Prepared) (t : Ty) : Bool :=
  t.typeVariables.all (fun v => !ComparisonShapeSolver.sourceAllowed p v) &&
    t.modeVariables.all (fun v => match v with
      | .rigid _ => true
      | .flex n => !(p.firstMode ≤ n && n < p.nextMode))

def requests (p : SchemePreparation.Prepared) (total : ModExpr → Bool)
    (indices : List Nat) : Nat → Bool → Ty → Ty → List ComparisonPartialModes.Request
  | 0, _, _, _ => []
  | fuel + 1, reversed, source, target =>
    match source with
    | .modal a (.var (.flex n)) =>
      if indices.contains n && fixed p a then
        match ComparisonModalSpine.factor a target with
        | some spine => [⟨n, ComparisonPartialModes.recompose spine, reversed⟩]
        | none => []
      else []
    | _ =>
      match ComparisonBody.stripShared total source target with
      | some (a, b) => requests p total indices fuel reversed a b
      | none => match source, target with
        | .prod a b, .prod c d | .sum a b, .sum c d =>
          requests p total indices fuel reversed a c ++
            requests p total indices fuel reversed b d
        | .fn a b, .fn c d =>
          requests p total indices fuel (!reversed) a c ++
            requests p total indices fuel reversed b d
        | _, _ => []

def prepare (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    ComparisonPartialModes.Result :=
  let indices := ComparisonPartialModes.eligible p
  let pending := requests p total indices
    (ComparisonBody.traversalSize p.sourceType + ComparisonBody.traversalSize p.targetType + 1)
    false p.sourceType p.targetType
  let selected := indices.filter fun n => pending.any fun r =>
    r.name == n && !(ComparisonPartialModes.split total [r.target]).stem.isEmpty
  ComparisonPartialModes.adapt total selected pending p.nextMode

end ModalityInference.ComparisonAnnotations
