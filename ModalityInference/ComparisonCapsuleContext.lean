import ModalityInference.ComparisonCapsuleIntervals
import ModalityInference.ComparisonParameterization
import ModalityInference.ComparisonAnnotations
import ModalityInference.ComparisonInstance

/-! Shared partial type intervals retain one literal input base and synthesize
their total suffix together with the source modalities. The resulting candidate
is checked against the complete original body and bounds by the caller. -/
namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals

abbrev Prepared := SchemePreparation.Prepared

/-- Product and sum children inherit the enclosing action; function children
start a new context, reversing the domain's variance. Unmatched structure remains
an obligation of the original comparison. -/
def requests (p : Prepared) (total : ModExpr → Bool) :
    Nat → Bool → Ty → Ty → ModExpr → ModExpr → List Request
  | 0, _, _, _, _, _ => []
  | fuel + 1, lower, source, target, sourceMode, targetMode =>
    match source with
    | .var (.flex n) =>
        if ComparisonInstance.typeAllowed p (.flex n) then
          [⟨n, .modal target targetMode, sourceMode, lower⟩]
        else []
    | .modal a m =>
        if total m then requests p total fuel lower a target (.compose m sourceMode) targetMode
        else []
    | _ => match target with
      | .modal b n => requests p total fuel lower source b sourceMode (.compose n targetMode)
      | _ => match source, target with
        | .prod a b, .prod c d | .sum a b, .sum c d =>
            requests p total fuel lower a c sourceMode targetMode ++
              requests p total fuel lower b d sourceMode targetMode
        | .fn a b, .fn c d =>
            requests p total fuel (!lower) a c .epsilon .epsilon ++
              requests p total fuel lower b d .epsilon .epsilon
        | _, _ => []

def collect (p : Prepared) (total : ModExpr → Bool) : List Request :=
  requests p total (ComparisonBody.traversalSize p.sourceType +
    ComparisonBody.traversalSize p.targetType + 1) false p.sourceType p.targetType .epsilon .epsilon

def bindings (p : Prepared) (total : ModExpr → Bool) : List Binding :=
  let collected := collect p total
  let names := (collected.map Request.name).dedup
  names.zipIdx.filterMap fun (name, offset) =>
    plan total name (p.nextMode + offset) collected

/-- Mixed partial intervals use one shared symbolic suffix. Defined groups
remain in structural reduction, where declared subtype paths are retained. -/
def mixedBindings (p : Prepared) (total : ModExpr → Bool) : List Binding :=
  (bindings p total).filter fun b =>
    b.requests.any Request.isLower && b.requests.any (fun r => !r.isLower) &&
      b.requests.all (fun r => ComparisonAnnotations.hasPartial total r.endpoint)

/-- Variables below a modality without a totality certificate retain their
literal images while other intervals are parameterized. -/
def frozenTypeSupport (total : ModExpr → Bool) : Ty → Finset TypeVar
  | .var _ | .unit | .credit => ∅
  | .prod a b | .sum a b | .fn a b => frozenTypeSupport total a ∪ frozenTypeSupport total b
  | .modal a m => if total m then frozenTypeSupport total a else a.typeVars

/-- Select mixed intervals whose images can be changed without entering a
frozen source context. Literal context matching handles the remaining keys. -/
def unfrozenBindings (p : Prepared) (total : ModExpr → Bool) : List Binding :=
  (mixedBindings p total).filter fun b => decide (TypeVar.flex b.name ∉ frozenTypeSupport total p.sourceType)

def symbolic (bindings : List Binding) : Substitution :=
  { types := bindings.map fun b => (b.name, b.image) }

def modeIds (p : Prepared) (bindings : List Binding) : List Nat :=
  List.range' p.firstMode (p.nextMode - p.firstMode) ++ bindings.map Binding.fresh

def goals (total : ModExpr → Bool) (bindings : List Binding) : Bounds :=
  bindings.flatMap (Binding.bounds total)

end ModalityInference.ComparisonCapsuleContext
