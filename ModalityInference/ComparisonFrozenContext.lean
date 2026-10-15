import ModalityInference.ComparisonExactContext
import ModalityInference.ComparisonBody

/-! Frozen contexts determine shared type and modality images after total
suffixes have been exposed. The remaining scalar comparisons and all original
source bounds are retained for the caller's complete certificate check. -/
namespace ModalityInference.ComparisonFrozenContext

abbrev Prepared := SchemePreparation.Prepared
abbrev Request := ComparisonExactContext.Request

/-- A source-dependent expression may acquire a partial image. Only fixed
total source labels can be peeled before the shared images are determined. -/
def sourceTotal (p : Prepared) (total : ModExpr → Bool) (m : ModExpr) : Bool :=
  total m && ComparisonExactContext.fixedMode p m

def requestsStep (p : Prepared) (total : ModExpr → Bool)
    (next : Ty → Ty → List Request) : Ty → Ty → List Request
  | .var (.flex n), target =>
      if ComparisonInstance.typeAllowed p (.flex n) && ComparisonExactContext.partialType total target
      then [(.var (.flex n), target)] else []
  | .modal a m, .modal b n =>
      if !sourceTotal p total m && !total n then [(.modal a m, .modal b n)] else []
  | .prod a b, .prod c d | .sum a b, .sum c d | .fn a b, .fn c d =>
      next a c ++ next b d
  | _, _ => []

def requests (p : Prepared) (total : ModExpr → Bool) : Nat → Ty → Ty → List Request
  | 0, _, _ => []
  | fuel + 1, source, target =>
      requestsStep p total (requests p total fuel)
        (ComparisonBody.peel (sourceTotal p total) source).base
        (ComparisonBody.peel total target).base

def collect (p : Prepared) (total : ModExpr → Bool) : List Request :=
  requests p total (ComparisonBody.traversalSize p.sourceType +
    ComparisonBody.traversalSize p.targetType + 1) p.sourceType p.targetType

def independent (p : Prepared) (total : ModExpr → Bool) : Substitution :=
  ComparisonContext.solvePriorityComponents (ComparisonExactContext.requestSupport p)
    (fun request => match request.1 with
      | .modal _ m => ComparisonContext.compoundMode p m
      | _ => false)
    (fun request action => ComparisonInstance.matchType p request.1 request.2 action)
    (collect p total) {}

def prepare (p : Prepared) (total : ModExpr → Bool) : Option Substitution := do
  if !ComparisonInstance.targetFresh p then none else do
    let action := independent p total
    if ComparisonExactContext.scopeCheck p action then some action else none

end ModalityInference.ComparisonFrozenContext
