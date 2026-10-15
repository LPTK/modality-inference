import ModalityInference.ComparisonAnnotations
import ModalityInference.ComparisonContext
import ModalityInference.ComparisonExactContext
import ModalityInference.ComparisonModalSpine

/-! Compound source actions can determine shared literal modality images from
a complete target spine above the same fixed operand. The caller retains every
original body and bound obligation when checking the specialization. -/
namespace ModalityInference.ComparisonCompoundSpine

abbrev Prepared := SchemePreparation.Prepared
abbrev Request := ComparisonContext.Request

def requests (p : Prepared) : Ty → Ty → List Request
  | .prod a b, .prod c d | .sum a b, .sum c d | .fn a b, .fn c d =>
      requests p a c ++ requests p b d
  | .modal a m, target =>
      if ComparisonAnnotations.fixed p a && ComparisonContext.compoundMode p m then
        match ComparisonModalSpine.factor a target with
        | some ms => [(m, ComparisonPartialModes.recompose ms)]
        | none => []
      else match target with
        | .modal b _ => requests p a b
        | _ => []
  | _, _ => []

def independent (p : Prepared) : Substitution :=
  ComparisonContext.solvePriorityComponents (ComparisonContext.requestSupport p)
    (fun request => ComparisonContext.compoundMode p request.1)
    (fun request action => ComparisonInstance.matchMode p request.1 request.2 action)
    (requests p p.sourceType p.targetType) {}

def prepare (p : Prepared) : Option Substitution := do
  if !ComparisonInstance.targetFresh p then none else do
    let action := independent p
    if ComparisonExactContext.scopeCheck p action then some action else none

end ModalityInference.ComparisonCompoundSpine
