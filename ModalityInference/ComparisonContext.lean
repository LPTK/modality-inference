import ModalityInference.ComparisonInstance
import ModalityInference.ComparisonTypes

/-! Exact partial-annotation matching inside structural body contexts. This
prepass chooses only fresh source modality images. It discharges no body or
bound obligation, and leaves unrelated components for ordinary comparison. -/
namespace ModalityInference.ComparisonContext

abbrev Prepared := SchemePreparation.Prepared

/-- All matched occurrences share one substitution. Fixed identifiers and
repeated source occurrences use the exact checks of `matchMode`. -/
def collect (p : Prepared) (total : ModExpr → Bool) :
    Ty → Ty → Substitution → Option Substitution
  | .prod a b, .prod c d, action
  | .sum a b, .sum c d, action
  | .fn a b, .fn c d, action => do
      let action ← collect p total a c action
      collect p total b d action
  | .modal a m, .modal b n, action => do
      let action ← collect p total a b action
      if total n then some action else ComparisonInstance.matchMode p m n action
  | _, _, action => some action

/-- The target has no fresh source identifiers, so every selected image is
independent of all source binders. This is a positive fallback prepass. -/
def prepare (p : Prepared) (total : ModExpr → Bool) : Option Substitution :=
  if ComparisonInstance.targetFresh p then collect p total p.sourceType p.targetType {}
  else none

/-- Source bounds are transformed together with the body, retaining every
written guard. Declared assumptions and all binder ranges remain unchanged. -/
def rewrite (p : Prepared) (action : Substitution) : Prepared :=
  { p with sourceType := action.ty p.sourceType, sourceBounds := action.bounds p.sourceBounds }

/-- Compose the context's modality images with the subsequent comparison
substitution. Existing type images are already images of the rewritten input. -/
def finish (before : Substitution) (after : CompareSubstitution) : CompareSubstitution :=
  { types := after.types
    modes := (({ modes := after.modes } : Substitution).compose before).modes }

end ModalityInference.ComparisonContext
