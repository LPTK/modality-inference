import ModalityInference.ComparisonInstance
import ModalityInference.ComparisonTypes

/-! Exact partial-annotation matching inside structural body contexts. This
prepass chooses only fresh source modality images. It discharges no body or
bound obligation, and leaves unrelated components for ordinary comparison. -/
namespace ModalityInference.ComparisonContext

abbrev Prepared := SchemePreparation.Prepared

/-- Connected requests are solved together. A failed component leaves all of its
variables to the later symbolic phases; it cannot discard a solution for an
independent component. The support contains only fresh source identifiers. -/
def closeComponent (support : α → List Nat) :
    Nat → List α → List α → List α × List α
  | 0, group, pending => (group, pending)
  | fuel + 1, group, pending =>
      let touches := fun request => (support request).any fun name =>
        group.any fun member => (support member).contains name
      let adjacent := pending.filter touches
      if adjacent.isEmpty then (group, pending)
      else closeComponent support fuel (group ++ adjacent) (pending.filter fun r => !touches r)

def componentsFuel (support : α → List Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, request :: requests =>
      let (group, pending) := closeComponent support requests.length [request] requests
      group :: componentsFuel support fuel pending

def components (support : α → List Nat) (requests : List α) : List (List α) :=
  componentsFuel support requests.length requests

/-- Compound partial contexts constrain a simultaneous image before direct
occurrences contribute optional exact matches. Direct occurrences can instead
be related by total suffix inequalities, so their failure must not discard a
successful compound-context match. -/
def solvePriorityComponents (support : α → List Nat) (compound : α → Bool)
    (matchRequest : α → β → Option β) (requests : List α) (initial : β) : β :=
  (components support requests).foldl (fun action group =>
    match (group.filter compound).foldlM
        (fun action request => matchRequest request action) action with
    | none => action
    | some selected =>
        ((group.filter fun request => !compound request).foldlM
          (fun action request => matchRequest request action) selected).getD selected) initial

abbrev Request := ModExpr × ModExpr

def requests (total : ModExpr → Bool) : Ty → Ty → List Request
  | .prod a b, .prod c d
  | .sum a b, .sum c d
  | .fn a b, .fn c d => requests total a c ++ requests total b d
  | .modal a m, .modal b n =>
      requests total a b ++ if total n then [] else [(m, n)]
  | _, _ => []

def requestSupport (p : Prepared) (request : Request) : List Nat :=
  request.1.freeVariables.filterMap fun v =>
    match v with
    | .flex n => if ComparisonInstance.modeAllowed p v then some n else none
    | .rigid _ => none

def compoundMode (p : Prepared) : ModExpr → Bool
  | .var (.flex n) => !ComparisonInstance.modeAllowed p (.flex n)
  | _ => true

def independent (p : Prepared) (total : ModExpr → Bool) : Substitution :=
  solvePriorityComponents (requestSupport p) (fun request => compoundMode p request.1)
    (fun (source, target) action => ComparisonInstance.matchMode p source target action)
    (requests total p.sourceType p.targetType) {}

def scopeCheck (p : Prepared) (action : Substitution) : Bool :=
  action.types.isEmpty && action.modes.all fun (name, image) =>
    ComparisonInstance.modeAllowed p (.flex name) &&
      image.freeVariables.all fun v => !ComparisonInstance.modeAllowed p v

/-- The target has no fresh source identifiers, so every selected image is
independent of all source binders. This is a positive fallback prepass. -/
def prepare (p : Prepared) (total : ModExpr → Bool) : Option Substitution :=
  if ComparisonInstance.targetFresh p then
    let action := independent p total
    if scopeCheck p action then some action else none
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
