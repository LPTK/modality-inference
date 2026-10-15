import ModalityInference.ComparisonContext
import ModalityInference.ComparisonTypes
import ModalityInference.ComparisonAbsorption

/-! Exact partial-annotation contexts may determine their type bases and mode
images together. This positive prepass preserves every original obligation by
substitution; unrelated components remain for ordinary comparison. -/
namespace ModalityInference.ComparisonExactContext

abbrev Prepared := SchemePreparation.Prepared

abbrev Request := Ty × Ty

def partialType (total : ModExpr → Bool) : Ty → Bool
  | .var _ | .unit | .credit => false
  | .prod a b | .sum a b | .fn a b => partialType total a || partialType total b
  | .modal a m => !total m || partialType total a

def requests (p : Prepared) (total : ModExpr → Bool) : Ty → Ty → List Request
  | .var (.flex n), target =>
      if ComparisonInstance.typeAllowed p (.flex n) && partialType total target
      then [(.var (.flex n), target)] else []
  | .prod a b, .prod c d
  | .sum a b, .sum c d
  | .fn a b, .fn c d => requests p total a c ++ requests p total b d
  | .modal a m, .modal b n =>
      if total n then requests p total a b else [(.modal a m, .modal b n)]
  | _, _ => []

/-- Type and modality identifiers have separate namespaces. -/
def requestSupport (p : Prepared) (request : Request) : List Nat :=
  (request.1.typeVariables.filterMap fun v => match v with
    | .flex n => if ComparisonInstance.typeAllowed p v then some (2 * n) else none
    | .rigid _ => none) ++
  (request.1.modeVariables.filterMap fun v => match v with
    | .flex n => if ComparisonInstance.modeAllowed p v then some (2 * n + 1) else none
    | .rigid _ => none)

/-- Once a type image has been determined, an outer direct mode can expose
that entire image by the identity law. This handles a type used both bare and
inside modality contexts without moving a partial annotation through them. -/
def matchRequest (p : Prepared) (request : Request) (action : Substitution) :
    Option Substitution :=
  match request.1 with
  | .modal a (.var (.flex n)) =>
      if ComparisonInstance.modeAllowed p (.flex n) && action.ty a == request.2 then
        ComparisonInstance.bindMode n .epsilon action
      else ComparisonInstance.matchType p request.1 request.2 action
  | _ => ComparisonInstance.matchType p request.1 request.2 action

def independent (p : Prepared) (total : ModExpr → Bool) : Substitution :=
  ComparisonContext.solvePriorityComponents (requestSupport p) (fun request =>
    match request.1 with
    | .modal _ m => ComparisonContext.compoundMode p m
    | _ => true)
    (matchRequest p) (requests p total p.sourceType p.targetType) {}

/-- A sufficient identity specialization exposes modality capsules to partial
type-interval elimination, including nonuniform and bare uses of their type
parameters. Written bounds are rechecked after substitution. -/
def neutralOwners (p : Prepared) : ComparisonAbsorption.Owners :=
  (ComparisonAbsorption.capsules p.sourceType).filter fun (x, m) =>
    ComparisonInstance.typeAllowed p (.flex x) &&
      ComparisonInstance.modeAllowed p (.flex m)

def neutral (p : Prepared) : Substitution :=
  { modes := (ComparisonAbsorption.modes (neutralOwners p)).map fun m => (m, .epsilon) }

def fixedType (p : Prepared) (t : Ty) : Bool :=
  t.typeVariables.all (fun v => !ComparisonInstance.typeAllowed p v) &&
    t.modeVariables.all (fun v => !ComparisonInstance.modeAllowed p v)

def fixedMode (p : Prepared) (m : ModExpr) : Bool :=
  m.freeVariables.all (fun v => !ComparisonInstance.modeAllowed p v)

/-- The final certificate check also protects calls on arbitrary prepared
records. Images may be partial, but contain no fresh source identifier. -/
def scopeCheck (p : Prepared) (action : Substitution) : Bool :=
  action.types.all (fun (n, t) => ComparisonInstance.typeAllowed p (.flex n) &&
    fixedType p t) &&
  action.modes.all (fun (n, m) => ComparisonInstance.modeAllowed p (.flex n) &&
    fixedMode p m)

def prepare (p : Prepared) (total : ModExpr → Bool) : Option Substitution := do
  if !ComparisonInstance.targetFresh p then none else do
    let action := independent p total
    if scopeCheck p action then some action else none

/-- Bounds are rewritten in full, including every written definedness guard. -/
def rewrite (p : Prepared) (action : Substitution) : Prepared :=
  { p with sourceType := action.ty p.sourceType, sourceBounds := action.bounds p.sourceBounds }

/-- Apply the later internal substitution to every earlier image. Earlier keys
take priority; unaffected later images are retained verbatim. -/
def finish (before : Substitution) (after : CompareSubstitution) : CompareSubstitution :=
  { types := before.types.map (fun (n, t) => (n, after.ty t)) ++
      after.types.filter (fun pair => !(before.types.map Prod.fst).contains pair.1)
    modes := (({ modes := after.modes } : Substitution).compose before).modes }

end ModalityInference.ComparisonExactContext
