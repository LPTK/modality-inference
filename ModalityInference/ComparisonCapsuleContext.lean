import ModalityInference.ComparisonCapsuleIntervals
import ModalityInference.ComparisonExactContext
import ModalityInference.SchemeModeSynthesis

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

def modeIds (p : Prepared) (bindings : List Binding) : List Nat :=
  List.range' p.firstMode (p.nextMode - p.firstMode) ++ bindings.map Binding.fresh

def goals (total : ModExpr → Bool) (bindings : List Binding) : Bounds :=
  bindings.flatMap (Binding.bounds total)

def materialize (p : Prepared) (bindings : List Binding) (modes : Substitution) : Substitution :=
  { types := bindings.map fun b =>
      (b.name, .modal b.base (modes.mode (.flex b.fresh)))
    modes := modes.modes.filter fun (n, _) => ComparisonInstance.modeAllowed p (.flex n) }

/-- Fresh suffix coordinates must have been eliminated from every image. -/
def bounded (p : Prepared) (action : Substitution) : Bool :=
  action.types.all (fun (n, t) => n < p.nextType &&
    t.typeVariables.all (fun v => v.index < p.nextType) &&
    t.modeVariables.all (fun v => v.index < p.nextMode)) &&
  action.modes.all (fun (n, m) => n < p.nextMode &&
    m.freeVariables.all (fun v => v.index < p.nextMode))

def prepare (fuel : Nat) (p : Prepared) (total : ModExpr → Bool) :
    RunResult (Option Substitution) := do
  let selected := bindings p total
  if selected.isEmpty then return none
  let modes ← SchemeModeSynthesis.run fuel (modeIds p selected)
    (.imp (boundsModeFormula p.assumptions) (boundsModeFormula (goals total selected)))
  let action := materialize p selected modes.substitution
  if ComparisonExactContext.scopeCheck p action && bounded p action then return some action
  else return none

end ModalityInference.ComparisonCapsuleContext
