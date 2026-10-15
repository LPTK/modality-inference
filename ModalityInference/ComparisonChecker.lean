import ModalityInference.ComparisonElimination
import ModalityInference.ComparisonPreparation
import ModalityInference.SchemeModeSynthesis
import ModalityInference.ComparisonInstance

namespace ModalityInference.ComparisonChecker

structure Evidence where
  substitution : CompareSubstitution
  assumptions : Bounds
  obligations : CompareBounds
  body : CompareTy × CompareTy
  flexibleAtoms : List Nat
  query : BoolExpr
  backend : ConcreteBackend.Report
  deriving Repr

/-- The ordinary decomposition retains modalized bounds. The strengthened
variant uses only sufficient shared-wrapper steps to certify partial bodies. -/
def propagate (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (shared : Bool) : RunResult Evidence := do
  let known ← ComparisonBody.knownTotal fuel p.assumptions
    (ComparisonAnnotations.expressions p.sourceType ++
      ComparisonAnnotations.expressions p.targetType)
  let annotations := ComparisonAnnotations.prepare p (ComparisonBody.isTotal known)
  let work := { p with sourceType := annotations.substitution.ty p.sourceType }
  let bare := if shared then ComparisonBody.eligible work (ComparisonBody.isTotal known)
        else ComparisonPartial.eligible work
  let names := (List.range' p.firstType (p.nextType - p.firstType)).filter
    (fun n => !bare.contains n)
  let templates := ComparisonSkeleton.allocate work shapes names p.nextType annotations.nextMode
  let reduced ← ComparisonReduction.prepare fuel work templates bare known shared
  let reduced := { reduced with modes := annotations.bounds ++ reduced.modes }
  let types ← ComparisonElimination.run fuel work shapes templates reduced
  let adapted := annotations.images.map Prod.fst
  let modes ← SchemeModeSynthesis.run fuel
    ((List.range' p.firstMode (templates.nextMode - p.firstMode)).filter
      (fun n => !adapted.contains n)) types.query
  let report ← ConcreteBackend.decideFormula fuel modes.query
  if !report.valid then return ← .rejected "scheme comparison obligations are not valid"
  let leaves : CompareSubstitution := { types := types.types }
  let modeAction : Substitution :=
    { modes := annotations.images.map (fun (n, m) => (n, m.subst modes.substitution.mode)) ++
        modes.substitution.modes }
  let images : List (Nat × CompareTy) := reduced.partialTypes ++
    templates.substitution.types.map (fun (n, t) => (n, leaves.ty t))
  let action : CompareSubstitution :=
    { types := images.map fun (n, t) =>
        (n, t.subst CompareTy.var modeAction.mode)
      modes := modeAction.modes }
  return {
      substitution := ComparisonPreparation.reconstruct p action
      assumptions := p.assumptions
      obligations := action.bounds p.sourceBounds
      body := (action.ty p.sourceType, .ofTy p.targetType)
      flexibleAtoms := modes.flexibleAtoms
      query := modes.query
      backend := report }

def run (fuel : Nat) (source target : Scheme) : RunResult Evidence := do
  let p := SchemePreparation.prepare [] source target
  if let some result ← ComparisonInstance.attempt fuel p then
    let action := CompareSubstitution.ofSubstitution result.action
    return {
      substitution := ComparisonPreparation.reconstruct p action
      assumptions := p.assumptions
      obligations := action.bounds p.sourceBounds
      body := (action.ty p.sourceType, .ofTy p.targetType)
      flexibleAtoms := []
      query := result.query
      backend := result.backend }
  let shapes ← ComparisonShapeSolver.prepare fuel p
  match shapes with
  | .infeasibleAssumptions =>
      .rejected "declared shape equations are infeasible; outside residual-target comparison"
  | .solved shapes =>
    match propagate fuel p shapes false with
    | .rejected reason =>
        -- Shared-wrapper reduction is sufficient, not invertible. It is a
        -- positive fallback; an exhausted primary run never selects this path.
        match propagate fuel p shapes true with
        | .success result => .success result
        | .exhausted => .exhausted
        | .rejected _ => .rejected reason
    | result => result

end ModalityInference.ComparisonChecker
