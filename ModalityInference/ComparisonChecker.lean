import ModalityInference.ComparisonElimination
import ModalityInference.ComparisonPreparation
import ModalityInference.SchemeModeSynthesis
import ModalityInference.ComparisonInstance
import ModalityInference.ComparisonAbsorption
import ModalityInference.ComparisonContext
import ModalityInference.ComparisonExactContext

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
    (shapes : ComparisonShapeSolver.Solved) (shared : Bool)
    (before : Substitution := {}) : RunResult Evidence := do
  let input := ComparisonExactContext.rewrite p before
  let known ← ComparisonBody.knownTotal fuel input.assumptions
    (ComparisonAnnotations.expressions input.sourceType ++
      ComparisonAnnotations.expressions input.targetType)
  let absorption := ComparisonAbsorption.plan input (ComparisonBody.isTotal known)
  let absorbed := { input with sourceType := absorption.body }
  let annotations := ComparisonAnnotations.prepare absorbed (ComparisonBody.isTotal known)
  let work := { absorbed with sourceType := annotations.substitution.ty absorbed.sourceType }
  let selected := before.types.map Prod.fst
  let bare := (if shared then ComparisonBody.eligible work (ComparisonBody.isTotal known)
        else ComparisonPartial.eligible work).filter (fun n => !selected.contains n)
  let names := (List.range' p.firstType (p.nextType - p.firstType)).filter
    (fun n => !selected.contains n && !bare.contains n)
  let templates := ComparisonSkeleton.allocate work shapes names p.nextType annotations.nextMode
  let reduced ← ComparisonReduction.prepare fuel work templates bare known shared
  let reduced := { reduced with modes := annotations.bounds ++ reduced.modes }
  let types ← ComparisonElimination.run fuel work shapes templates reduced
  let adapted := before.modes.map Prod.fst ++ absorption.modes ++ annotations.images.map Prod.fst
  let modes ← SchemeModeSynthesis.run fuel
    ((List.range' p.firstMode (templates.nextMode - p.firstMode)).filter
      (fun n => !adapted.contains n)) types.query
  let report ← ConcreteBackend.decideFormula fuel modes.query
  if !report.valid then return ← .rejected "scheme comparison obligations are not valid"
  let leaves : CompareSubstitution := { types := types.types }
  let modeAction : Substitution :=
    { modes := absorption.action.modes ++
        annotations.images.map (fun (n, m) => (n, m.subst modes.substitution.mode)) ++
        modes.substitution.modes }
  let images : List (Nat × CompareTy) := reduced.partialTypes ++
    templates.substitution.types.map (fun (n, t) => (n, leaves.ty t))
  let action : CompareSubstitution :=
    { types := images.map fun (n, t) =>
        (n, t.subst CompareTy.var modeAction.mode)
      modes := modeAction.modes }
  let action := ComparisonExactContext.finish before action
  return {
      substitution := ComparisonPreparation.reconstruct p action
      assumptions := p.assumptions
      obligations := action.bounds p.sourceBounds
      body := (action.ty p.sourceType, .ofTy p.targetType)
      flexibleAtoms := modes.flexibleAtoms
      query := modes.query
      backend := report }

/-- Sufficient shared-wrapper reduction is attempted only after a definitive
ordinary rejection. It never replaces a successful or exhausted result. -/
def variants (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (before : Substitution := {}) : RunResult Evidence :=
  match propagate fuel p shapes false before with
  | .rejected reason =>
      match propagate fuel p shapes true before with
      | .success result => .success result
      | .exhausted => .exhausted
      | .rejected _ => .rejected reason
  | result => result

/-- Refine exact partial contexts on the current specialization, then compose
with the earlier action. Every branch rechecks the original prepared input. -/
def refineContexts (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (before : Substitution := {}) : RunResult Evidence :=
  match variants fuel p shapes before with
  | .rejected reason => do
      let input := ComparisonExactContext.rewrite p before
      let known ← ComparisonBody.knownTotal fuel input.assumptions
        (ComparisonAnnotations.expressions input.sourceType ++
          ComparisonAnnotations.expressions input.targetType)
      let absorption := ComparisonAbsorption.plan input (ComparisonBody.isTotal known)
      let context := { input with sourceType := absorption.body }
      let modes : RunResult Evidence :=
        match ComparisonContext.prepare context (ComparisonBody.isTotal known) with
        | some selected =>
            if selected.modes.isEmpty then .rejected reason
            else variants fuel p shapes (selected.compose before)
        | none => .rejected reason
      match modes with
      | .rejected _ =>
          match ComparisonExactContext.prepare context (ComparisonBody.isTotal known) with
          | some selected =>
              if selected.types.isEmpty && selected.modes.isEmpty then .rejected reason
              else variants fuel p shapes (selected.compose before)
          | none => .rejected reason
      | result => result
  | result => result

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
    match refineContexts fuel p shapes with
    | .rejected reason =>
        let before := ComparisonExactContext.neutral p
        if before.modes.isEmpty then .rejected reason
        else refineContexts fuel p shapes before
    | result => result

end ModalityInference.ComparisonChecker
